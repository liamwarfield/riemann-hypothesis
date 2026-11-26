module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
public import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDuality
public import Development.WeilBound.ThetaLifts.SphericalSplitting.SphSplitGeo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLines
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWittModelUnitaryAction

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RadFinAdjoinStable
noncomputable def UpperTheory.Reformulated.B.Qj9.Stable :
    {M : Type} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → Set (Module.End ℂ M) → Submodule ℂ M → Prop :=
    fun {M : Type} [AddCommGroup M] [_root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) ↦
      ∀ g ∈ Op, ∀ x ∈ P, (g : M → M) x ∈ P

theorem UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable :
    ∀ {M : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M),
      UpperTheory.Reformulated.B.Qj9.Stable Op P → ∀ e ∈ Algebra.adjoin ℂ Op, ∀ x ∈ P, (e : M → M) x ∈ P := by
  intro M _ _ Op P h e he
  induction he using Algebra.adjoin_induction with
  | mem g hg => exact h g hg
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact P.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.add_apply]
    exact P.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [Module.End.mul_apply]
    exact ha _ (hb x hx)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Lit.HoweDuality

section One

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def Stable (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) : Prop := ∀ g ∈ Op, ∀ x ∈ P, g x ∈ P

def Gen (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (s : M) : Prop :=
  ∀ P : Submodule ℂ M, Rel ≤ P → Stable Op P → s ∈ P → P = ⊤

def Rad (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) : Prop :=
  ∃ s, Gen Op Rel s ∧ ∀ k ∈ K, ∃ e ∈ Algebra.adjoin ℂ Op, e s = s ∧ e k ∈ Rel

def RadFin (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) : Prop :=
  ∃ s, Gen Op Rel s ∧ ∀ S : Finset M, (∀ k ∈ S, k ∈ K) → ∃ e ∈ Algebra.adjoin ℂ Op, e s = s ∧ ∀ k ∈ S, e k ∈ Rel

end One

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
  {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def intersection_update_fsHerm_neg_one (i : ι) (r : M₀ × ∀ j, M j) : M i →ₗ[ℂ] M₀ ⊗[ℂ] (⨂[ℂ] j, M j) :=
  TensorProduct.mk ℂ M₀ _ r.1 ∘ₗ (PiTensorProduct.tprod ℂ (s := M)).toLinearMap r.2 i

omit [Fintype ι] in
theorem position_apply (i : ι) (r : M₀ × ∀ j, M j) (x : M i) :
    intersection_update_fsHerm_neg_one i r x = r.1 ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update r.2 i x) := rfl

def factorOp (i : ι) (g : Module.End ℂ (M i)) : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) :=
  TensorProduct.map LinearMap.id
    (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g))


variable (M₀) in
def part (i : ι) (K : Submodule ℂ (M i)) : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) :=
  ⨆ r : M₀ × ∀ j, M j, K.map (intersection_update_fsHerm_neg_one i r)

end Tensor

end UpperTheory.Lit.HoweDuality

end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.PartStable
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.partStable :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
      {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
      (i : ι) (K : Submodule ℂ (M i)),
      (∀ g : Module.End ℂ M₀, ∀ t ∈ part (M₀ := M₀) i K,
        TensorProduct.map g LinearMap.id t ∈ part (M₀ := M₀) i K) ∧
      (∀ g : Module.End ℂ (M i), (∀ x ∈ K, g x ∈ K) → ∀ t ∈ part (M₀ := M₀) i K,
        factorOp i g t ∈ part (M₀ := M₀) i K) ∧
      ∀ l, l ≠ i → ∀ g : Module.End ℂ (M l), ∀ t ∈ part (M₀ := M₀) i K,
        factorOp l g t ∈ part (M₀ := M₀) i K := by
  intro ι _ _ M₀ _ _ M _ _ i K
  have mem : ∀ (r : M₀ × ∀ j, M j), ∀ x ∈ K,
      intersection_update_fsHerm_neg_one i r x ∈ part (M₀ := M₀) i K := fun r x hx =>
    (le_iSup (fun r : M₀ × ∀ j, M j => K.map (intersection_update_fsHerm_neg_one i r)) r) (Submodule.mem_map_of_mem hx)
  have key : ∀ Φ : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)),
      (∀ (r : M₀ × ∀ j, M j), ∀ x ∈ K,
        Φ (intersection_update_fsHerm_neg_one i r x) ∈ part (M₀ := M₀) i K) →
      ∀ t ∈ part (M₀ := M₀) i K, Φ t ∈ part (M₀ := M₀) i K := by
    intro Φ h t ht
    have : part (M₀ := M₀) i K ≤ (part (M₀ := M₀) i K).comap Φ :=
      iSup_le fun r => Submodule.map_le_iff_le_comap.2 fun x hx => h r x hx
    exact this ht
  refine ⟨fun g => key _ fun r x hx => ?_, fun g hg => key _ fun r x hx => ?_,
    fun l hl g => key _ fun r x hx => ?_⟩
  · have := mem (g r.1, r.2) x hx
    simpa [position_apply] using this
  · have := mem r (g x) (hg x hx)
    rw [position_apply] at this
    rw [position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    convert this using 3
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  · have := mem (r.1, Function.update r.2 l (g (r.2 l))) x hx
    rw [position_apply] at this
    rw [position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    convert this using 3
    funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update_of_ne hl.symm]
    · by_cases hj' : j = l
      · subst hj'; simp [Function.update_of_ne hj]
      · simp [Function.update_of_ne hj, Function.update_of_ne hj']
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerVp
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.kerVp :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}, IsMatched Bs G Xc om om' R Rf → ∀ v : Pl (F := F), relFin om' v ≤ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ∧ Stable (opFin om' v) (LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype)) ∧ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ≠ ⊤ ∧ ∀ N : Submodule ℂ ↥(SB (Fin a' × Fin (a + a') → Fv F v)), LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) ≤ N → Stable (opFin om' v) N → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v
  have hz : ∀ (h : UA σ G.W.J), Acts (evFin F v) (om (1, h))
      (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) 0 := by
    intro h r _
    have h0 : tens (evFin F v) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x
      simp [tens]
    rw [h0, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact hM.fin.inv' v hx
  · rintro g ⟨h, hh, hg⟩ x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx ⊢
    have e := hM.fin.equiv v h hh 0 (Submodule.zero_mem _) x x.2 0 (Submodule.zero_mem _)
      (g x) (g x).2 (hz h) (hg x) (by rw [map_zero]; exact hx.symm)
    rw [map_zero] at e
    exact e.symm
  · intro hK
    haveI := hM.fin.nontriv v
    obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
    have hmem : y ∈ Submodule.map (Rf.p' v) (SB (Fin a' × Fin (a + a') → Fv F v)) := by
      rw [hM.fin.onto' v]
      exact Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := hmem
    have hk : (⟨φ, hφ⟩ : SB (Fin a' × Fin (a + a') → Fv F v)) ∈
        LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype) := by
      rw [hK]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hk
    exact hy hk
  · intro N hKN hN hNtop
    have hst : ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
            Acts (evFin F v) (om (1, h)) φ φ₁ →
              Rf.p v φ ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) →
              Rf.p v φ₁ ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) := by
      intro h hh φ hφ φ₁ hφ₁ hact hp
      obtain ⟨y, ⟨n, hn, rfl⟩, hpn⟩ := hp
      have hgn := hN _ (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp_mem hM.triple v hh) n hn
      have e := hM.fin.equiv v h hh φ hφ n n.2 φ₁ hφ₁ _ (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp hM.triple v hh n).2
        hact (GlobalTheory.HoweGlobalPair.FinPlaceSmall.locOp_acts hM.triple v hh n) hpn.symm
      exact ⟨_, ⟨_, hgn, rfl⟩, e.symm⟩
    rcases hM.fin.irred v _ hst with hbot | htop
    · intro x hx
      have hm : Rf.p' v x ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) :=
        ⟨x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hbot, Submodule.mem_bot] at hm
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      exact hm
    · exfalso
      apply hNtop
      rw [eq_top_iff]
      intro x _
      have hm : Rf.p' v x ∈ Submodule.map (Rf.p' v) (Submodule.map (SB (Fin a' × Fin (a + a') → Fv F v)).subtype N) := by
        rw [htop]
        exact Submodule.mem_top
      obtain ⟨y, ⟨n, hn, rfl⟩, hpn⟩ := hm
      have hk : x - n ∈ N := by
        apply hKN
        rw [LinearMap.mem_ker, LinearMap.comp_apply, map_sub, map_sub, sub_eq_zero]
        exact hpn.symm
      have := N.add_mem hk hn
      rwa [sub_add_cancel] at this
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadIrr
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.radIrr :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl (F := F)} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → PositivityTheory.Sph.IrrAt om v → ∀ K : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ K → Stable (opFin om v) K → K ≠ ⊤ → Rad (opFin om v) (relFin om v) K := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hI K hrel hst hne
  have one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat 1 - 1)
    have h1 : mat (1 : UA σ X.J) = 1 := Matrix.ext fun i => congrFun rfl
    rw [h1, sub_self]
    intro _ _
    simp
  have aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have key : ∀ P : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ P →
      Stable (opFin om v) P → P = relFin om v ∨ P = ⊤ := by
    intro P hP hPs
    have hT : GlobalTheory.Published.ThetaSub om v (P.map (SB (Fin n × Fin d → Fv F v)).subtype) := by
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        have hzS := aug_le hz
        refine ⟨⟨z, hzS⟩, hP ?_, rfl⟩
        simpa [relFin] using hz
      · rintro _ ⟨k, -, rfl⟩
        exact k.2
      · rintro h hh _ ⟨k, hk, rfl⟩ φ₁ hφ₁ hA
        have hφ₁eq : φ₁ = ω (1, h) k := (hL.acts 1 one_mem h hh k k.2 φ₁).mp hA
        let g : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
          { toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩
            map_add' := fun x y => by ext1; simp
            map_smul' := fun c x => by ext1; simp }
        have hg : g ∈ opFin om v := by
          refine ⟨h, hh, fun φ => ?_⟩
          exact (hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl
        refine ⟨g k, hPs g hg k hk, ?_⟩
        simp [g, hφ₁eq]
    rcases hI _ hT with h1 | h1
    · left
      ext x
      constructor
      · intro hx
        have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := by
          rw [← h1]
          exact ⟨x, hx, rfl⟩
        simpa [relFin] using hx'
      · intro hx
        exact hP hx
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ P.map (SB (Fin n × Fin d → Fv F v)).subtype := by
        rw [h1]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
  have hK : K = relFin om v := by
    rcases key K hrel hst with h | h
    · exact h
    · exact absurd h hne
  obtain ⟨s, hs⟩ : ∃ s, s ∉ relFin om v := by
    by_contra hc
    push_neg at hc
    apply hne
    rw [hK, eq_top_iff]
    intro x _
    exact hc x
  refine ⟨s, ?_, ?_⟩
  · intro P hP hPs hsP
    rcases key P hP hPs with h | h
    · rw [h] at hsP
      exact absurd hsP hs
    · exact h
  · intro k hk
    refine ⟨1, Subalgebra.one_mem _, rfl, ?_⟩
    rw [hK] at hk
    simpa using hk
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadSph
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.radSph :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl (F := F)} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → PositivityTheory.Sph.SphAt M ψ om v → ∀ K : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ K → Stable (opFin om v) K → K ≠ ⊤ → Rad (opFin om v) (relFin om v) K := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hS K hrel hst hne
  have one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat 1 - 1)
    have h1 : mat (1 : UA σ X.J) = 1 := Matrix.ext fun i => congrFun rfl
    rw [h1, sub_self]
    intro _ _
    simp
  have aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have hG : ∀ h ∈ UAt σ W (evFin F v), ∃ g ∈ opFin om v,
      ∀ x : ↥(SB (Fin n × Fin d → Fv F v)), (g x : (Fin n × Fin d → Fv F v) → ℂ) = ω (1, h) x := by
    intro h hh
    refine ⟨{ toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩
              map_add' := fun x y => by ext1; simp
              map_smul' := fun c x => by ext1; simp }, ⟨h, hh, fun φ => ?_⟩, fun x => rfl⟩
    exact (hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl
  choose g hgOp hgapp using hG
  obtain ⟨s, hs⟩ := hS ω ρ hL
  let s' : ↥(SB (Fin n × Fin d → Fv F v)) := ⟨s, hs.mem⟩
  have hgen : Gen (opFin om v) (relFin om v) s' := by
    intro P hP hPs hsP
    have hle : augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) s} ≤
        P.map (SB (Fin n × Fin d → Fv F v)).subtype := by
      refine sup_le ?_ ?_
      · intro z hz
        exact ⟨⟨z, aug_le hz⟩, hP hz, rfl⟩
      · refine Submodule.span_le.mpr ?_
        rintro z ⟨h, hh, rfl⟩
        exact ⟨g h hh s', hPs _ (hgOp h hh) _ hsP, hgapp h hh s'⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := hle (hs.gen x x.2)
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  refine ⟨s', hgen, ?_⟩
  intro k hk
  obtain ⟨m, kk, w, c, hkw, hsum⟩ := hs.line k k.2
  let e : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
    ((m + 1 : ℂ))⁻¹ • ∑ i, w i • g (kk i) (hkw i).1
  have he_app : ∀ x : ↥(SB (Fin n × Fin d → Fv F v)),
      (e x : (Fin n × Fin d → Fv F v) → ℂ) = ((m + 1 : ℂ))⁻¹ • ∑ i, w i • ω (1, kk i) x := by
    intro x
    simp [e, hgapp]
  have hm : (m + 1 : ℂ) ≠ 0 := by
    norm_cast
  have hes : e s' = s' := by
    ext1
    rw [he_app]
    have hsum' : ∑ i : Fin (m + 1), w i • ω (1, kk i) s = ∑ _i : Fin (m + 1), s :=
      Finset.sum_congr rfl (fun i _ => (hkw i).2)
    show ((m + 1 : ℂ))⁻¹ • ∑ i, w i • ω (1, kk i) s = s
    rw [hsum', Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    push_cast
    rw [inv_mul_cancel₀ hm, one_smul]
  have heK : e k ∈ K := by
    show (((m + 1 : ℂ))⁻¹ • ∑ i, w i • g (kk i) (hkw i).1) k ∈ K
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    refine K.smul_mem _ (K.sum_mem fun i _ => ?_)
    rw [LinearMap.smul_apply]
    exact K.smul_mem _ (hst _ (hgOp _ _) k hk)
  have hrelv : e k - (((m + 1 : ℂ))⁻¹ * c) • s' ∈ relFin om v := by
    show ((e k - (((m + 1 : ℂ))⁻¹ * c) • s' : ↥(SB (Fin n × Fin d → Fv F v))) :
      (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v
    rw [Submodule.coe_sub, Submodule.coe_smul, he_app]
    have hh := (augAt om v).smul_mem ((m + 1 : ℂ))⁻¹ hsum
    rw [smul_sub, smul_smul] at hh
    exact hh
  by_cases hc : ((m + 1 : ℂ))⁻¹ * c = 0
  · refine ⟨e, ?_, hes, ?_⟩
    · exact Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun i _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (hgOp _ _)) _) _
    · rw [hc, zero_smul, sub_zero] at hrelv
      exact hrelv
  · exfalso
    apply hne
    apply hgen K hrel hst
    have h1 : (((m + 1 : ℂ))⁻¹ * c) • s' ∈ K := by
      have h2 := K.sub_mem heK (hrel hrelv)
      rwa [sub_sub_cancel] at h2
    have h3 := K.smul_mem (((m + 1 : ℂ))⁻¹ * c)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h3
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerV
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

theorem UpperTheory.Lit.HoweDuality.kerV :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ} {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}, IsMatched Bs G Xc om om' R Rf → ∀ v : Pl (F := F), relFin om v ≤ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ∧ Stable (opFin om v) (LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype)) ∧ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ≠ ⊤ ∧ ∀ N : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)), LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) ≤ N → Stable (opFin om v) N → N ≠ ⊤ → N ≤ LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v
  have hT := hM.triple
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hM.fin.inv v hx
  · rintro g ⟨h, hh, hg⟩ x hx
    have hx' : Rf.p v (x : (Fin a × Fin (a + a') → Fv F v) → ℂ) = 0 := hx
    have h0 : Acts (evFin F v) (om' (1, h)) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) 0 := by
      intro r _
      have ht : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
        funext y; simp [tens]
      rw [ht, map_zero]
    have e := hM.fin.equiv v h hh x x.2 0 (zero_mem _) (g x) (g x).2 0 (zero_mem _) (hg x) h0
      (by rw [hx', map_zero])
    show Rf.p v ((g x : SB _) : (Fin a × Fin (a + a') → Fv F v) → ℂ) = 0
    rw [e, map_zero]
  · intro hKe
    have hbot : (SB (Fin a × Fin (a + a') → Fv F v)).map (Rf.p v) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨ψ, hψ, rfl⟩
      have hm : (⟨ψ, hψ⟩ : SB (Fin a × Fin (a + a') → Fv F v)) ∈
          LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype) := by
        rw [hKe]; exact Submodule.mem_top
      exact hm
    rw [hM.fin.onto v] at hbot
    haveI := hM.fin.nontriv v
    exact top_ne_bot hbot
  · intro N hKN hst hne
    have key : ∀ x : SB (Fin a × Fin (a + a') → Fv F v),
        Rf.p v x ∈ (N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v) → x ∈ N := by
      rintro x ⟨_, ⟨n, hn, rfl⟩, hpn⟩
      have hk : x - n ∈ N := hKN (by
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
        exact hpn.symm)
      have := N.add_mem hn hk
      rwa [add_sub_cancel] at this
    rcases hM.fin.irred v ((N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v)) (by
      intro h hh ψ hψ ψ₁ hψ₁ hact hpm
      have hx : (⟨ψ, hψ⟩ : SB (Fin a × Fin (a + a') → Fv F v)) ∈ N := key ⟨ψ, hψ⟩ hpm
      have e := GlobalTheory.ThK.LocalOps.acts_unique v _ hψ hact (GlobalTheory.HoweGlobal.FinPlace.locOp_acts hT v hh ⟨ψ, hψ⟩)
      exact Submodule.mem_map_of_mem ⟨GlobalTheory.HoweGlobal.FinPlace.locOp hT v hh ⟨ψ, hψ⟩,
        hst _ (GlobalTheory.HoweGlobal.FinPlace.locOp_mem hT v hh) _ hx, e.symm⟩) with h0 | htop
    · intro x hx
      have hmem : Rf.p v x ∈ (N.map (SB (Fin a × Fin (a + a') → Fv F v)).subtype).map (Rf.p v) :=
        Submodule.mem_map_of_mem ⟨x, hx, rfl⟩
      rw [h0] at hmem
      exact (Submodule.mem_bot ℂ).1 hmem
    · exfalso
      apply hne
      rw [Submodule.eq_top_iff']
      intro x
      apply key
      rw [htop]; exact Submodule.mem_top
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Imports
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.NakAll
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadFin
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

private theorem UpperTheory.Lit.HoweDuality.radFin_adjoin_stable {M : Type} [AddCommGroup M] [Module ℂ M]
    (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) (hP : Stable Op P)
    (e : Module.End ℂ M) (he : e ∈ Algebra.adjoin ℂ Op) : ∀ x ∈ P, e x ∈ P :=
  _root_.UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable Op P hP e he

theorem UpperTheory.Lit.HoweDuality.radFin :
    ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M), Stable Op Rel → Stable Op K → Rad Op Rel K → RadFin Op Rel K := by
  intro M _ _ Op Rel K hRel hK hRad
  classical
  obtain ⟨s, hs, h⟩ := hRad
  refine ⟨s, hs, fun S => ?_⟩
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨1, one_mem _, rfl, by simp⟩
  | insert k S _ ih =>
    intro hS
    obtain ⟨e', he', hs', hk'⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    have hkK : e' k ∈ K :=
      radFin_adjoin_stable Op K hK e' he' k (hS k (Finset.mem_insert_self _ _))
    obtain ⟨e'', he'', hs'', hk''⟩ := h _ hkK
    refine ⟨e'' * e', mul_mem he'' he', by simp [hs', hs''], fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · simpa using hk''
    · simpa using radFin_adjoin_stable Op Rel hRel e'' he'' _ (hk' x hx)
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.SlotBasic
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.slotFacts :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι), (⨆ r : M₀ × (∀ j, M j), LinearMap.range (intersection_update_fsHerm_neg_one i r)) = ⊤ ∧ ∀ (g : Module.End ℂ (M i)) (r : M₀ × (∀ j, M j)) (x : M i), factorOp i g (intersection_update_fsHerm_neg_one i r x) = intersection_update_fsHerm_neg_one i r (g x) := by
  intro ι _ _ M₀ _ _ M _ _ i
  refine ⟨?_, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul x₀ w =>
      induction w using PiTensorProduct.induction_on with
      | smul_tprod c y =>
        rw [TensorProduct.tmul_smul]
        refine Submodule.smul_mem _ c ?_
        refine Submodule.mem_iSup_of_mem (x₀, y) ⟨y i, ?_⟩
        rw [position_apply]
        simp only [Function.update_eq_self]
      | add a b ha hb =>
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
  · intro g r x
    rw [position_apply, position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Nak
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.nak :
    ∀ {M T R : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup T] [Module ℂ T] (j : R → M →ₗ[ℂ] T) (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (N : Submodule ℂ T), (⨆ r, LinearMap.range (j r)) = ⊤ → (∀ g ∈ Op, ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (g x)) ∧ ∀ t ∈ N, Φ t ∈ N) → (∀ r, ∀ x ∈ Rel, j r x ∈ N) → RadFin Op Rel K → N ⊔ (⨆ r, K.map (j r)) = ⊤ → N = ⊤ := by
  intro M T R _ _ _ _ j Op Rel K N hspan hOp hRel hRad hsup
  classical
  have h1 : ∀ e ∈ Algebra.adjoin ℂ Op,
      ∃ Φ : Module.End ℂ T, (∀ r x, Φ (j r x) = j r (e x)) ∧ ∀ t ∈ N, Φ t ∈ N := by
    intro e he
    induction he using Algebra.adjoin_induction with
    | mem g hg => exact hOp g hg
    | algebraMap c =>
      refine ⟨c • (1 : Module.End ℂ T), fun r x => ?_, fun t ht => ?_⟩
      · simp [Algebra.algebraMap_eq_smul_one]
      · simpa using N.smul_mem c ht
    | add a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A + B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using N.add_mem (hAN t ht) (hBN t ht)
    | mul a b _ _ ha hb =>
      obtain ⟨A, hA, hAN⟩ := ha
      obtain ⟨B, hB, hBN⟩ := hb
      refine ⟨A * B, fun r x => ?_, fun t ht => ?_⟩
      · simp [hA, hB]
      · simpa using hAN _ (hBN t ht)
  have h2 : ∀ u ∈ (⨆ r, K.map (j r)), ∃ S : Finset M, (∀ k ∈ S, k ∈ K) ∧
      ∀ (e : Module.End ℂ M) (Φ : Module.End ℂ T), (∀ r x, Φ (j r x) = j r (e x)) →
        (∀ k ∈ S, e k ∈ Rel) → Φ u ∈ N := by
    intro u hu
    induction hu using Submodule.iSup_induction' with
    | mem r x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨{k}, by simpa using hk, fun e Φ hΦ hS => ?_⟩
      rw [hΦ]
      exact hRel r _ (hS k (Finset.mem_singleton_self k))
    | zero => exact ⟨∅, by simp, fun e Φ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨S, hS, hS'⟩ := hx
      obtain ⟨S2, hS2, hS2'⟩ := hy
      refine ⟨S ∪ S2, fun k hk => ?_, fun e Φ hΦ h => ?_⟩
      · rcases Finset.mem_union.1 hk with h | h
        · exact hS k h
        · exact hS2 k h
      · rw [map_add (f := _)]
        exact N.add_mem (hS' e Φ hΦ fun k hk => h k (Finset.mem_union_left _ hk))
          (hS2' e Φ hΦ fun k hk => h k (Finset.mem_union_right _ hk))
  obtain ⟨s, hGen, hs⟩ := hRad
  have h3 : ∀ r, j r s ∈ N := by
    intro r
    have hm : j r s ∈ N ⊔ (⨆ r, K.map (j r)) := by rw [hsup]; trivial
    obtain ⟨n, hn, u, hu, hnu⟩ := Submodule.mem_sup.1 hm
    obtain ⟨S, hSK, hS⟩ := h2 u hu
    obtain ⟨e, he, hes, heS⟩ := hs S hSK
    obtain ⟨Φ, hΦ, hΦN⟩ := h1 e he
    have : j r s = Φ n + Φ u := by rw [← map_add (f := _), hnu, hΦ, hes]
    rw [this]
    exact N.add_mem (hΦN n hn) (hS e Φ hΦ heS)
  have h4 : ∀ r, N.comap (j r) = ⊤ := by
    intro r
    refine hGen _ (fun x hx => hRel r x hx) (fun g hg x hx => ?_) (h3 r)
    obtain ⟨Φ, hΦ, hΦN⟩ := hOp g hg
    show j r (g x) ∈ N
    rw [← hΦ]
    exact hΦN _ hx
  rw [eq_top_iff, ← hspan]
  refine iSup_le fun r => ?_
  rintro _ ⟨x, rfl⟩
  have : x ∈ N.comap (j r) := by rw [h4 r]; trivial
  exact this
end

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.nakAll :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (Op : ∀ i, Set (Module.End ℂ (M i))) (Rel K : ∀ i, Submodule ℂ (M i)), (∀ i, Stable (Op i) (Rel i)) → (∀ i, Stable (Op i) (K i)) → (∀ i, Rad (Op i) (Rel i) (K i)) → ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)), (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) → (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) → N ⊔ (⨆ i, part M₀ i (K i)) = ⊤ → N = ⊤ := by
  intro ι _ _ M₀ _ _ M _ _ Op Rel K hRel hK hRad N hN hOp hsup
  have key : ∀ S : Finset ι, N ⊔ (⨆ i ∈ S, part M₀ i (K i)) = ⊤ → N = ⊤ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro h; simpa using h
    | insert i S hi ih =>
      intro h
      apply ih
      refine UpperTheory.Lit.HoweDuality.nak (fun r : M₀ × (∀ j, M j) => intersection_update_fsHerm_neg_one i r) (Op i) (Rel i) (K i) _
        (UpperTheory.Lit.HoweDuality.slotFacts i).1 (fun g hg => ⟨factorOp i g, (UpperTheory.Lit.HoweDuality.slotFacts i).2 g, ?_⟩)
        (fun r x hx => Submodule.mem_sup_left (hN i x hx r.1 r.2))
        (UpperTheory.Lit.HoweDuality.radFin _ _ _ (hRel i) (hK i) (hRad i)) ?_
      · have hle : N ⊔ (⨆ l ∈ S, part M₀ l (K l)) ≤
            (N ⊔ (⨆ l ∈ S, part M₀ l (K l))).comap (factorOp i g) := by
          refine sup_le (fun t ht => Submodule.mem_sup_left (hOp i g hg t ht))
            (iSup₂_le fun l hl t ht => Submodule.mem_sup_right ?_)
          have hne : i ≠ l := fun e => hi (e ▸ hl)
          exact (le_iSup₂ (f := fun l (_ : l ∈ S) => part M₀ l (K l)) l hl)
            ((UpperTheory.Lit.HoweDuality.partStable l (K l)).2.2 i hne g t ht)
        exact fun t ht => hle ht
      · rw [Finset.iSup_insert, sup_comm (part M₀ i (K i)), ← sup_assoc] at h
        exact h
  apply key Finset.univ
  simpa using hsup
end

open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

theorem UpperTheory.Lit.HoweDuality.tens :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ P₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] [AddCommGroup P₀] [Module ℂ P₀] {M P : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] (Op₀ : Set (Module.End ℂ M₀)) (Op : ∀ i, Set (Module.End ℂ (M i))) (Rel₀ : Submodule ℂ M₀) (Rel : ∀ i, Submodule ℂ (M i)) (p₀ : M₀ →ₗ[ℂ] P₀) (p : ∀ i, M i →ₗ[ℂ] P i), Module.rank ℂ M₀ ≤ Cardinal.aleph0 → (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M₀), StrictMono N → (∀ j, Rel₀ ≤ N j ∧ ∀ g ∈ Op₀, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) → (∀ N : Submodule ℂ M₀, Rel₀ ≤ N → (∀ g ∈ Op₀, ∀ x ∈ N, g x ∈ N) → N ≠ ⊤ → N ≤ LinearMap.ker p₀) → Rel₀ ≤ LinearMap.ker p₀ → (∀ g ∈ Op₀, ∀ x ∈ LinearMap.ker p₀, g x ∈ LinearMap.ker p₀) → (∀ i, Stable (Op i) (Rel i)) → (∀ i, Stable (Op i) (LinearMap.ker (p i))) → (∀ i, Rad (Op i) (Rel i) (LinearMap.ker (p i))) → (∀ i, ∀ N : Submodule ℂ (M i), LinearMap.ker (p i) ≤ N → Stable (Op i) N → N ≠ ⊤ → N ≤ LinearMap.ker (p i)) → ∀ N : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] i, M i)), (∀ x ∈ Rel₀, ∀ y, x ⊗ₜ[ℂ] y ∈ N) → (∀ i, ∀ x ∈ Rel i, ∀ (x₀ : M₀) (y : ∀ j, M j), x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y i x) ∈ N) → (∀ g ∈ Op₀, ∀ t ∈ N, TensorProduct.map g LinearMap.id t ∈ N) → (∀ i, ∀ g ∈ Op i, ∀ t ∈ N, TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g)) t ∈ N) → N = ⊤ ∨ N ≤ LinearMap.ker (TensorProduct.map p₀ (PiTensorProduct.map p)) := by
  intro ι _ _ M₀ P₀ _ _ _ _ M P _ _ _ _ Op₀ Op Rel₀ Rel p₀ p hr₀ hr hL₀ hmax₀ hRel₀ hker₀ hRel hK hRad
    hmax N hN₀ hN hOp₀ hOp
  have stab : ∀ Φ : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)), (∀ t ∈ N, Φ t ∈ N) →
      (∀ l, ∀ t ∈ part M₀ l (LinearMap.ker (p l)), Φ t ∈ part M₀ l (LinearMap.ker (p l))) →
      ∀ t ∈ N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))),
        Φ t ∈ N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))) := by
    intro Φ h1 h2
    have hle : N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))) ≤
        (N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l)))).comap Φ :=
      sup_le (fun t ht => Submodule.mem_sup_left (h1 t ht))
        (iSup_le fun l t ht => Submodule.mem_sup_right
          ((le_iSup (fun l => part M₀ l (LinearMap.ker (p l))) l) (h2 l t ht)))
    exact fun t ht => hle ht
  have key := GlobalTheory.T.tensor_eq_top_or_le_ker_finiteLength_modules Op₀ Op Rel₀ (fun i => LinearMap.ker (p i)) p₀ p hr₀ hr hL₀ hmax₀ hRel₀ hker₀
    (fun i => ⟨2, fun m C hC h => ?_⟩) hmax (fun i => le_rfl) hK
    (N ⊔ (⨆ l, part M₀ l (LinearMap.ker (p l))))
    (fun x hx y => Submodule.mem_sup_left (hN₀ x hx y))
    (fun i x hx x₀ y => Submodule.mem_sup_right
      ((le_iSup (fun l => part M₀ l (LinearMap.ker (p l))) i)
        ((le_iSup (fun r : M₀ × ∀ j, M j => (LinearMap.ker (p i)).map (intersection_update_fsHerm_neg_one i r)) (x₀, y))
          (Submodule.mem_map_of_mem hx))))
    (fun g hg => stab _ (hOp₀ g hg) fun l => (partStable l _).1 g)
    (fun i g hg => stab (factorOp i g) (hOp i g hg) fun l => ?_)
  · rcases key with h | h
    · exact Or.inl (nakAll Op Rel (fun i => LinearMap.ker (p i)) hRel hK hRad N hN hOp h)
    · exact Or.inr (le_sup_left.trans h)
  · by_contra hm
    have hm : 2 < m := not_le.1 hm
    have h01 : C ⟨0, by omega⟩ < C ⟨1, by omega⟩ := hC (by simp [Fin.lt_def])
    have h12 : C ⟨1, by omega⟩ < C ⟨2, hm⟩ := hC (by simp [Fin.lt_def])
    have h1 := hmax i _ (h ⟨1, by omega⟩).1 (h ⟨1, by omega⟩).2 h12.ne_top
    exact absurd (h01.trans_le (h1.trans (h ⟨0, by omega⟩).1)) (lt_irrefl _)
  · by_cases hl : i = l
    · subst hl
      exact (partStable i _).2.1 g (hK i g hg)
    · exact (partStable l _).2.2 i hl g
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace UpperTheory.Lit.HoweDuality

open GlobalTheory.HoweGlobalPair

private theorem relStable :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl (F := F)} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → Stable (opFin om v) (relFin om v) := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL g hg x hx
  obtain ⟨h, hh, hact⟩ := hg
  have h1X : (1 : UA σ X.J) ∈ UAt σ X ⇑(evFin F v) := by
    show At _ (mat (1 : UA σ X.J) - 1)
    intro u _
    rw [show mat (1 : UA σ X.J) = 1 from rfl, sub_self, smul_zero]
  have h1W : (1 : UA σ W.J) ∈ UAt σ W ⇑(evFin F v) := by
    show At _ (mat (1 : UA σ W.J) - 1)
    intro u _
    rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]
  have hgx : ((g x : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) = ω (1, h) (x : (Fin n × Fin d → Fv F v) → ℂ) :=
    (hL.acts 1 h1X h hh x x.2 _).1 (hact x)
  have key : augAt om v ≤ (augAt om v).comap (ω (1, h)) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g', hg', φ, hφ, φ₁, hφ₁, hA, rfl⟩
    have e1 : φ₁ = ω (g', 1) φ := (hL.acts g' hg' 1 h1W φ hφ φ₁).1 hA
    subst e1
    have m1 := hL.mul 1 h1X h hh g' hg' 1 h1W φ hφ
    have m2 := hL.mul g' hg' 1 h1W 1 h1X h hh φ hφ
    simp only [one_mul, mul_one] at m1 m2
    have hp : ω (1, h) φ ∈ SB (Fin n × Fin d → Fv F v) := hL.pres 1 h1X h hh φ hφ
    simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub]
    rw [← m1, m2]
    exact Submodule.subset_span ⟨g', hg', ω (1, h) φ, hp, ω (g', 1) (ω (1, h) φ),
      hL.pres g' hg' 1 h1W _ hp, (hL.acts g' hg' 1 h1W _ hp _).2 rfl, rfl⟩
  have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := hx
  show ((g x : SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v
  rw [hgx]
  exact key hx'

theorem sphTri : PositivityTheory.Sph.SphTri :=
  PositivityTheory.Sph.sphTri_of PositivityTheory.Sph.sphSplit_geo (PositivityTheory.Sph.vacInert PositivityTheory.Sph.howeInert)

theorem locV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ}
    {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    (hM : IsMatched Bs G Xc om om' R Rf) (v : Pl (F := F)) :
    Stable (opFin om v) (relFin om v) ∧
      Rad (opFin om v) (relFin om v) (LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype)) := by
  obtain ⟨ω, ρ, L⟩ := (PositivityTheory.Sph.locRep_tri hM.triple v).1
  have hk := kerV hM v
  refine ⟨relStable L, ?_⟩
  rcases (sphTri F E σ Bs a a' G Xc om om' hM.triple v).1 with h | h
  · exact radSph L h _ hk.1 hk.2.1 hk.2.2.1
  · exact radIrr L h _ hk.1 hk.2.1 hk.2.2.1

theorem locVp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ}
    {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    (hM : IsMatched Bs G Xc om om' R Rf) (v : Pl (F := F)) :
    Stable (opFin om' v) (relFin om' v) ∧
      Rad (opFin om' v) (relFin om' v) (LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype)) := by
  obtain ⟨ω, ρ, L⟩ := (PositivityTheory.Sph.locRep_tri hM.triple v).2
  have hk := kerVp hM v
  refine ⟨relStable L, ?_⟩
  rcases (sphTri F E σ Bs a a' G Xc om om' hM.triple v).2 with h | h
  · exact radSph L h _ hk.1 hk.2.1 hk.2.2.1
  · exact radIrr L h _ hk.1 hk.2.1 hk.2.2.1

theorem stageVp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      ∀ T : Finset (Pl (F := F)), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T → PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN T hT
  classical
  have hTr := hM.triple
  have hg := hTr.geo
  have hc := hTr.chars
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  have hlie := GlobalTheory.T.firstMember_lieAlgebra_preserves_polynomialFock F E σ hTr.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hTr.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hTr.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hcpt := GlobalTheory.T.firstMember_maximalCompact_preserves_polynomialFock F E σ hTr.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hTr.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hTr.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M' Bs.ψ Bs.emb hg.hM'.std T
  have hloc := GlobalTheory.T.howeDuality_realPlaces_polynomialVectors_smallPair F E σ Bs a a' G Xc om om' R Rf hM hreal hlie hcpt
  have hfl := fun v => locVp hM v
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.unitaryDualPair_global_to_local_tensor_transfer G.M' Bs.ψ Bs.emb om' (fun v => (hg.hM'.vac v).1) hg.hM'.std N hN T L hL
  have key := tens (ι := T) (M₀ := ↥(G.M'.Pol Bs.ψ Bs.emb))
    (M := fun v : T => ↥(SB (Fin a' × Fin (a + a') → Fv F v.1)))
    (opInf G.M' Bs.ψ Bs.emb om') (fun v => opFin om' v.1)
    (relInf G.M' Bs.ψ Bs.emb om') (fun v => relFin om' v.1)
    (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) (fun v => Rf.p' v.1 ∘ₗ (SB _).subtype)
    hloc.1 (fun v => GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le F _ v.1) hloc.2.1 hloc.2.2.1 hloc.2.2.2.1 hloc.2.2.2.2
    (fun v => (hfl v.1).1) (fun v => (kerVp hM v.1).2.1) (fun v => (hfl v.1).2) (fun v => (kerVp hM v.1).2.2.2)
    (N.comap L) h1 h2 h3 h4
  rcases key with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦT
    obtain ⟨t, rfl⟩ := hrange hΦT
    have ht0 := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := GlobalTheory.HoweGlobalPair.decomp t
    refine ⟨T, hT, 0, m, Fin.elim0, Fin.elim0, fun j => ((f j : ↥(G.M'.Pol Bs.ψ Bs.emb)) : SInf F (Fin a' × Fin (a + a'))),
      fun j v => if h : v ∈ T then ((φ j ⟨v, h⟩ : ↥(SB _)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) else G.M'.vac v,
      fun j => Fin.elim0 j, fun j => ⟨(f j).2, fun v => ?_, fun v hv => by simp only [dif_neg hv]⟩, ?_, ?_, ?_⟩
    · by_cases h : v ∈ T
      · simp only [dif_pos h]; exact (φ j ⟨v, h⟩).2
      · simp only [dif_neg h]; exact (hg.hM'.vac v).1
    · simp
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hL _ _ _ (fun v h => by simp only [dif_pos h]) (fun v h => by simp only [dif_neg h])
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.mem_ker, map_sum] at ht0
      rw [Fin.sum_univ_zero, ← ht0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
      simp

theorem allVp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      N ≠ GlobalTheory.SquareAgree.algD G.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN hne Φ hΦ
  by_contra hcon
  obtain ⟨T, hT, hΦT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb (hN.le hΦ) Xc.T
  apply hne
  refine le_antisymm hN.le fun Ψ hΨ => ?_
  obtain ⟨T', hT', hΨT'⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb hΨ T
  rcases stageVp F E σ Bs a a' G Xc om om' R Rf hM hreal N hN T' (hT.trans hT') with h | h
  · exact h hΨT'
  · exact absurd (h Φ hΦ (GlobalTheory.HoweGlobal.algAt_mono G.M' Bs.ψ Bs.emb hT' hΦT)) hcon

end UpperTheory.Lit.HoweDuality

end
