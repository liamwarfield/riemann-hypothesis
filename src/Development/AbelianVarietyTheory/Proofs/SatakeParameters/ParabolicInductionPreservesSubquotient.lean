module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.ParIndSubquot

theorem parInd_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e W W' _ _ _ _ ρ ρ' hρ' h
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι hι).isSmooth hρ'
  have hinj : Function.Injective (parIndMap e ι) := by
    intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hι ?_))
    exact congrFun (congrArg (fun χ : IndSp e ρ' => χ.1.1) hφψ) g
  let σ₀ : Representation ℂ (parab k e) S.toSubmodule := (SmGL.twist S.toRepresentation (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  have hsurj : Function.Surjective (parIndMap e f) := by
    refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
      hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
      (isSmooth_comp (isSmooth_twist hS (isSmoothChar_deltaHalf k)) _ hcont)
      (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
    intro x _
    refine Submodule.subset_span ⟨(), -x, ?_⟩
    show x = (0 : _) - -x
    simp
  exact (IsSubquotient.of_surjective (parIndMap e f) hsurj).trans (IsSubquotient.of_injective (parIndMap e ι) hinj)

end GlobalTheory.ParIndSubquot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotientStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInduction_preserves_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := by
  first | exact @GlobalTheory.ParIndSubquot.parInd_isSubquotient | exact GlobalTheory.ParIndSubquot.parInd_isSubquotient | (intros; apply GlobalTheory.ParIndSubquot.parInd_isSubquotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.GoodCuspPoint

theorem param_parts_pos_rank (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (hx : HasParamX D.nd D.naut i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso D.nd D.naut Sig = D.R.r := by
  obtain ⟨P, -, hBC⟩ := hx
  refine ⟨fun p hp => ?_, ?_⟩
  · have hm : (⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ : Formalism.BasicNotions.Part D.naut.CG) ∈
        twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
      List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩
    exact ⟨(hBC.1 _ hm).1, (hBC.1 _ hm).2.1⟩
  · have h := hBC.2.2.1
    have e : rankIso D.nd D.naut (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) =
        rankIso D.nd D.naut Sig + D.R.t := by
      simp [rankIso, twistIso, muPart, List.map_map, Function.comp_def]
    rw [e] at h
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega

theorem cuspidal_of_good_labels (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tieLab D) (i : D.nd.Loc) (x : D.nd.X i)
    (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (hx : HasParamX D.nd D.naut i x Sig)
    (hg : goodSig D.nd D.naut Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨hpos, hrank⟩ := param_parts_pos_rank D i x Sig hx
  let k : Fin 2 := 0
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := (hg k).1
  have : Nonempty (D.nd.PlG k) := by
    rw [← Fintype.card_pos_iff, D.nd.card_PlG k]
    show 0 < 2 * D.R.ord
    have := D.R.ord_pos
    omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  have hf : ∀ v, D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) =
      ∏ j : Fin Sig.length,
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d := by
    intro v
    rw [Formalism.MainNotions.SumRepresentations.inertiaCharpoly_eq_of_iso D.nd D.naut hT k v Sig,
      Formalism.MainNotions.SumRepresentations.list_prod_fin Sig (fun p => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d)]
  have hrk : ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d = D.R.r := by
    rw [← hrank, rankIso, Formalism.MainNotions.SumRepresentations.list_sum_fin Sig (fun p => p.a * p.d)]
  have hd : ∀ j : Fin Sig.length, 1 ≤ (Sig.get j).a ∧ 1 ≤ (Sig.get j).d :=
    fun j => hpos _ (List.get_mem Sig j)
  have hdeg : ∀ v (j : Fin Sig.length),
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree =
        (Sig.get j).a := by
    intro v
    have hne : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hf v]
      exact (h1 v).1.ne_zero
    have hsum : ∑ j : Fin Sig.length,
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d =
        ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d := by
      have h1' : (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r :=
        (h1 v).2.1
      rw [hrk, ← h1', hf v, natDegree_prod _ _ hne]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, mul_comm]
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d ≤ (Sig.get j).a * (Sig.get j).d := by
      intro j _
      refine Nat.mul_le_mul_right _ ?_
      have := hT.2 k v (D.naut.locG (Sig.get j).π (D.naut.plGw k v))
      rwa [D.naut.locG_dim] at this
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)
    exact Nat.eq_of_mul_eq_mul_right (hd j).2 this
  obtain ⟨hc, hall⟩ := Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one (ZMod (D.host.g k)) (D.nd.PlG k) D.R.r
    (fun v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))
    (Fin Sig.length) (fun j => (Sig.get j).a) (fun j => (Sig.get j).d)
    (fun v j => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))) hr
    (fun v => (h1 v).2.1) h2 hf hdeg (fun j => (hd j).1) (fun j => (hd j).2)
    (by
      rintro ⟨a, ha1, ha2, ha⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (ha v))
  rw [Fintype.card_fin] at hc
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hc
  obtain ⟨hd1, ha1⟩ := hall ⟨0, by simp⟩
  obtain ⟨a, π, d⟩ := p
  simp only [List.get_eq_getElem, List.getElem_cons_zero] at hd1 ha1
  subst hd1 ha1
  exact ⟨π, rfl⟩

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tieLab D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut :=
  fun D hT i x Sig hx hg => cuspidal_of_good_labels D hT i x Sig hx hg

end GlobalTheory.GoodCuspPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodLabels_rank_part_parameter_cuspidal : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tieLab D → GlobalTheory.LocalInv.GoodCuspidal D.nd D.naut := by
  first | exact @GlobalTheory.GoodCuspPoint.main | exact GlobalTheory.GoodCuspPoint.main | (intros; apply GlobalTheory.GoodCuspPoint.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead
open scoped TensorProduct

namespace GlobalTheory.ProdReorder

section Eqv

variable {G V W U : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}

theorem eqv_trans (h₁ : Nonempty (ρ.Equiv σ)) (h₂ : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) :=
  h₁.elim fun a => h₂.elim fun b => ⟨a.trans b⟩

theorem eqv_symm (h : Nonempty (ρ.Equiv σ)) : Nonempty (σ.Equiv ρ) := h.map Representation.Equiv.symm

theorem eqv_refl (ρ : Representation ℂ G V) : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩

end Eqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_placing {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e e' : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π)) :=
  (Placing.parInd_jac_placing k α n m e e' _).1 _

theorem ind₂_congr {r t N : ℕ} (h : r + t = N) {V V' W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {π₁ : Representation ℂ (GL (Fin r) k) V} {σ₁ : Representation ℂ (GL (Fin r) k) V'}
    {π₂ : Representation ℂ (GL (Fin t) k) W} {σ₂ : Representation ℂ (GL (Fin t) k) W'}
    (φ₁ : Nonempty (π₁.Equiv σ₁)) (φ₂ : Nonempty (π₂.Equiv σ₂)) :
    Nonempty ((ind₂ (stdSum h) (extTensor π₁ π₂)).Equiv (ind₂ (stdSum h) (extTensor σ₁ σ₂))) := by
  subst h
  exact φ₁.elim fun a => φ₂.elim fun b => ⟨LocGL.prod₂Equiv a b⟩

theorem ind₂_assoc' {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M')
    (h₄ : r + M' = N) {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (π₁ : Representation ℂ (GL (Fin r) k) V₁)
    (π₂ : Representation ℂ (GL (Fin s) k) V₂) (π₃ : Representation ℂ (GL (Fin t) k) V₃)
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃) :
    Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h₁) (extTensor π₁ π₂)) π₃)).Equiv
      (ind₂ (stdSum h₄) (extTensor π₁ (ind₂ (stdSum h₃) (extTensor π₂ π₃))))) := by
  subst h₁ h₃ h₂
  exact Stages.prod₂_assoc k r s t V₁ V₂ V₃ π₁ π₂ π₃ s₁ s₂ s₃

theorem multiProd_head {s : ℕ} {d : Fin (s + 1) → ℕ} {X : Fin (s + 1) → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) {T N : ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) (h : d 0 + T = N) (e' : (Σ a : Fin s, Fin (d a.succ)) ≃ Fin T) :
    Nonempty ((multiProd e π).Equiv
      (ind₂ (stdSum h) (extTensor (π 0) (multiProd e' fun a : Fin s => π a.succ)))) := by
  have hT : T = ∑ a : Fin s, d a.succ := by
    have := Fintype.card_congr e'
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact this.symm
  subst hT h
  have A := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := k) d (Fin.sum_univ_succ d) π
  have B := multiProd_placing (k := k) e (stdBlocks d (Fin.sum_univ_succ d)) π
  have C := multiProd_placing (k := k) (stdBlocks (fun i : Fin s => d i.succ) rfl) e' fun a => π a.succ
  exact A.elim fun A => B.elim fun B => C.elim fun C =>
    ⟨B.trans (A.symm.trans (LocGL.prod₂Equiv (Representation.Equiv.refl (π 0)) C))⟩

theorem multiProd_empty {d d' : Fin 0 → ℕ} {X X' : Fin 0 → Type} [iX : ∀ a, AddCommGroup (X a)]
    [mX : ∀ a, Module ℂ (X a)] [iX' : ∀ a, AddCommGroup (X' a)] [mX' : ∀ a, Module ℂ (X' a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d' a)) k) (X' a))
    {t : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin t) (e' : (Σ a, Fin (d' a)) ≃ Fin t) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π')) := by
  obtain rfl : d = d' := funext fun a => a.elim0
  obtain rfl : X = X' := funext fun a => a.elim0
  obtain rfl : iX = iX' := funext fun a => a.elim0
  obtain rfl : mX = mX' := funext fun a => a.elim0
  obtain rfl : π = π' := funext fun a => a.elim0
  exact multiProd_placing e e' π

theorem ind₂_unit_right {r t : ℕ} (h : r + t = r) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) {d : Fin 0 → ℕ} {X : Fin 0 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor π (multiProd e τ))).Equiv π) := by
  let f : (Σ _ : Fin 1, Fin r) ≃ Fin r :=
    { toFun := Sigma.snd
      invFun := fun i => ⟨0, i⟩
      left_inv := fun ⟨a, i⟩ => by obtain rfl := Subsingleton.elim a 0; rfl
      right_inv := fun _ => rfl }
  let e' : (Σ a : Fin 0, Fin r) ≃ Fin t :=
    (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin r) (Σ a, Fin (d a))).trans e
  have A := LocGL.nonempty_equiv_multiProd_one hπ f fun _ _ => rfl
  have B := multiProd_head (k := k) (d := fun _ : Fin 1 => r) (fun _ => π) f h e'
  have C := ind₂_congr h (eqv_refl π) (multiProd_empty (k := k) (fun a : Fin 0 => π) τ e' e)
  exact eqv_symm (eqv_trans A (eqv_trans B C))

theorem multiProd_comp_congr {s u : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) {f g : Fin u → Fin s} (hfg : f = g)
    {T : ℕ} (e : (Σ i, Fin (d (f i))) ≃ Fin T) (e' : (Σ i, Fin (d (g i))) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (σ (f i)).π).Equiv (multiProd e' fun i => (σ (g i)).π)) := by
  subst hfg
  exact multiProd_placing e e' _

def sigmaPart {s s₁ s₂ : ℕ} (d : Fin s → ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s)
    (hb : Function.Bijective (Sum.elim ι₁ ι₂)) :
    (Σ a, Fin (d a)) ≃ (Σ i, Fin (d (ι₁ i))) ⊕ (Σ j, Fin (d (ι₂ j))) :=
  (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) (Equiv.ofBijective _ hb)).symm.trans
    (Equiv.sumSigmaDistrib fun x => Fin (d (Sum.elim ι₁ ι₂ x)))

def Commutes {p q : ℕ} (x : Irr k p) (y : Irr k q) : Prop :=
  ∀ (N : ℕ) (h₁ : p + q = N) (h₂ : q + p = N),
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π y.π)).Equiv (ind₂ (stdSum h₂) (extTensor y.π x.π)))

theorem Commutes.symm {p q : ℕ} {x : Irr k p} {y : Irr k q} (h : Commutes x y) : Commutes y x :=
  fun N h₁ h₂ => (h N h₂ h₁).map Representation.Equiv.symm

end GlobalTheory.ProdReorder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChange
noncomputable section

namespace GlobalTheory.SatBcZero

section Weyl

open Formalism.UG GlobalTheory.SatakeWeyl

theorem weyl_of_coeff (hswap : CoeffSwap) (hneg : CoeffNeg) (L : Type) [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ)
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) (α : Fin m → ℂ)
    (h : GU σ n → ℂ) (hh : h ∈ Hecke ℂ (KU σ n)) :
    (∀ π : Equiv.Perm (Fin m), SatU ϖ q h (α ∘ π) = SatU ϖ q h α) ∧
      ∀ i : Fin m, SatU ϖ q h (Function.update α i (α i)⁻¹) = SatU ϖ q h α := by
  have hex := fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a
  choose T hT using hex
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i := fun f =>
    (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |>
      congrArg (Units.coeHom ℂ) |> fun e => by
        simpa [map_prod, ← ofAdd_sum] using e.symm
  set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 *
    (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef
  have h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a := by
    refine perm_of_swap S fun i j hij a => ?_
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    simp only [hSdef]
    rw [hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]
    · simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
      push_cast
      ring
    · rintro c - ⟨hc, hc'⟩
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]
  have h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j hj a
    simp only [hSdef]
    rw [hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Function.update_self]
      ring
    · intro c _ hc
      rw [Function.update_of_ne hc, sub_self]
    · simp
  have h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j a
    have hj := j.2
    let l : Fin m := ⟨m - 1, by omega⟩
    rw [← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l),
      ← h1 (Equiv.swap j l) (Function.update a j (-a j))]
    congr 1
    rw [Function.update_comp_equiv]
    simp
  refine ⟨fun π => ?_, fun i => ?_⟩
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_perm S π (h1 π) α
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_neg S i (h3 i) α

theorem coeff_symm : CoeffSwap ∧ CoeffNeg := by
  have hr : RankOne := GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps GlobalTheory.T.cell_sum_two_stage_descent_unipotent GlobalTheory.T.cell_sum_left_right_invariance_normaliser
    (GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity (GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex GlobalTheory.T.finite_index_left_right_coset_sums_eq) GlobalTheory.T.contracting_automorphism_subgroup_chain_index)
  have hl : LeviStep := GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr GlobalTheory.T.exists_smaller_unitary_group_embedding GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts GlobalTheory.T.unitary_diagonal_factorization_along_embedding GlobalTheory.T.unitary_levi_normalizes_unipotent_radical
    (GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart GlobalTheory.T.unitary_block_triangular_levi_part_unitary) GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq
  have hi : IntIndex := GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq
  have ht : TraceZeroIndex := GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq hi
  exact ⟨GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets,
    GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction hl (GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard ht) (GlobalTheory.T.unitaryRankThreeRootIndex_of_cards hi ht)⟩

end Weyl

theorem eq_of_invariant (m : ℕ) (f : (Fin m → ℂ) → ℂ)
    (hf : ∀ α : Fin m → ℂ, (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧
      ∀ i, f (Function.update α i (α i)⁻¹) = f α) (α α' : Fin m → ℂ)
    (h : Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) =
      Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹)) : f α = f α' := by
  classical
  have h2 := congrArg (Multiset.map (fun x : ℂ => s(x, x⁻¹))) h
  simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => s((γ i)⁻¹, γ i)) = fun i => s(γ i, (γ i)⁻¹) :=
    fun γ => funext fun i => Sym2.eq_swap
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => s(α i, (α i)⁻¹))
      = Finset.univ.val.map (fun i => s(α' i, (α' i)⁻¹)) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := GlobalTheory.exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    rcases Sym2.eq_iff.1 (hπ i) with h4 | h4
    · exact Or.inl h4.1.symm
    · exact Or.inr h4.2.symm
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf (fun i => if i ∈ s then α' i else (α ∘ π) i)).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α).1 π, ← this]

theorem satU_eq_of_ubc_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K)
    (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂ,
      Formalism.MainNotions.N.ubc n (Finset.univ.val.map α) = Formalism.MainNotions.N.ubc n (Finset.univ.val.map α') →
      ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h α' := by
  intro K _ _ _ ϖ σ q n hU α α' e φ hφ
  unfold Formalism.MainNotions.N.ubc at e
  have e1 := add_right_cancel e
  refine eq_of_invariant _ (Formalism.UG.SatU ϖ q φ)
    (fun γ => weyl_of_coeff coeff_symm.1 coeff_symm.2 K ϖ σ q n (n / 2) hU (by omega) (by omega) γ φ hφ) _ _ ?_
  simpa only [Multiset.map_map, Function.comp_def] using e1

end GlobalTheory.SatBcZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatake_eq_of_same_unramifiedBaseChange : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂ, ubc n (Finset.univ.val.map α) = ubc n (Finset.univ.val.map α') → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h α' := by
  first | exact @GlobalTheory.SatBcZero.satU_eq_of_ubc_eq | exact GlobalTheory.SatBcZero.satU_eq_of_ubc_eq | (intros; apply GlobalTheory.SatBcZero.satU_eq_of_ubc_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem conj_sqrtMinusD : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h2 := D.host.conjE_apply D.host.φ₀ D.host.sqrtMinusD
  have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h2, map_neg, h3]
  simp

theorem sqrtMinusD_mul_self : D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E) := by
  rw [← sq]
  exact D.host.sqd_sq

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj]

theorem mem_F_iff (x : D.host.E) : x ∈ D.host.F ↔ D.host.conj x = x :=
  D.host.conjE_mem_hostF_iff x

theorem d_ne_zero : ((D.host.d : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero

theorem sqrtMinusD_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have := sqrtMinusD_mul_self D
  rw [h, zero_mul, eq_comm, neg_eq_zero] at this
  exact d_ne_zero D this

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem hypEFK : Formalism.MainNotions.SphericalInertData.HypEFK D := by
  rw [Formalism.MainNotions.SphericalInertData.HypEFK, eq_top_iff]
  intro x _
  set c := D.host.conj
  set s := D.host.sqrtMinusD
  have hs : s ≠ 0 := sqrtMinusD_ne_zero D
  have hcs : c s = -s := conj_sqrtMinusD D
  have hcc : c (c x) = x := conj_conj D x
  have hu : (x + c x) / 2 ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x + c x) / 2) = _
    rw [map_div₀, map_add (f := _), hcc, map_ofNat, add_comm]
  have hv : (x - c x) / (2 * s) ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x - c x) / (2 * s)) = _
    rw [map_div₀, map_sub, map_mul, hcc, map_ofNat, hcs]
    field_simp
    ring
  have hK : s ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hx : x = (x + c x) / 2 + (x - c x) / (2 * s) * s := by
    field_simp
    ring
  rw [hx]
  refine add_mem (Subfield.subset_closure (Or.inl hu))
    (mul_mem (Subfield.subset_closure (Or.inl hv)) (Subfield.subset_closure (Or.inr hK)))

theorem two_le_finrank : 2 ≤ Module.finrank ℚ D.host.F := by
  have h := D.host.finrank_hostF
  show 2 ≤ Module.finrank ℚ (D.host.F)
  rw [h]
  have := D.R.ord_pos
  omega

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits Polynomial

variable (D : D7)

theorem d_eq : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by
  have := D.host.hyp.2.2.2.1; omega⟩

theorem isIntegral_half (y : D.host.E) (hy : y * y = -((D.host.d : ℕ) : D.host.E)) :
    IsIntegral ℤ ((1 + y) / 2) := by
  obtain ⟨m, hm⟩ := d_eq D
  refine ⟨X ^ 2 - X + C (2 * (m : ℤ)), ?_, ?_⟩
  · have : (X ^ 2 - X + C (2 * (m : ℤ)) : ℤ[X]) = X ^ 2 + (C (2 * (m : ℤ)) - X) := by ring
    rw [this]
    refine (monic_X_pow 2).add_of_left ?_
    refine lt_of_le_of_lt (degree_sub_le _ _) ?_
    rw [degree_X_pow, degree_X]
    refine max_lt (lt_of_le_of_lt degree_C_le (by norm_num)) (by norm_num)
  · have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, algebraMap_int_eq, eq_intCast]
    push_cast
    rw [hd] at hy
    linear_combination (1/4 : D.host.E) * hy

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem isSplitPl_of_two_mem (w : PlE D.host) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    IsSplitPl D.host w := by
  set s := D.host.sqrtMinusD
  have hss : s * s = -((D.host.d : ℕ) : D.host.E) := sqrtMinusD_mul_self D
  have hss' : (-s) * (-s) = -((D.host.d : ℕ) : D.host.E) := by rw [neg_mul_neg]; exact hss
  have hcs : D.host.conj s = -s := conj_sqrtMinusD D
  obtain ⟨m, hm⟩ := d_eq D
  let α : 𝓞 D.host.E := ⟨(1 + s) / 2, isIntegral_half D s hss⟩
  let β : 𝓞 D.host.E := ⟨(1 + -s) / 2, isIntegral_half D (-s) hss'⟩
  have hα : ((α : 𝓞 D.host.E) : D.host.E) = (1 + s) / 2 := rfl
  have hβ : ((β : 𝓞 D.host.E) : D.host.E) = (1 + -s) / 2 := rfl
  have hsum : α + β = 1 := by
    apply RingOfIntegers.ext
    show (1 + s) / 2 + (1 + -s) / 2 = ((1 : 𝓞 D.host.E) : D.host.E)
    push_cast
    ring
  have hprod : α * β = ((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have key : ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) = 2 * (m : D.host.E) := by
      exact (map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _).trans (by rw [map_natCast, map_natCast]; norm_num)
    show (1 + s) / 2 * ((1 + -s) / 2) = ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)
    rw [key]
    have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    rw [hd] at hss
    linear_combination (-1/4 : D.host.E) * hss
  have hcα : D.host.conj ((α : 𝓞 D.host.E) : D.host.E) = ((β : 𝓞 D.host.E) : D.host.E) := by
    rw [hα, hβ, map_div₀, map_add (f := _), map_one, hcs, map_ofNat]
  have hcβ : D.host.conj ((β : 𝓞 D.host.E) : D.host.E) = ((α : 𝓞 D.host.E) : D.host.E) := by
    rw [← hcα, conj_conj]
  have hne : ∀ x y : 𝓞 D.host.E, x + y = 1 → x ∈ w.asIdeal → y ∉ w.asIdeal := by
    intro x y hxy hx hy
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem hx hy))
  have hmem : α * β ∈ w.asIdeal := by
    rw [hprod]; exact Ideal.mul_mem_right _ _ h2
  rcases w.isPrime.mem_or_mem hmem with ha | hb
  · refine ⟨α, ha, fun y hy => ?_⟩
    have : y = β := RingOfIntegers.coe_injective (hy.trans hcα)
    rw [this]; exact hne α β hsum ha
  · refine ⟨β, hb, fun y hy => ?_⟩
    have : y = α := RingOfIntegers.coe_injective (hy.trans hcβ)
    rw [this]; exact hne β α (by rw [add_comm]; exact hsum) hb

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

theorem jointCond_of_definite : ∀ D : D7, (∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)) →
    GlobalDatumCompatibility D := by
  intro D hdef
  refine ⟨hypEFK D, ⟨two_le_finrank D, fun w hw h2 => hw (isSplitPl_of_two_mem D w h2)⟩, hdef⟩

end GlobalTheory.DesignBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHost
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHost
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitPlaceConj

theorem isSplitPl_w : ∀ (D : D7) (s : SplitPlace D.host.E), IsSplitPl D.host s.w := by
  intro D s
  have hc : ∀ z : D.host.E, IsCMField.complexConj D.host.E z = D.host.conj z := by
    intro z
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep D.host.E s
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E :=
    RingOfIntegers.mapRingHom (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E)
  have hce : ((c e : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (e : D.host.E) := rfl
  refine ⟨c e, (s.split_mem_ideal _).2 (by rw [hce]; exact he'), fun y hy hm => ?_⟩
  have hye : (y : D.host.E) = (e : D.host.E) := by
    rw [hy, hce, ← hc, IsCMField.complexConj_apply_apply]
  have h1 := (s.split_mem_ideal y).1 hm
  rw [hye, he] at h1
  exact lt_irrefl _ h1

end GlobalTheory.SplitPlaceConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHostStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host : ∀ (D : D7) (s : SplitPlace D.host.E), IsSplitPl D.host s.w := by
  first | exact @GlobalTheory.SplitPlaceConj.isSplitPl_w | exact GlobalTheory.SplitPlaceConj.isSplitPl_w | (intros; apply GlobalTheory.SplitPlaceConj.isSplitPl_w <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitCompl

theorem exists_ringEquiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L),
    ∃ i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous i ∧ Continuous i.symm ∧
      ∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x := by
  intro L _ _ _ s

  have hf : ∀ x : L, Valued.v (s.i.toRingHom x) = s.w.valuation L x :=
    fun x => PI.CompAtExist.muV_eq s x
  obtain ⟨φ, hφc, hφ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.w s.v (f := s.i.toRingHom) hf

  let g : maximalRealSubfield L →+* s.w.adicCompletion L :=
    (algebraMap L (s.w.adicCompletion L)).comp (algebraMap (maximalRealSubfield L) L)
  have hg : ∀ a, Valued.v (g a) = s.v.valuation (maximalRealSubfield L) a := by
    intro a
    simp only [g, RingHom.comp_apply]
    rw [GlobalTheory.Idele.valued_algebraMap, ← PI.CompAtExist.muV_eq s, PI.CompAtExist.muV_apply, AlgHom.commutes,
      GlobalTheory.Idele.valued_algebraMap]
  obtain ⟨ψ, hψc, hψ, -⟩ := GlobalTheory.DenseCompl.exists_extension s.v s.w g hg
  have hcomp : ∀ y, φ (ψ y) = y := by
    intro y
    refine (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) s.v).induction_on
      (p := fun y => φ (ψ y) = y) y (isClosed_eq (hφc.comp hψc) continuous_id) fun a => ?_
    rw [hψ]
    simp only [g, RingHom.comp_apply]
    rw [hφ]
    exact s.i.commutes a
  have hsurj : Function.Surjective φ := fun y => ⟨ψ y, hcomp y⟩
  let e := RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have he : ∀ y, e.symm y = ψ y := fun y => e.injective (by rw [e.apply_symm_apply]; exact (hcomp y).symm)
  refine ⟨e.symm, ?_, ?_, fun x => ?_⟩
  · exact hψc.congr fun y => (he y).symm
  · exact hφc
  · have h := e.symm_apply_apply (algebraMap L (s.w.adicCompletion L) x)
    exact (congrArg e.symm (hφ x)).symm.trans h

end GlobalTheory.SplitCompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHost
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHost
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompactRepField

theorem exists_hom_of_entries_mem {F E Γ : Type} [Field F] [Field E] [Algebra F E] [Group Γ]
    {a : ℕ} (r : Γ →* GL (Fin a) E) (K : IntermediateField F E)
    (h : ∀ g i j, (r g : Matrix (Fin a) (Fin a) E) i j ∈ K) :
    ∃ r₁ : Γ →* GL (Fin a) ↥K, ∀ g i j,
      ((r₁ g : Matrix (Fin a) (Fin a) ↥K) i j : E) = (r g : Matrix (Fin a) (Fin a) E) i j := by
  let m : Γ →* Matrix (Fin a) (Fin a) ↥K :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, h g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  exact ⟨m.toHomUnits, fun g i j => rfl⟩

theorem exists_continuous_model :
    ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1), Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := by
  intro D l _ a ρ hρ L₀
  obtain ⟨L, hL, h⟩ := exists_finExt_entries_mem l (G D.host.E D.nd.Om) a ρ hρ L₀
  obtain ⟨ρ₁, h₁⟩ := exists_hom_of_entries_mem ρ L.1 h
  refine ⟨L, hL, ρ₁, ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    refine continuous_induced_rng.2 ?_
    exact (hρ.matrix_elem i j).congr fun g => (h₁ g i j).symm
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    exact h₁ g i j

end GlobalTheory.CompactRepField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHostStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_ladicGalRep_model_finite_ext_host : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1), Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := by
  first | exact @GlobalTheory.CompactRepField.exists_continuous_model | exact GlobalTheory.CompactRepField.exists_continuous_model | (intros; apply GlobalTheory.CompactRepField.exists_continuous_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.JacTensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def oneBlock (N : ℕ) : (Σ _ : Fin 1, Fin N) ≃ Fin N where
  toFun p := p.2
  invFun i := ⟨0, i⟩
  left_inv p := by
    obtain ⟨a, i⟩ := p
    rw [Subsingleton.elim a 0]
  right_inv _ := rfl

theorem isIrreducible_multiProd_fin_one {N : ℕ} {c : Fin 1 → ℕ} (g : (Σ i, Fin (c i)) ≃ Fin N)
    (s : ∀ i, IrrRep (GL (Fin (c i)) k)) : (multiProd g fun i => (s i).ρ).IsIrreducible := by
  obtain ⟨M, rfl⟩ : ∃ M, c = fun _ => M := ⟨c 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = fun _ => s₀ := ⟨s 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain rfl : M = N := by simpa using Fintype.card_congr g
  obtain ⟨φ₁⟩ := (Placing.parInd_jac_placing k (Fin 1) (Fin M) (fun _ => Fin M) g (oneBlock M) _).1
    (piTensor fun _ : Fin 1 => s₀.ρ)
  obtain ⟨φ₂⟩ := LocGL.nonempty_equiv_multiProd_one s₀.smooth (oneBlock M) fun _ _ => rfl
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (φ₂.trans φ₁.symm) s₀.irr

end GlobalTheory.JacTensor


open GlobalTheory.JacTensor in
theorem GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (GlobalTheory.SmGL.jac e π.π) → ∃ σ : ∀ a, Irr k (d a), IsSubquotient τ (piTensor fun a => (σ a).π) := by
  intro hGL k _ _ _ _ n π s d e Y _ _ τ hτ hs
  obtain ⟨φ⟩ := LocGL.nonempty_equiv_multiProd_one π.smooth (oneBlock n) fun _ _ => rfl
  have h1 : IsSubquotient τ (GlobalTheory.SmGL.jac e (multiProd (oneBlock n) fun _ : Fin 1 => π.π)) :=
    hs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e (isSmooth_parInd _ _)
      (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective))
  obtain ⟨b, f, g, t, -, ht⟩ := exists_cell_of_isSubquotient (hGL k).1 (hGL k).2
    (m' := fun a => Fin (d a)) (oneBlock n) e (fun _ => π.smooth)
    (fun _ => hasFiniteLength_of_isIrreducible π.irr) hτ h1
  exact ⟨fun a => ⟨_, multiProd (g a) fun i => (t i a).ρ, isSmooth_parInd _ _,
    isIrreducible_multiProd_fin_one (g a) fun i => t i a⟩, ht⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotientStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_tensor_of_jacquet_subquotient : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (GlobalTheory.SmGL.jac e π.π) → ∃ σ : ∀ a, Irr k (d a), IsSubquotient τ (piTensor fun a => (σ a).π) := by
  first | exact @GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac | exact GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac | (intros; apply GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwistParamAbove

theorem isFrobSS_wdRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] :
    IsFrobSS (wdRho P ι Bw h hj ρ) (wdN P ι ρ) (wdRep P ι Bw h hj ρ) := by
  obtain ⟨u, hN, hu, -, hc, hρ⟩ := wdRep_spec P ι Bw h hj ρ
  have := isFrobSS_of_unipotent u hu hc hρ
  rwa [hN] at this

theorem isModel_twist {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω Gw O} {a : ℕ} {L : FinExt l} {r : ↥Gw →* GL (Fin a) (Om l)} {c : ↥Gw →* GL (Fin 1) (Om l)} {s : ↥Gw →* GL (Fin a) ↥L.1} {m : ↥Gw →* GL (Fin 1) ↥L.1} (h₁ : IsModel Bw r L s) (h₂ : IsModel Bw c L m) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) := by
  refine ⟨h₁.1, ?_⟩
  rw [← h₁.2, ← h₂.2]
  ext g i j
  simp [mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
  simp [Matrix.map_apply]

end GlobalTheory.TwistParamAbove
end
end
