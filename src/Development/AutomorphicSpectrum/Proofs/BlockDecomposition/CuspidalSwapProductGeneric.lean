module

public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmConjugationProperties

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotients
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProduct
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraProd

theorem contra_contra_of_equiv {G V W U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {σ : Representation ℂ G V} {τ : Representation ℂ G W} {υ : Representation ℂ G U}
    (E₁ : (contra σ).Equiv τ) (E₂ : (contra τ).Equiv υ) (E₃ : υ.Equiv σ) :
    Nonempty ((contra (contra σ)).Equiv σ) :=
  ⟨((GlobalTheory.ContraRefl.contraEquiv E₁).symm.trans E₂).trans E₃⟩

theorem prodIrr_equiv_of_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : y = x)
    (hy : ∑ a, (y a).1 = N) (hx : ∑ a, (x a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr x hx)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem contra_contra_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  intro k _ _ _ _ hA h N x hd
  refine Exists.elim (contra_prodIrr hA x hd) fun hd₁ H₁ => H₁.elim fun E₁ => ?_
  refine Exists.elim (contra_prodIrr hA (fun a => Zc.dualCl (x a)) hd₁) fun hd₂ H₂ => H₂.elim fun E₂ => ?_
  refine (prodIrr_equiv_of_eq (funext fun a => GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA (x a)) hd₂ hd).elim fun E₃ => ?_
  exact contra_contra_of_equiv E₁ E₂ E₃

end GlobalTheory.CompanionTheory.ContraProd

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleContragredientOfInducedProductStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_contragredient_of_induced_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), Nonempty ((contra (contra (prodIrr x hd))).Equiv (prodIrr x hd)) := by
  first | exact @GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr | exact GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr | (intros; apply GlobalTheory.CompanionTheory.ContraProd.contra_contra_prodIrr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotientAltBis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContraIsSubquotient
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraSq

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := fun s => by
  have e : {g : G | S.toRepresentation g s = s} = {g : G | ρ g (s : V) = s} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact hρ s

theorem exists_smooth_extension {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (l₀ : Module.Dual ℂ S.toSubmodule) (hl₀ : ∀ h ∈ K, ∀ s, l₀ (S.toRepresentation h s) = l₀ s) :
    ∃ l : smoothPart ρ.dual, (∀ h ∈ K, contra ρ h l = l) ∧
      ∀ s : S.toSubmodule, (l : Module.Dual ℂ V) s = l₀ s := by
  have hmem : ∀ x : fixed S.toRepresentation K,
      (S.toSubmodule.subtype ∘ₗ (fixed S.toRepresentation K).subtype) x ∈ fixed ρ K := by
    intro x
    refine GlobalTheory.ContraRefl.mem_fix.2 fun h hh => ?_
    exact congrArg Subtype.val (GlobalTheory.ContraRefl.mem_fix.1 x.2 h hh)
  let ι : fixed S.toRepresentation K →ₗ[ℂ] fixed ρ K := LinearMap.codRestrict _ _ hmem
  have hι : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : ((x : S.toSubmodule) : V) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι hι
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hρ ho hc
    ((l₀ ∘ₗ (fixed S.toRepresentation K).subtype) ∘ₗ r)
  refine ⟨l, hl1, fun s => ?_⟩
  have key : (l : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype = l₀ := by
    refine GlobalTheory.ContraRefl.form_ext (isSmooth_sub hρ S) hc (fun h hh w => ?_) hl₀ fun w hw => ?_
    · have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (w : V))
        (hl1 h⁻¹ (inv_mem hh))
      simp only [contra_apply, inv_inv] at h1
      exact h1
    · have h2 := hl2 (ι ⟨w, hw⟩)
      have h3 : r (ι ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hr ⟨w, hw⟩
      simp only [LinearMap.comp_apply, h3] at h2
      exact h2
  exact LinearMap.congr_fun key s

def annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (S : Subrepresentation ρ)
    (f : S.toRepresentation.IntertwiningMap τ) : Subrepresentation (contra ρ) :=
  ⟨{ carrier := {l | ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0}
     add_mem' := fun {a b} ha hb s hs => by simp [ha s hs, hb s hs]
     zero_mem' := fun s _ => by simp
     smul_mem' := fun c a ha s hs => by simp [ha s hs] }, by
    intro h l hl s hs
    have h0 : f (S.toRepresentation h⁻¹ s) = 0 := by
      rw [f.isIntertwining, hs, map_zero]
    exact hl _ h0⟩

theorem mem_annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {l : smoothPart ρ.dual} :
    l ∈ (annih S f).toSubmodule ↔ ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0 :=
  Iff.rfl

def pull {ρ : Representation ℂ G V} (S : Subrepresentation ρ) (g : W →ₗ[ℂ] S.toSubmodule) :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ W :=
  (S.toSubmodule.subtype ∘ₗ g).dualMap

theorem pull_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {g : W →ₗ[ℂ] S.toSubmodule}
    (hg : ∀ w, f (g w) = w) {l : smoothPart ρ.dual} (hl : l ∈ (annih S f).toSubmodule)
    (s : S.toSubmodule) : pull S g (l : Module.Dual ℂ V) (f s) = (l : Module.Dual ℂ V) s := by
  have h0 : f (g (f s) - s) = 0 := by
    have : f (g (f s) - s) = f (g (f s)) - f s := map_sub f.toLinearMap _ _
    rw [this, hg, sub_self]
  have h1 := mem_annih.1 hl _ h0
  have h2 : (l : Module.Dual ℂ V) ((g (f s) : V) - s) = 0 := h1
  rw [map_sub, sub_eq_zero] at h2
  exact h2

def restrLin {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toSubmodule →ₗ[ℂ] smoothPart τ.dual where
  toFun l := ⟨pull S g ((l : smoothPart ρ.dual) : Module.Dual ℂ V),
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((isSmooth_contra ρ (l : smoothPart ρ.dual)).mem_nhds (by simp)) fun h hh => by
        have hh' : contra ρ h (l : smoothPart ρ.dual) = l := hh
        refine LinearMap.ext fun w => ?_
        obtain ⟨s, rfl⟩ := hf w
        show pull S g _ (τ h⁻¹ (f s)) = pull S g _ (f s)
        rw [← f.isIntertwining, pull_apply_map hg l.2, pull_apply_map hg l.2]
        have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (s : V)) hh'
        simp only [contra_apply] at h1
        exact h1)⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)

theorem restrLin_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (l : (annih S f).toSubmodule) (s : S.toSubmodule) :
    (restrLin hf hg l : Module.Dual ℂ W) (f s) = ((l : smoothPart ρ.dual) : Module.Dual ℂ V) s :=
  pull_apply_map hg l.2 s

theorem restrLin_comm {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (h : G) (l : (annih S f).toSubmodule) (w : W) :
    (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) w =
      (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ w) := by
  have e : ∀ s : S.toSubmodule,
      (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) (f s) =
        (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ (f s)) := fun s => by
    rw [← f.isIntertwining, restrLin_apply_map, restrLin_apply_map]
    rfl
  have := e (g w)
  rwa [hg w] at this

def restr {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toRepresentation.IntertwiningMap (contra τ) where
  toLinearMap := restrLin hf hg
  isIntertwining' h :=
    LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun w => restrLin_comm hf hg h l w)

theorem contra_isSubquotient : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) →
    ∀ (ρ : Representation ℂ G V) (τ : Representation ℂ G W),
      IsSmooth ρ → IsSubquotient τ ρ → IsSubquotient (contra τ) (contra ρ) := by
  intro G V W _ _ _ _ _ _ _ hG ρ τ hρ ⟨S, f, hf⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.toLinearMap
    (LinearMap.range_eq_top.2 hf)
  have hg' : ∀ w, f (g w) = w := fun w => LinearMap.congr_fun hg w
  refine ⟨annih S f, restr hf hg', fun m => ?_⟩
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra τ m).mem_nhds (by simp))
  have hfix : ∀ h ∈ K, ∀ s, (m : Module.Dual ℂ W) (f (S.toRepresentation h s)) =
      (m : Module.Dual ℂ W) (f s) := by
    intro h hh s
    have h1 : contra τ h⁻¹ m = m := hKs (inv_mem hh)
    have h2 := congrArg (fun x : smoothPart τ.dual => (x : Module.Dual ℂ W) (f s)) h1
    simp only [contra_apply, inv_inv] at h2
    rw [f.isIntertwining]
    exact h2
  obtain ⟨l, -, hl⟩ := exists_smooth_extension hρ S ho hc
    ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) hfix
  have hmem : l ∈ (annih S f).toSubmodule := fun s hs => by
    have h1 := hl s
    have h2 : ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) s = (m : Module.Dual ℂ W) (f s) := rfl
    rw [h1, h2, hs, map_zero]
  refine ⟨⟨l, hmem⟩, Subtype.ext (LinearMap.ext fun w => ?_)⟩
  obtain ⟨s, rfl⟩ := hf w
  show pull S g (l : Module.Dual ℂ V) (f s) = _
  rw [pull_apply_map hg' hmem]
  exact hl s

end GlobalTheory.CompanionTheory.ContraSq

end
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_contra_of_isSubquotient : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (ρ : Representation ℂ G V) (τ : Representation ℂ G W), IsSmooth ρ → IsSubquotient τ ρ → IsSubquotient (contra τ) (contra ρ) := by
  first | exact @GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient | exact GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.ContraSq.contra_isSubquotient <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotients
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenRev

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h


set_option maxHeartbeats 2000000 in
theorem isSubquotient_prodIrr_rev : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k →
    ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type}
      [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible →
      IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  intro k _ _ _ _ hA hGK h N x hd hd' W _ _ σ _ hi hsq

  obtain ⟨hdy, ⟨E1⟩⟩ := GlobalTheory.T.contragredient_product_irreducible hA (fun a => x (Fin.rev a)) hd'

  obtain ⟨hd2, ⟨E2⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK (fun a => Zc.dualCl (x (Fin.rev a))) hdy
  have ex : (fun a => Zc.dualCl ((fun a => Zc.dualCl (x (Fin.rev a))) (Fin.rev a))) = x := funext fun a => by
    simp only [Fin.rev_rev]
    exact GlobalTheory.T.dual_class_involutive hA (x a)
  obtain ⟨E3⟩ := GlobalTheory.CompanionTheory.LSocle.prodIrr_congr ex hd2 hd
  have h1 : IsSubquotient σ ((prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy).comp (Zc.Cos.thetaW k N)) :=
    isSubquotient_of_equiv hsq (E2.trans E3).symm
  have h2 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (prodIrr (fun a => Zc.dualCl (x (Fin.rev a))) hdy) := by
    have := GlobalTheory.CompanionTheory.WordProd.RowCell.isSubquotient_pullback (Zc.Cos.thetaW k N) h1
    rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW] at this
  have hs : IsSmooth (σ.comp (Zc.Cos.thetaW k N)) := h2.isSmooth (isSmooth_prodIrr _ _)
  have hi' : Representation.IsIrreducible (σ.comp (Zc.Cos.thetaW k N)) :=
    GlobalTheory.CosocleComp.isIrreducible_comp (GlobalTheory.CompanionTheory.LSocle.thetaW_surjective N) hi
  have h3 : IsSubquotient (σ.comp (Zc.Cos.thetaW k N)) (contra (prodIrr (fun a => x (Fin.rev a)) hd')) :=
    isSubquotient_of_equiv h2 E1.symm
  have h4 := GlobalTheory.T.isSubquotient_contra_of_isSubquotient (GlobalTheory.SqIntUnit.compactOpen_basis k N) _ _ (isSmooth_contra _) h3
  obtain ⟨E4⟩ := GlobalTheory.T.double_contragredient_of_induced_product hA (fun a => x (Fin.rev a)) hd'
  obtain ⟨E5⟩ := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK σ hs hi'
  exact isSubquotient_of_equiv_left E5.symm (isSubquotient_of_equiv h4 E4)

end GlobalTheory.CompanionTheory.GenRev
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReversedProductSameSubquotientsStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversed_product_same_subquotients : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Fin.rev a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Fin.rev a)) hd') := by
  first | exact @GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | exact GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev | (intros; apply GlobalTheory.CompanionTheory.GenRev.isSubquotient_prodIrr_rev <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenMulti

theorem multiProd_isSubquotient_of_forall (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M)
    (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i))
    (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i))
    (hs : ∀ i, IsSmooth (ρ' i)) (hq : ∀ i, IsSubquotient (ρ i) (ρ' i)) :
    IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') :=
  GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ (GlobalTheory.SmGL.stdBlocks N hM) _ _ _ _
    (GlobalTheory.SmGL.isSmooth_piTensor hs)
    (GlobalTheory.piTensor_isSubquotient_of_forall _ _ X Y ρ ρ' hq)

end GlobalTheory.CompanionTheory.GenMulti
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotientStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_preserves_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M) (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i)) (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i)), (∀ i, IsSmooth (ρ' i)) → (∀ i, IsSubquotient (ρ i) (ρ' i)) → IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') := by
  first | exact @GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | exact GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall | (intros; apply GlobalTheory.CompanionTheory.GenMulti.multiProd_isSubquotient_of_forall <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotient
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenExists

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_subQuot [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (A B : Subrepresentation ρ) : IsSmooth (subQuot A B) := by
  have stab : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (w : W),
      ∃ H : Subgroup G, ∀ g, g ∈ H ↔ σ g w = w := by
    intro W _ _ σ w
    refine ⟨{ carrier := {g | σ g w = w}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · intro a b ha hb
      replace ha : σ a w = w := ha
      replace hb : σ b w = w := hb
      show σ (a * b) w = w
      rw [map_mul, Module.End.mul_apply, hb, ha]
    · show σ 1 w = w
      rw [map_one, Module.End.one_apply]
    · intro a ha
      replace ha : σ a w = w := ha
      show σ a⁻¹ w = w
      conv_lhs => rw [← ha]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  intro v
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨H₁, hH₁⟩ := stab ρ (x : V)
  obtain ⟨H₂, hH₂⟩ := stab (subQuot A B) (Submodule.Quotient.mk x)
  have hle : H₁ ≤ H₂ := by
    intro g hg
    rw [hH₁] at hg
    rw [hH₂]
    show Submodule.Quotient.mk (A.toRepresentation g x) = Submodule.Quotient.mk x
    congr 1
    exact Subtype.ext hg
  have e₁ : (H₁ : Set G) = {g | ρ g x = x} := Set.ext hH₁
  have e₂ : (H₂ : Set G) = {g | (subQuot A B) g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x} :=
    Set.ext hH₂
  rw [← e₂]
  exact Subgroup.isOpen_mono hle (e₁ ▸ hρ x)

theorem nontrivial_twJacquet_subQuot {ρ : Representation ℂ G V} (N : Subgroup G) (χ : N →* ℂˣ)
    (A B : Subrepresentation ρ) (hB : B.toSubmodule ≤ twKer ρ N χ) (hA : ¬ A.toSubmodule ≤ twKer ρ N χ) :
    Nontrivial (TwJacquet (subQuot A B) N χ) := by
  obtain ⟨a, haA, hak⟩ := SetLike.not_le_iff_exists.mp hA
  let φ : A.toSubmodule →ₗ[ℂ] V ⧸ twKer ρ N χ := (twKer ρ N χ).mkQ ∘ₗ A.toSubmodule.subtype
  have hφ : Submodule.comap A.toSubmodule.subtype B.toSubmodule ≤ LinearMap.ker φ := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (x : V) = (0 : V ⧸ twKer ρ N χ)
    rw [Submodule.Quotient.mk_eq_zero]
    exact hB (Submodule.mem_comap.mp hx)
  let Ψ := (Submodule.comap A.toSubmodule.subtype B.toSubmodule).liftQ φ hφ
  have hker : twKer (subQuot A B) N χ ≤ LinearMap.ker Ψ := by
    apply Submodule.span_le.mpr
    rintro w ⟨n, v, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul]
    show Submodule.Quotient.mk (ρ n (x : V)) - (χ n : ℂ) • Submodule.Quotient.mk (x : V) =
      (0 : V ⧸ twKer ρ N χ)
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨n, (x : V), rfl⟩
  refine ⟨⟨(Submodule.Quotient.mk (Submodule.Quotient.mk ⟨a, haA⟩ :
      A.toSubmodule ⧸ Submodule.comap A.toSubmodule.subtype B.toSubmodule) :
      _ ⧸ twKer (subQuot A B) N χ), 0, ?_⟩⟩
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  have h' := hker h
  rw [LinearMap.mem_ker] at h'
  have h'' : Submodule.Quotient.mk a = (0 : V ⧸ twKer ρ N χ) := h'
  exact hak ((Submodule.Quotient.mk_eq_zero _).mp h'')

end General

theorem exists_generic_subQuot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ →
    IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧
      IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ hfl hgen
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI := hNA.1
  haveI := hNA.2
  have hle : ∀ S T : Subrepresentation ρ, S.asSubmodule ≤ T.asSubmodule ↔ S ≤ T := fun S T => Iff.rfl
  have hsm : StrictMono (fun S : Subrepresentation ρ => S.asSubmodule) := fun S T h =>
    lt_of_le_of_ne ((hle S T).mpr h.le)
      (fun he => h.ne (le_antisymm ((hle S T).mp he.le) ((hle T S).mp he.ge)))
  have wfl : WellFounded (fun S T : Subrepresentation ρ => S < T) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_lt)
  have wfg : WellFounded (fun S T : Subrepresentation ρ => T < S) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_gt)
  have hgen' : Nontrivial (V ⧸ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := hgen
  let T0 : Subrepresentation ρ := ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
  have htop : ¬ T0.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    intro h
    obtain ⟨x, y, hxy⟩ := hgen'.exists_pair_ne
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hxy
    rw [Submodule.Quotient.eq]
    exact h Submodule.mem_top
  obtain ⟨A, hAP, hAmin⟩ := wfl.has_min {A | ¬ A.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N)} ⟨T0, htop⟩
  let Z : Subrepresentation ρ := ⟨⊥, fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]⟩
  have hZk : Z.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := bot_le
  have hZA : Z < A := by
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).mp hx
      rw [hx0]
      exact A.toSubmodule.zero_mem
    · intro h
      rw [← h] at hAP
      exact hAP hZk
  obtain ⟨B, hBA, hBmax⟩ := wfg.has_min {B | B < A} ⟨Z, hZA⟩
  have hcov : B ⋖ A := ⟨hBA, fun C hBC hCA => hBmax C hCA hBC⟩
  have hBk : B.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    by_contra h
    exact hAmin B h hBA
  exact ⟨A, B, hBA.le, GlobalTheory.SmGL.isIrreducible_subQuot hcov, GlobalTheory.CompanionTheory.GenExists.isSmooth_subQuot hρ A B,
    GlobalTheory.CompanionTheory.GenExists.nontrivial_twJacquet_subQuot _ _ A B hBk hAP⟩

end GlobalTheory.CompanionTheory.GenExists

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericHasGenericIrreducibleSubquotientStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_has_generic_irreducible_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ → IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧ IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  first | exact @GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot | exact GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot | (intros; apply GlobalTheory.CompanionTheory.GenExists.exists_generic_subQuot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGeneric
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GenSwap

open GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSubquotient_of_equiv {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {ρ' : Representation ℂ G U}
    (h : IsSubquotient σ ρ) (E : ρ.Equiv ρ') : IsSubquotient σ ρ' :=
  h.trans (IsSubquotient.of_surjective E.symm.toIntertwiningMap E.symm.surjective)

theorem isSubquotient_of_equiv_left {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [AddCommGroup U] [Module ℂ U] {σ : Representation ℂ G W} {τ : Representation ℂ G U}
    {ρ : Representation ℂ G V} (E : σ.Equiv τ) (h : IsSubquotient σ ρ) : IsSubquotient τ ρ :=
  (IsSubquotient.of_surjective E.toIntertwiningMap E.surjective).trans h

theorem isGenericFor_prodIrr (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) (hC : GlobalTheory.BZSeg.CuspGeneric k)
    {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hc : ∀ a, (x a).IsCusp) (hd : ∑ a, (x a).1 = N) : IsGenericFor ψ (prodIrr x hd) := by
  rw [← isGeneric_iff_isGenericFor hψ h1]
  exact (GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity k hW h N (fun a => (x a).1) hd (fun a => (x a).2.rep.V)
    (fun a => (x a).rep) (fun a => (x a).2.rep.smooth)).2 fun a =>
      hC _ _ _ (hc a).1 (x a).2.rep.smooth (x a).2.rep.irr (hc a).2

theorem isSubquotient_of_generic_common {N : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) {U V V' W : Type}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (T : Representation ℂ (GL (Fin N) k) U) (P : Representation ℂ (GL (Fin N) k) V)
    (P' : Representation ℂ (GL (Fin N) k) V') (hT : IsSubquotient T P) (hT' : IsSubquotient T P')
    (hTg : IsGenericFor ψ T) (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTs : IsSmooth T := hT.isSmooth hP
  have hTf : GlobalTheory.SmGL.HasFiniteLength T := GlobalTheory.CompanionTheory.IrrSub.hasFiniteLength_of_isSubquotient hT hfl
  obtain ⟨A, B, -, hi', -, hg'⟩ := GlobalTheory.T.generic_has_generic_irreducible_subquotient k ψ hψ N T hTs hTf hTg
  have s₁ := GlobalTheory.ParIndExact.isSubquotient_subQuot A B
  obtain ⟨e⟩ := GlobalTheory.T.whittaker_rank_extension_bound k ψ hψ N P σ (subQuot A B) hP hr hi hi' hsq (s₁.trans hT) hgσ hg'
  exact isSubquotient_of_equiv_left e.symm (s₁.trans hT')

theorem isSubquotient_of_common {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y Z : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    [∀ a, AddCommGroup (Z a)] [∀ a, Module ℂ (Z a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Z a)) (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a))
    (hτ : ∀ a, IsSmooth (τ a)) (hq : ∀ a, IsSubquotient (τ a) (π a)) (hq' : ∀ a, IsSubquotient (τ a) (π' a))
    (hg : ∀ a, IsGenericFor ψ (τ a)) {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have hTg : IsGenericFor ψ (multiProd (stdBlocks d hN) τ) := by
    obtain ⟨H⟩ := hW ψ hψ h1 s N d hN Z τ hτ
    have : Nontrivial (⨂[ℂ] a, TwJacquet (τ a) (unipB k (Fin (d a))) (whitChar ψ (d a))) :=
      (GlobalTheory.CompanionTheory.Leib.nontrivial_piTensorProduct_iff _).2 hg
    exact H.toEquiv.nontrivial
  exact isSubquotient_of_generic_common hψ _ P P'
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z X τ π hπ hq) E)
    (isSubquotient_of_equiv (GlobalTheory.T.product_preserves_subquotient k d N hN Z Y τ π' hπ' hq') E') hTg hP hfl hr σ hi hgσ hsq

theorem isSubquotient_of_positions {s N : ℕ} (hW : GlobalTheory.BZMir.Leib.WhitHeredity k) {ψ : AddChar k Circle}
    (hψ : Continuous ψ) (h1 : ψ ≠ 1) (d : Fin s → ℕ) (hN : ∑ a, d a = N) {X Y : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a))
    (hπ : ∀ a, IsSmooth (π a)) (hπ' : ∀ a, IsSmooth (π' a)) (hg : ∀ a, IsGenericFor ψ (π a))
    (hf : ∀ a, GlobalTheory.SmGL.HasFiniteLength (π a))
    (hsw : ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (π a) → IsSubquotient g (π' a))
    {V V' W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GL (Fin N) k) V) (P' : Representation ℂ (GL (Fin N) k) V')
    (E : (multiProd (stdBlocks d hN) π).Equiv P) (E' : (multiProd (stdBlocks d hN) π').Equiv P')
    (hP : IsSmooth P) (hfl : GlobalTheory.SmGL.HasFiniteLength P)
    (hr : Module.rank ℂ (TwJacquet P (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible) (hgσ : IsGenericFor ψ σ)
    (hsq : IsSubquotient σ P) : IsSubquotient σ P' := by
  have ex := fun a => GlobalTheory.T.generic_has_generic_irreducible_subquotient k ψ hψ (d a) (π a) (hπ a) (hf a) (hg a)
  choose A B _ hirr hsm hgen using ex
  have hq : ∀ a, IsSubquotient (subQuot (A a) (B a)) (π a) := fun a => GlobalTheory.ParIndExact.isSubquotient_subQuot _ _
  exact isSubquotient_of_common hW hψ h1 d hN π π' (fun a => subQuot (A a) (B a)) hπ hπ' hsm hq
    (fun a => hsw a _ _ (hsm a) (hirr a) (hq a)) hgen P P' E E' hP hfl hr σ hi hgσ hsq

theorem fac_rev {h j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k)) (i : Fin 2) :
    (fac hj x 1 : Fin 2 → IrrGL (k := k)) (Fin.rev i) = (fac' hj x 1 : Fin 2 → IrrGL (k := k)) i := by
  rw [fac_one hj x, fac'_one hj x]
  fin_cases i <;> rfl

theorem nonempty_equiv_of_eq {n M : ℕ} {u v : Fin n → IrrGL (k := k)} (e : u = v) (h₁ : ∑ a, (u a).1 = M)
    (h₂ : ∑ a, (v a).1 = M) : Nonempty ((prodIrr u h₁).Equiv (prodIrr v h₂)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩


set_option maxHeartbeats 1000000 in
theorem position_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) {h j : ℕ} (hj : j + 1 < h)
    (x : Fin h → IrrGL (k := k)) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) :
    ∀ a (W : Type) [AddCommGroup W] [Module ℂ W] (g : Representation ℂ (GL (Fin (d a)) k) W),
      IsSmooth g → g.IsIrreducible → IsSubquotient g (prodIrr (fac hj x a) (s₁ a)) →
      IsSubquotient g (prodIrr (fac' hj x a) (s₂ a)) := by
  refine fin_three_forall ?_ ?_ ?_
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_zero hj x).symm (s₁ 0) (s₂ 0)
    exact isSubquotient_of_equiv hq E
  · intro W _ _ g hgs hgi hq
    have hd2 : ∑ a, (fac hj x 1 (Fin.rev a)).1 = d 1 :=
      (Equiv.sum_comp Fin.revPerm fun b => (fac hj x 1 b).1).trans (s₁ 1)
    obtain ⟨E⟩ := prodIrr_congr rfl (fun a => fac hj x 1 (Fin.rev a)) (fac' hj x 1) (fun i => fac_rev hj x i) hd2 (s₂ 1)
    exact isSubquotient_of_equiv (GlobalTheory.T.reversed_product_same_subquotients hA hGK (fac hj x 1) (s₁ 1) hd2 g hgs hgi hq) E
  · intro W _ _ g _ _ hq
    obtain ⟨E⟩ := nonempty_equiv_of_eq (fac'_two hj x).symm (s₁ 2) (s₂ 2)
    exact isSubquotient_of_equiv hq E


set_option maxHeartbeats 1000000 in
theorem core (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : Zc.Cos.GKLocal k) (hW : GlobalTheory.BZMir.Leib.WhitHeredity k)
    (hR : GlobalTheory.BZSeg.WhitRankIrr k) (hC : GlobalTheory.BZSeg.CuspGeneric k) (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) {h N j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL (k := k)) (hc : ∀ a, (x a).IsCusp) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) (hN : ∑ a, d a = N)
    (hd : ∑ a, (x a).1 = N) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (hi : σ.IsIrreducible)
    (hg : IsGenericFor ψ σ) (hsq : IsSubquotient σ (prodIrr x hd)) :
    IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  have hJ : j < h := by omega
  have hkey : ∀ c, fac' hj x (ofLex (order hj c)).1 (ofLex (order hj c)).2 =
      x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ c) := fun c =>
    congrArg (fun y => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ y)) (place_order hj c)
  obtain ⟨p⟩ := flatten (grp h j) (fac hj x) d s₁ hN (order hj) x (fun c => congrArg x (place_order hj c)) hd
  obtain ⟨q⟩ := flatten (grp h j) (fac' hj x) d s₂ hN (order hj)
    (fun a => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ a)) hkey hd'
  exact isSubquotient_of_positions hW hψ h1 d hN (fun a => prodIrr (fac hj x a) (s₁ a))
    (fun a => prodIrr (fac' hj x a) (s₂ a)) (fun _ => isSmooth_prodIrr _ _) (fun _ => isSmooth_prodIrr _ _)
    (fun a => isGenericFor_prodIrr hW hC hψ h1 _ (fun _ => hc _) _) (fun _ => GlobalTheory.T.product_irreducible_finite_length hA _ _)
    (position_swap hA hGK hj x d s₁ s₂) _ _ p q
    (isSmooth_prodIrr _ _) (GlobalTheory.T.product_irreducible_finite_length hA _ _) (GlobalTheory.T.whittaker_rank_product_le_one k hW hR ψ hψ h1 h N x hd) σ hi hg hsq

theorem isSubquotient_prodIrr_swap : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  intro k _ _ _ _ hA hGK hW hR hC ψ hψ h1 h N x hc hd j hj hd' W _ _ σ _ hi hg hsq
  have t : ∑ b : Fin 2, ((fac' hj x 1 : Fin 2 → IrrGL (k := k)) b).1 = ∑ b : Fin 2, ((fac hj x 1 : Fin 2 → IrrGL (k := k)) b).1 := by
    rw [fac_one hj x, fac'_one hj x]
    simp [Fin.sum_univ_two, add_comm]
  have s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = ∑ b, (fac hj x a b).1 :=
    fin_three_forall (by rw [fac'_zero hj x]) t (by rw [fac'_two hj x])
  exact core hA hGK hW hR hC ψ hψ h1 hj x hc (fun a => ∑ b, (fac hj x a b).1) (fun _ => rfl) s₂
    ((sum_place hj fun c => (x c).1).trans hd) hd hd' σ hi hg hsq

end GlobalTheory.CompanionTheory.GenSwap

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalSwapProductGenericStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_swap_product_generic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k → GlobalTheory.BZMir.Leib.WhitHeredity k → GlobalTheory.BZSeg.WhitRankIrr k → GlobalTheory.BZSeg.CuspGeneric k → ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)), (∀ a, (x a).IsCusp) → ∀ (hd : ∑ a, (x a).1 = N) (j : ℕ) (hj : j + 1 < h) (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W), IsSmooth σ → σ.IsIrreducible → IsGenericFor ψ σ → IsSubquotient σ (prodIrr x hd) → IsSubquotient σ (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd') := by
  first | exact @GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap | exact GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap | (intros; apply GlobalTheory.CompanionTheory.GenSwap.isSubquotient_prodIrr_swap <;> assumption)
end
