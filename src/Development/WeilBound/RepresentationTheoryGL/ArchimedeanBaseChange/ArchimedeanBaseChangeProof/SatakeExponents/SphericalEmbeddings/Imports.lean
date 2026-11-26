module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2LinkedPair
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.NoLinkRev

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGenericOfInjective
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CuspStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def prod₂MapR {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (π₁ : Representation ℂ (GL (Fin r) k) U)
    {π₂ : Representation ℂ (GL (Fin t) k) X} {π₂' : Representation ℂ (GL (Fin t) k) Y}
    (f : π₂.IntertwiningMap π₂') : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁ π₂') :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁ π₂')
    ⟨TensorProduct.map LinearMap.id f.toLinearMap, fun g => by
      ext u x
      exact congrArg (fun b => π₁ g.1 u ⊗ₜ[ℂ] b) (f.isIntertwining _ _ g.2 x)⟩ _)

def prod₂MapL {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {π₁ : Representation ℂ (GL (Fin r) k) X}
    {π₁' : Representation ℂ (GL (Fin r) k) Y} (f : π₁.IntertwiningMap π₁')
    (π₂ : Representation ℂ (GL (Fin t) k) U) : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁' π₂) :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁' π₂)
    ⟨TensorProduct.map f.toLinearMap LinearMap.id, fun g => by
      ext x u
      exact congrArg (fun b => b ⊗ₜ[ℂ] π₂ g.2 u) (f.isIntertwining _ _ g.1 x)⟩ _)

end GlobalTheory.CompanionTheory.CuspStd
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GL2SphericalSwap
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseBub
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.PseBub

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse PositivityTheory.Rg.BcB.N3.PseSat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comp_injective {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] {π : Representation ℂ (GL (Fin n) k) V} {ρ : Representation ℂ (GL (Fin n) k) W}
    {τ : Representation ℂ (GL (Fin n) k) U} (hi : π.IsIrreducible) (hsph : IsSpherical π)
    (f : π.IntertwiningMap ρ) (hf : Function.Injective f) (T : ρ.IntertwiningMap τ) (hT : KInj k T) :
    Function.Injective (T.comp f) := by
  classical
  set g := T.comp f with hg
  have hg' : ∀ v, g v = T (f v) := fun v => Representation.IntertwiningMap.comp_apply _ _ _ T f v
  rcases hi.eq_bot_or_eq_top (Representation.IntertwiningMap.ker _ _ g) with h | h
  · intro x y hxy
    have hx : x - y ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [Representation.IntertwiningMap.mem_ker, map_sub, hxy, sub_self]
    rw [h] at hx
    have hx' : x - y ∈ (⊥ : Submodule ℂ V) := hx
    exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hx')
  · exfalso
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hsph
    have hfv : f v ∈ fixed ρ (KO k (Fin n)) := by
      intro h'
      have := hv h'
      rw [← Representation.IntertwiningMap.isIntertwining, this]
      simp
    have hker : v ∈ Representation.IntertwiningMap.ker _ _ g := by
      rw [h]
      exact (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ V))
    rw [Representation.IntertwiningMap.mem_ker, hg'] at hker
    have := hT (f v) hfv hker
    exact hv0 (hf (by rw [this, map_zero]))

def wt {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := ∑ i : Fin n, (i : ℕ) * (σ i : ℕ)

theorem wt_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : wt σ ≤ n * (n * n) := by
  unfold wt
  calc ∑ i : Fin n, (i : ℕ) * (σ i : ℕ) ≤ ∑ _i : Fin n, n * n :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul i.2.le (σ i).2.le
    _ = n * (n * n) := by simp

theorem wt_swap {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) (hij : (j : ℕ) = i + 1) (hd : σ j < σ i) :
    wt σ < wt (σ * Equiv.swap i j) := by
  classical
  have hne : i ≠ j := by
    intro h
    subst h
    omega
  unfold wt
  have key : ∀ τ : Equiv.Perm (Fin n), ∑ k : Fin n, (k : ℕ) * (τ k : ℕ) =
      (i : ℕ) * (τ i : ℕ) + ((j : ℕ) * (τ j : ℕ) +
        ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (τ k : ℕ)) := by
    intro τ
    rw [Finset.add_sum_erase (Finset.univ.erase i) (fun k : Fin n => (k : ℕ) * (τ k : ℕ))
      (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩)]
    rw [Finset.add_sum_erase Finset.univ (fun k : Fin n => (k : ℕ) * (τ k : ℕ)) (Finset.mem_univ i)]
  rw [key σ, key (σ * Equiv.swap i j)]
  have hrest : ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * ((σ * Equiv.swap i j) k : ℕ) =
      ∑ k ∈ (Finset.univ.erase i).erase j, (k : ℕ) * (σ k : ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj := Finset.ne_of_mem_erase hk
    have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrest, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hd' : (σ j : ℕ) < σ i := hd
  rw [hij]
  nlinarith

theorem exists_descent {n : ℕ} (σ : Equiv.Perm (Fin n)) (h1 : σ ≠ 1) :
    ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ σ j < σ i := by
  by_contra hne
  push_neg at hne
  apply h1
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    have hs : StrictMono (σ : Fin (m + 1) → Fin (m + 1)) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro i
      have hle := hne i.castSucc i.succ (by simp)
      exact lt_of_le_of_ne hle (fun h => (Fin.castSucc_lt_succ (i := i)).ne (σ.injective h))
    ext x
    have hx := congrFun hs.eq_id x
    simp [hx]

theorem bubble : Bubble k := by
  intro hSL hG2 n ξ hξ σ₀ V _ _ π hi hsph hf₀
  have key : ∀ m : ℕ, ∀ σ : Equiv.Perm (Fin n), n * (n * n) - wt σ = m →
      (∃ f : π.IntertwiningMap (iP (ξ ∘ ⇑σ)), Function.Injective ⇑f) →
        ∃ f : π.IntertwiningMap (iP ξ), Function.Injective ⇑f := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro σ hm hσ
      by_cases h1 : σ = 1
      · subst h1
        exact hσ
      · obtain ⟨i, j, hij, hd⟩ := exists_descent σ h1
        obtain ⟨f, hf⟩ := hσ
        have hle : ‖(((ξ ∘ ⇑σ) i : ℂˣ) : ℂ)‖ ≤ ‖(((ξ ∘ ⇑σ) j : ℂˣ) : ℂ)‖ := hξ _ _ hd.le
        obtain ⟨T0, hT0⟩ := hG2 _ _ hle
        obtain ⟨T, hT⟩ := hSL n (ξ ∘ ⇑σ) i j hij ⟨T0, hT0⟩
        have hinj := comp_injective hi hsph f hf T hT
        have hw := wt_swap σ i j hij hd
        have hwle := wt_le (σ * Equiv.swap i j)
        have hlt : n * (n * n) - wt (σ * Equiv.swap i j) < m := by
          generalize n * (n * n) = N at *
          omega
        exact ih _ hlt (σ * Equiv.swap i j) rfl ⟨T.comp f, hinj⟩
  exact key _ σ₀ rfl hf₀

end PositivityTheory.Rg.BcB.N3.PseBub
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseAsm
namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3 GlobalTheory.SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sphEmb_of (hG : GL2SphericalSwap k) (hS : StageLift k) (hE : ExpSph k) (hP : SatPerm k) (hB : Bubble k) : SphEmb k := by
  intro n ξ hm V _ _ π hs hi hsph hq
  obtain ⟨η, f, hf⟩ := hE n V π hs hi hsph
  obtain ⟨σ, rfl⟩ := hP n ξ η V π hs hi hsph hq ⟨f, hf⟩
  exact hB hS hG n ξ hm σ V π hi hsph ⟨f, PositivityTheory.Rg.BcB.N3.PseSat.injective_of_ne_zero hi f hf⟩

end PositivityTheory.Rg.BcB.N3.Pse
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseExp
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.PseExp

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_map_of_eigenform {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π)
    (μ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t x, l (jacB π t x) = (μ t : ℂ) * l x) :
    ∃ f : π.IntertwiningMap (indB (ofChar μ)), f ≠ 0 := by
  let ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ :=
    (ofChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨l, fun g => LinearMap.ext fun x => by
      obtain ⟨t, rfl⟩ := (leviTorus k (Fin n)).surjective g
      have e : (ρ (leviTorus k (Fin n) t)) (l x) = (μ t : ℂ) * l x := by
        show ofChar μ ((leviTorus k (Fin n)).symm (leviTorus k (Fin n) t)) _ = _
        rw [MulEquiv.symm_apply_apply, ofChar_apply]
      exact (hl t x).trans e.symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  refine ⟨f, fun h0 => hl0 (LinearMap.ext fun x => ?_)⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : φ (Submodule.Quotient.mk v) = (f v).1.1 1 := by rw [← hf]; rfl
  have h2 : l (Submodule.Quotient.mk v) = φ (Submodule.Quotient.mk v) := rfl
  rw [h2, h1, h0]
  rfl

theorem expSph : ExpSph k := by
  intro n V _ _ π hs hi hsph
  have hadm : IsAdmissible π := (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi
  have hI : fixed π (iwahori k (Fin n)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsph
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨χ, l, hl0, hl, hχ⟩ := GlobalTheory.SatakeExists.exists_eigenform_jacBU hadm hI
  let δ : (Fin n → kˣ) →* ℂˣ :=
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_eq_torusChar (χ * δ⁻¹) fun t ht => by
    have : δ t = 1 := GlobalTheory.SmGL.UnramFixed.deltaHalf_torusO k ht
    simp [hχ t ht, this]
  obtain ⟨f, hf⟩ := exists_map_of_eigenform hadm.1 (χ * δ⁻¹) l hl0 fun t x => by
    rw [GlobalTheory.SmGL.UnramFixed.jacB_apply, map_smul, hl, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul,
      MonoidHom.inv_apply]
    ring
  refine ⟨α, ?_⟩
  show ∃ f : π.IntertwiningMap (indB (ofChar (torusChar fun i => unrChar k (α i)))), f ≠ 0
  rw [hα]
  exact ⟨f, hf⟩

end PositivityTheory.Rg.BcB.N3.PseExp
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStage
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageC
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageB
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseStageA
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Lin

variable {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

theorem coordL_lTensor {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℂ U) (g : X →ₗ[ℂ] Y) (v : U ⊗[ℂ] X) :
    TensorProduct.equivFinsuppOfBasisLeft b (LinearMap.lTensor U g v) =
      Finsupp.mapRange g (map_zero g) (TensorProduct.equivFinsuppOfBasisLeft b v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul u x =>
    ext i
    simp
  | add v w hv hw =>
    rw [map_add (f := _), map_add (f := _), hv, hw, map_add (f := _), Finsupp.mapRange_add (map_add g)]

theorem coordR_rTensor {ι : Type} [DecidableEq ι] (b : Module.Basis ι ℂ U) (g : X →ₗ[ℂ] Y) (v : X ⊗[ℂ] U) :
    TensorProduct.equivFinsuppOfBasisRight b (LinearMap.rTensor U g v) =
      Finsupp.mapRange g (map_zero g) (TensorProduct.equivFinsuppOfBasisRight b v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x u =>
    ext i
    simp
  | add v w hv hw =>
    rw [map_add (f := _), map_add (f := _), hv, hw, map_add (f := _), Finsupp.mapRange_add (map_add g)]

theorem eq_zero_of_lTensor {G : Type} [Group G] (π : G →* (X →ₗ[ℂ] X)) (S : Set G) (f : X →ₗ[ℂ] Y)
    (hf : ∀ x, (∀ h ∈ S, π h x = x) → f x = 0 → x = 0) (v : U ⊗[ℂ] X)
    (hv : ∀ h ∈ S, LinearMap.lTensor U (π h) v = v) (h0 : LinearMap.lTensor U f v = 0) : v = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ U
  have key : TensorProduct.equivFinsuppOfBasisLeft b v = 0 := by
    ext i
    have h1 : ∀ h ∈ S, π h (TensorProduct.equivFinsuppOfBasisLeft b v i) =
        TensorProduct.equivFinsuppOfBasisLeft b v i := by
      intro h hh
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft b w i) (hv h hh)
      simpa [coordL_lTensor] using this
    have h2 : f (TensorProduct.equivFinsuppOfBasisLeft b v i) = 0 := by
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisLeft b w i) h0
      simpa [coordL_lTensor] using this
    simpa using hf _ h1 h2
  exact (LinearEquiv.map_eq_zero_iff _).mp key

theorem eq_zero_of_rTensor {G : Type} [Group G] (π : G →* (X →ₗ[ℂ] X)) (S : Set G) (f : X →ₗ[ℂ] Y)
    (hf : ∀ x, (∀ h ∈ S, π h x = x) → f x = 0 → x = 0) (v : X ⊗[ℂ] U)
    (hv : ∀ h ∈ S, LinearMap.rTensor U (π h) v = v) (h0 : LinearMap.rTensor U f v = 0) : v = 0 := by
  classical
  let b := Module.Free.chooseBasis ℂ U
  have key : TensorProduct.equivFinsuppOfBasisRight b v = 0 := by
    ext i
    have h1 : ∀ h ∈ S, π h (TensorProduct.equivFinsuppOfBasisRight b v i) =
        TensorProduct.equivFinsuppOfBasisRight b v i := by
      intro h hh
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisRight b w i) (hv h hh)
      simpa [coordR_rTensor] using this
    have h2 : f (TensorProduct.equivFinsuppOfBasisRight b v i) = 0 := by
      have := congrArg (fun w => TensorProduct.equivFinsuppOfBasisRight b w i) h0
      simpa [coordR_rTensor] using this
    simpa using hf _ h1 h2
  exact (LinearEquiv.map_eq_zero_iff _).mp key

end Lin

variable {n : ℕ} {V W Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]

theorem kinj_comp {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W}
    {τ : Representation ℂ (GL (Fin n) k) Z} (S : π.IntertwiningMap σ) (T : σ.IntertwiningMap τ) (hS : KInj k S)
    (hT : KInj k T) : KInj k (T.comp S) := by
  intro v hv h0
  have hv' : ∀ h : ↥(KO k (Fin n)), π h v = ((1 : ↥(KO k (Fin n)) →* ℂˣ) h : ℂ) • v := hv
  have hSv : S v ∈ GlobalTheory.PRep.fixed σ (KO k (Fin n)) := by
    show ∀ h : ↥(KO k (Fin n)), σ h (S v) = ((1 : ↥(KO k (Fin n)) →* ℂˣ) h : ℂ) • S v
    intro h
    rw [← S.isIntertwining, hv' h, map_smul]
  exact hS v hv (hT (S v) hSv h0)

theorem kinj_equiv {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (E : π.Equiv σ) :
    KInj k E.toIntertwiningMap := by
  intro v _ h
  simpa using h

end PositivityTheory.Rg.BcB.N3.PseStage

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

theorem kinj_prod₂MapR (π₁ : Representation ℂ (GL (Fin r) k) U) {π₂ : Representation ℂ (GL (Fin t) k) X}
    {π₂' : Representation ℂ (GL (Fin t) k) Y} (f : π₂.IntertwiningMap π₂') (hf : KInj k f) :
    KInj k (GlobalTheory.CompanionTheory.CuspStd.prod₂MapR π₁ f) := by
  intro F hF h0
  have hind := F.1.2
  simp only [indSpace, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hind
  have hF' : ∀ w : ↥(KO k (Fin (r + t))),
      prod₂ π₁ π₂ w F = ((1 : ↥(KO k (Fin (r + t))) →* ℂˣ) w : ℂ) • F := hF
  have hFix : ∀ w ∈ KO k (Fin (r + t)), ∀ x, F.1.1 (x * w) = F.1.1 x := by
    intro w hw x
    have e1 : (prod₂ π₁ π₂ w F).1.1 x = F.1.1 (x * w) := rfl
    rw [← e1, hF' ⟨w, hw⟩]
    simp only [MonoidHom.one_apply, Units.val_one]
    rw [one_smul]
  have h0' : ∀ x, LinearMap.lTensor U f.toLinearMap (F.1.1 x) = 0 := by
    intro x
    have e0 : (GlobalTheory.CompanionTheory.CuspStd.prod₂MapR π₁ f F).1.1 x =
        TensorProduct.map LinearMap.id f.toLinearMap (F.1.1 x) := rfl
    rw [LinearMap.lTensor, ← e0, h0]
    rfl
  have hf' : ∀ x, (∀ h ∈ (KO k (Fin t) : Set (GL (Fin t) k)), π₂ h x = x) →
      f.toLinearMap x = 0 → x = 0 := by
    intro x hx hfx
    refine hf x ?_ hfx
    show ∀ h : ↥(KO k (Fin t)), π₂ h x = ((1 : ↥(KO k (Fin t)) →* ℂˣ) h : ℂ) • x
    intro h
    simpa using hx h h.2
  have hv : ∀ h ∈ (KO k (Fin t) : Set (GL (Fin t) k)),
      LinearMap.lTensor U (π₂ h) (F.1.1 1) = F.1.1 1 := by
    intro h hh
    set ℓ : Levi k (Two (Fin r) (Fin t)) := leviTwo k (Fin r) (Fin t) (1, h) with hℓ
    have hℓK : ∀ b, ℓ b ∈ KO k (Two (Fin r) (Fin t) b) := by
      intro b
      cases b
      · exact one_mem _
      · exact hh
    have hEmb : leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ ∈ KO k (Fin (r + t)) := by
      have hfacts := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k Bool (Fin (r + t))
        (Two (Fin r) (Fin t)) (two (stdSum (rfl : r + t = r + t)))).1 ℓ 1 (one_mem _)
      simpa using hfacts.mpr ⟨hℓK, one_mem _⟩
    have hDelta : deltaHalf k (Two (Fin r) (Fin t)) ℓ = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one (fun a _ => ?_)
      
      apply isUnram_absPow k _ _
      obtain ⟨g, hg⟩ := hℓK a
      rw [← hg]
      have heq : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
          algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
        ((algebraMap 𝒪[k] k).map_det _).symm
      exact heq.symm ▸ (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
    have h2 : F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = F.1.1 1 := by
      simpa using hFix _ (hEmb) 1
    have h1 := hind ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ, leviEmb_mem_parab k _ ℓ⟩ 1
    rw [mul_one] at h1
    change F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = _ at h1
    rw [h2] at h1
    have hE : extTensor π₁ π₂ (1, h) = LinearMap.lTensor U (π₂ h) := by
      apply TensorProduct.ext'
      intro u x
      simp [extTensor_tmul]
    clear hind hF' hFix h0' hf' hF h0 h2
    conv_rhs => rw [h1]
    rw [MonoidHom.comp_apply, twist_apply, leviProj_leviEmb, hDelta,
      MonoidHom.comp_apply, hℓ]
    simp [hE]
  have h1F : F.1.1 1 = 0 :=
    eq_zero_of_lTensor π₂ (KO k (Fin t) : Set (GL (Fin t) k)) f.toLinearMap hf' (F.1.1 1) hv (h0' 1)
  have hall : ∀ x, F.1.1 x = 0 := by
    intro x
    obtain ⟨p, c, hc, rfl⟩ := GlobalTheory.SmGL.Stages.iwasawa_two (k := k) (stdSum (rfl : r + t = r + t)) x
    rw [hFix c hc, ← mul_one (p : GL (Fin (r + t)) k), hind p 1, h1F, map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [hall x]
  rfl

theorem kinj_prod₂MapL {π₁ : Representation ℂ (GL (Fin r) k) X} {π₁' : Representation ℂ (GL (Fin r) k) Y}
    (f : π₁.IntertwiningMap π₁') (hf : KInj k f) (π₂ : Representation ℂ (GL (Fin t) k) U) :
    KInj k (GlobalTheory.CompanionTheory.CuspStd.prod₂MapL f π₂) := by
  intro F hF h0
  have hind := F.1.2
  simp only [indSpace, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at hind
  have hF' : ∀ w : ↥(KO k (Fin (r + t))),
      prod₂ π₁ π₂ w F = ((1 : ↥(KO k (Fin (r + t))) →* ℂˣ) w : ℂ) • F := hF
  have hFix : ∀ w ∈ KO k (Fin (r + t)), ∀ x, F.1.1 (x * w) = F.1.1 x := by
    intro w hw x
    have e1 : (prod₂ π₁ π₂ w F).1.1 x = F.1.1 (x * w) := rfl
    rw [← e1, hF' ⟨w, hw⟩]
    simp only [MonoidHom.one_apply, Units.val_one]
    rw [one_smul]
  have h0' : ∀ x, LinearMap.rTensor U f.toLinearMap (F.1.1 x) = 0 := by
    intro x
    have e0 : (GlobalTheory.CompanionTheory.CuspStd.prod₂MapL f π₂ F).1.1 x =
        TensorProduct.map f.toLinearMap LinearMap.id (F.1.1 x) := rfl
    rw [LinearMap.rTensor, ← e0, h0]
    rfl
  have hf' : ∀ x, (∀ h ∈ (KO k (Fin r) : Set (GL (Fin r) k)), π₁ h x = x) →
      f.toLinearMap x = 0 → x = 0 := by
    intro x hx hfx
    refine hf x ?_ hfx
    show ∀ h : ↥(KO k (Fin r)), π₁ h x = ((1 : ↥(KO k (Fin r)) →* ℂˣ) h : ℂ) • x
    intro h
    simpa using hx h h.2
  have hv : ∀ h ∈ (KO k (Fin r) : Set (GL (Fin r) k)),
      LinearMap.rTensor U (π₁ h) (F.1.1 1) = F.1.1 1 := by
    intro h hh
    set ℓ : Levi k (Two (Fin r) (Fin t)) := leviTwo k (Fin r) (Fin t) (h, 1) with hℓ
    have hℓK : ∀ b, ℓ b ∈ KO k (Two (Fin r) (Fin t) b) := by
      intro b
      cases b
      · exact hh
      · exact one_mem _
    have hEmb : leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ ∈ KO k (Fin (r + t)) := by
      have hfacts := (GlobalTheory.SmGL.LeviInt.levi_integral_facts k Bool (Fin (r + t))
        (Two (Fin r) (Fin t)) (two (stdSum (rfl : r + t = r + t)))).1 ℓ 1 (one_mem _)
      simpa using hfacts.mpr ⟨hℓK, one_mem _⟩
    have hDelta : deltaHalf k (Two (Fin r) (Fin t)) ℓ = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one (fun a _ => ?_)
      
      apply isUnram_absPow k _ _
      obtain ⟨g, hg⟩ := hℓK a
      rw [← hg]
      have heq : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g) : kˣ) : k) =
          algebraMap 𝒪[k] k (Matrix.GeneralLinearGroup.det g : 𝒪[k]ˣ) :=
        ((algebraMap 𝒪[k] k).map_det _).symm
      exact heq.symm ▸ (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)
    have h2 : F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = F.1.1 1 := by
      simpa using hFix _ (hEmb) 1
    have h1 := hind ⟨leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ, leviEmb_mem_parab k _ ℓ⟩ 1
    rw [mul_one] at h1
    change F.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t))) ℓ) = _ at h1
    rw [h2] at h1
    have hE : extTensor π₁ π₂ (h, 1) = LinearMap.rTensor U (π₁ h) := by
      apply TensorProduct.ext'
      intro x u
      simp [extTensor_tmul]
    clear hind hF' hFix h0' hf' hF h0 h2
    conv_rhs => rw [h1]
    rw [MonoidHom.comp_apply, twist_apply, leviProj_leviEmb, hDelta,
      MonoidHom.comp_apply, hℓ]
    simp [hE]
  have h1F : F.1.1 1 = 0 :=
    eq_zero_of_rTensor π₁ (KO k (Fin r) : Set (GL (Fin r) k)) f.toLinearMap hf' (F.1.1 1) hv (h0' 1)
  have hall : ∀ x, F.1.1 x = 0 := by
    intro x
    obtain ⟨p, c, hc, rfl⟩ := GlobalTheory.SmGL.Stages.iwasawa_two (k := k) (stdSum (rfl : r + t = r + t)) x
    rw [hFix c hc, ← mul_one (p : GL (Fin (r + t)) k), hind p 1, h1F, map_zero]
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [hall x]
  rfl

end PositivityTheory.Rg.BcB.N3.PseStage

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unrChar_append {r t : ℕ} (a : Fin r → ℂˣ) (b : Fin t → ℂˣ) :
    (fun i => unrChar k (Fin.append a b i)) = Fin.append (fun i => unrChar k (a i)) (fun i => unrChar k (b i)) := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;> simp

set_option maxHeartbeats 2000000 in
theorem prin_append {r t : ℕ} (ψ₁ : Fin r → kˣ →* ℂˣ) (ψ₂ : Fin t → kˣ →* ℂˣ) :
    Nonempty ((prod₂ (prinSeries ψ₁) (prinSeries ψ₂)).Equiv (prinSeries (Fin.append ψ₁ ψ₂))) := by
  obtain ⟨E1⟩ := GlobalTheory.SmGL.PrinProd.stage_one (k := k) ψ₁ ψ₂
  obtain ⟨E2⟩ := GlobalTheory.SmGL.PrinProd.stage_two (k := k) ψ₁ ψ₂
  exact ⟨E1.trans E2⟩

set_option maxHeartbeats 2000000 in
theorem iP_append (r t : ℕ) (A : Fin r → ℂˣ) (B : Fin t → ℂˣ) :
    Nonempty ((prod₂ (iP (k := k) A) (iP (k := k) B)).Equiv (iP (k := k) (Fin.append A B))) := by
  have key : ∀ χ : Fin (r + t) → kˣ →* ℂˣ,
      χ = Fin.append (fun i => unrChar k (A i)) (fun i => unrChar k (B i)) →
      Nonempty ((prod₂ (prinSeries fun i => unrChar k (A i))
        (prinSeries fun i => unrChar k (B i))).Equiv (prinSeries χ)) := by
    rintro χ rfl
    exact prin_append _ _
  exact key _ (unrChar_append A B)

theorem mainGen {r t : ℕ} {VA VB Vc Vc' Vi Vi' Vo Vo' : Type} [AddCommGroup VA] [Module ℂ VA] [AddCommGroup VB]
    [Module ℂ VB] [AddCommGroup Vc] [Module ℂ Vc] [AddCommGroup Vc'] [Module ℂ Vc'] [AddCommGroup Vi] [Module ℂ Vi]
    [AddCommGroup Vi'] [Module ℂ Vi'] [AddCommGroup Vo] [Module ℂ Vo] [AddCommGroup Vo'] [Module ℂ Vo']
    (πA : Representation ℂ (GL (Fin r) k) VA) (πB : Representation ℂ (GL (Fin t) k) VB)
    {πc : Representation ℂ (GL (Fin 2) k) Vc} {πc' : Representation ℂ (GL (Fin 2) k) Vc'}
    {πi : Representation ℂ (GL (Fin (2 + t)) k) Vi} {πi' : Representation ℂ (GL (Fin (2 + t)) k) Vi'}
    {πo : Representation ℂ (GL (Fin (r + (2 + t))) k) Vo} {πo' : Representation ℂ (GL (Fin (r + (2 + t))) k) Vo'}
    (Ei : (prod₂ πc πB).Equiv πi) (Ei' : (prod₂ πc' πB).Equiv πi') (Eo : (prod₂ πA πi).Equiv πo)
    (Eo' : (prod₂ πA πi').Equiv πo') (T : πc.IntertwiningMap πc') (hT : KInj k T) :
    ∃ T' : πo.IntertwiningMap πo', KInj k T' := by
  let M : πi.IntertwiningMap πi' :=
    Ei'.toIntertwiningMap.comp ((GlobalTheory.CompanionTheory.CuspStd.prod₂MapL T πB).comp Ei.symm.toIntertwiningMap)
  have hM : KInj k M :=
    kinj_comp _ _ (kinj_comp _ _ (kinj_equiv _) (kinj_prod₂MapL T hT _)) (kinj_equiv _)
  exact ⟨Eo'.toIntertwiningMap.comp ((GlobalTheory.CompanionTheory.CuspStd.prod₂MapR πA M).comp Eo.symm.toIntertwiningMap),
    kinj_comp _ _ (kinj_comp _ _ (kinj_equiv _) (kinj_prod₂MapR _ M hM)) (kinj_equiv _)⟩

end PositivityTheory.Rg.BcB.N3.PseStage

end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped TensorProduct

namespace PositivityTheory.Rg.BcB.N3.PseStage

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 2000000 in
theorem main {r t : ℕ} (A : Fin r → ℂˣ) (a b : ℂˣ) (B : Fin t → ℂˣ)
    (T : (iP (k := k) ![a, b]).IntertwiningMap (iP (k := k) ![b, a])) (hT : KInj k T) :
    ∃ T' : (iP (k := k) (Fin.append A (Fin.append ![a, b] B))).IntertwiningMap
      (iP (k := k) (Fin.append A (Fin.append ![b, a] B))), KInj k T' := by
  obtain ⟨Ei⟩ := iP_append (k := k) 2 t ![a, b] B
  obtain ⟨Ei'⟩ := iP_append (k := k) 2 t ![b, a] B
  obtain ⟨Eo⟩ := iP_append (k := k) r (2 + t) A (Fin.append ![a, b] B)
  obtain ⟨Eo'⟩ := iP_append (k := k) r (2 + t) A (Fin.append ![b, a] B)
  exact mainGen _ _ Ei Ei' Eo Eo' T hT

set_option maxHeartbeats 2000000 in
variable (k) in
theorem stageLift : StageLift k := by
  intro n η i j hij ⟨T, hT⟩
  obtain ⟨r, hr⟩ : ∃ r, i.val = r := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, n = r + (2 + t) := ⟨n - (r + 2), by have := j.isLt; omega⟩
  subst ht
  obtain ⟨A, hA⟩ : ∃ A : Fin r → ℂˣ, ∀ l, A l = η (Fin.castAdd (2 + t) l) := ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Fin t → ℂˣ, ∀ l, B l = η (Fin.natAdd r (Fin.natAdd 2 l)) := ⟨_, fun _ => rfl⟩
  have ei : ∀ h : 0 < 2, Fin.natAdd r (Fin.castAdd t (⟨0, h⟩ : Fin 2)) = i := fun h => Fin.ext (by simp [hr])
  have ej : ∀ h : 1 < 2, Fin.natAdd r (Fin.castAdd t (⟨1, h⟩ : Fin 2)) = j := fun h => Fin.ext (by simp [hr, hij])
  have h1 : η = Fin.append A (Fin.append ![η i, η j] B) := by
    funext x
    refine Fin.addCases (fun l => ?_) (fun l => ?_) x
    · rw [Fin.append_left, hA]
    · rw [Fin.append_right]
      refine Fin.addCases (fun m => ?_) (fun m => ?_) l
      · rw [Fin.append_left]
        match m with
        | ⟨0, h⟩ => rw [ei h]; rfl
        | ⟨1, h⟩ => rw [ej h]; rfl
      · rw [Fin.append_right, hB]
  have h2 : η ∘ Equiv.swap i j = Fin.append A (Fin.append ![η j, η i] B) := by
    funext x
    refine Fin.addCases (fun l => ?_) (fun l => ?_) x
    · have e1 : Fin.castAdd (2 + t) l ≠ i := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      have e2 : Fin.castAdd (2 + t) l ≠ j := fun e => by
        have := congrArg Fin.val e; simp at this; omega
      rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne e1 e2, Fin.append_left, hA]
    · rw [Fin.append_right]
      refine Fin.addCases (fun m => ?_) (fun m => ?_) l
      · rw [Fin.append_left]
        match m with
        | ⟨0, h⟩ => rw [Function.comp_apply, ei h, Equiv.swap_apply_left]; rfl
        | ⟨1, h⟩ => rw [Function.comp_apply, ej h, Equiv.swap_apply_right]; rfl
      · have e1 : Fin.natAdd r (Fin.natAdd 2 m) ≠ i := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        have e2 : Fin.natAdd r (Fin.natAdd 2 m) ≠ j := fun e => by
          have := congrArg Fin.val e; simp at this; omega
        rw [Fin.append_right, hB, Function.comp_apply, Equiv.swap_apply_of_ne_of_ne e1 e2]
  have := main (k := k) A (η i) (η j) B T hT
  rw [← h1, ← h2] at this
  exact this

end PositivityTheory.Rg.BcB.N3.PseStage

end
end

namespace PositivityTheory.Rg.BcB.N3.Pse

open PositivityTheory.Rg.BcB.N3 GlobalTheory.SmGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GL2_spherical_swap : GL2SphericalSwap k := fun a b hab => by
  by_cases hL : unrChar k a = unrChar k b * absPow k 1
  · exact PositivityTheory.Rg.BcB.N3.GL2LinkedPair.linked a b hL
  · exact unl a b hL hab

theorem sphEmb : SphEmb k :=
  sphEmb_of k (GL2_spherical_swap k) (PositivityTheory.Rg.BcB.N3.PseStage.stageLift k) PositivityTheory.Rg.BcB.N3.PseExp.expSph
    PositivityTheory.Rg.BcB.N3.PseSat.satPerm PositivityTheory.Rg.BcB.N3.PseBub.bubble

end PositivityTheory.Rg.BcB.N3.Pse
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.UniqSub
namespace PositivityTheory.Rg.BcB.N3.Pus

theorem uniqSub (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    UniqSub k := uniqSub'

end PositivityTheory.Rg.BcB.N3.Pus
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.GaloisFixedAdelicMatricesDescend
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pee

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem extremeSph_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hC : SphConst k) (hS : SphEmb k) (hU : UniqSub k) : ExtremeSph k := by
  intro h0 n ξ hm V _ _ π hs hi ⟨f, hf⟩
  obtain ⟨W, _, _, σ, hσs, hσi, hσsph, hσq⟩ := hC n ξ
  obtain ⟨g, hg⟩ := hS n ξ hm W σ hσs hσi hσsph hσq
  obtain ⟨w, hwK, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσsph
  have hg0 : g ≠ 0 := fun e => hw0 (hg (by rw [e, map_zero]; rfl))
  obtain ⟨e⟩ := hU h0 n ξ hm V W π σ hi hσi f g hf hg0
  refine fun hb => hw0 ?_
  have hv : e.toLinearEquiv.symm w ∈ fixed π (KO k (Fin n)) := fun h => by
    have h1 := hwK h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
    apply e.toLinearEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    have h2 := e.isIntertwining' h
    have h3 := congrArg (fun F => F (e.toLinearEquiv.symm w)) h2
    simp only [LinearMap.comp_apply] at h3
    refine (h3.trans ?_).trans h1
    show σ h (e.toLinearEquiv (e.toLinearEquiv.symm w)) = σ h w
    rw [LinearEquiv.apply_symm_apply]
  rw [hb] at hv
  have h5 := congrArg e.toLinearEquiv ((Submodule.mem_bot ℂ).1 hv)
  rwa [LinearEquiv.apply_symm_apply, map_zero] at h5

theorem galois_fixed_adelic_matrices_descend (hE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ExpEmb k)
    (hX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ExtremeSph k)
    (hL : SatLink) : N3 := by
  intro E _ _ w c n N h σ P ξ hq he hm
  obtain ⟨f, hf⟩ := hE (w.adicCompletion E) n P.V P.ρ ξ P.smooth he
  have hc : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact hL E w c n N h σ P ξ hq (hX (w.adicCompletion E) hc n ξ hm P.V P.ρ P.smooth P.irred ⟨f, hf⟩) ⟨f, hf⟩

end PositivityTheory.Rg.BcB.N3.Pee
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.ExpEmb
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.Pee

theorem expEmb (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.Rg.BcB.N3.ExpEmb k := by
  intro n V _ _ π ξ hπ ⟨ℓ, hℓ0, hℓ⟩
  let χ : (Fin n → kˣ) →* ℂˣ := torusChar fun i => unrChar k (ξ i)
  let ρ := (ofChar χ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨ℓ, fun g => LinearMap.ext fun v => by
      have h := hℓ ((leviTorus k (Fin n)).symm g) v
      have e : jacB π ((leviTorus k (Fin n)).symm g) = jac (points (Fin n)) π g := by
        show (jac (points (Fin n)) π) ((leviTorus k (Fin n)) ((leviTorus k (Fin n)).symm g)) = _
        rw [MulEquiv.apply_symm_apply]
      rw [e] at h
      refine h.trans ?_
      exact (ofChar_apply χ ((leviTorus k (Fin n)).symm g) (ℓ v)).symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  refine ⟨f, fun h0 => hℓ0 ?_⟩
  have : φ = GlobalTheory.SmGL.Model.evalOne (points (Fin n)) (0 : π.IntertwiningMap (iP (k := k) ξ)) := by
    rw [← hf, h0]
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 := congrArg (fun F => F (Submodule.Quotient.mk v)) this
  exact h1

end PositivityTheory.Rg.BcB.N3.Pee
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.InjectiveOfIrred
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LFun
open GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.N3.Psl

open PositivityTheory.Rg.BcB.N3

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := by
  intro y
  have e : {g : G | S.toRepresentation g y = y} = {g : G | ρ g (y : V) = y} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [e]
  exact hρ (y : V)

theorem injective_of_irred {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hi : ρ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : f ≠ 0) :
    Function.Injective f := by
  have := hi
  exact (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf

theorem coe_mem_fixed {ρ : Representation ℂ G V} (S : Subrepresentation ρ) {K : Subgroup G}
    {s : S.toSubmodule} (hs : s ∈ fixed S.toRepresentation K) : s.1 ∈ fixed ρ K :=
  GlobalTheory.LGrp.mem_fixed.2 fun g hg => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hs g hg)

theorem hI {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (g : G) (y : V) : f (ρ g y) = σ g (f y) :=
  Representation.IntertwiningMap.isIntertwining _ _ f g y

set_option maxHeartbeats 4000000 in
theorem satLink : SatLink := by
  intro E _ _ w c n N h σ P ξ hq hsph ⟨f, hf⟩
  have hKO : ∀ m, KGL w (n := m) = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hc : IsCompact (KO (w.adicCompletion E) (Fin n) : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isCompact_KO

  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hfi := injective_of_irred P.irred f hf

  have hy : f x ∈ fixed (iP (k := w.adicCompletion E) ξ) (KO _ (Fin n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => by rw [← hI f, GlobalTheory.LGrp.mem_fixed.1 hx g hg]
  have hy0 : f x ≠ 0 := fun e => hx0 (hfi (e.trans (map_zero f).symm))
  have hφ : Formalism.UG.IsSpherical E w (fun i => (ξ i : ℂ)) (f x).1.1 :=
    (SphCompletion.isSpherical_iff E w n ξ _).2 ⟨f x, hy, rfl⟩
  have hφ0 : (f x).1.1 ≠ 0 := fun e => hy0 (Subtype.ext (Subtype.ext e))
  have hsatφ := isSatVecGL_of_isSpherical (w := w) hφ hφ0
  have hsatY : IsSatVecGL w (iP (k := w.adicCompletion E) ξ) (f x) (Finset.univ.val.map ξ) :=
    IsSatVecGL.of_map (ρ' := rightReg ℂ _ ℂ) ((Submodule.subtype _).comp (Submodule.subtype _))
      (fun _ _ => rfl) (fun u v e => Subtype.ext (Subtype.ext e)) hsatφ
  have hsatX : IsSatVecGL w P.ρ x (Finset.univ.val.map ξ) :=
    IsSatVecGL.of_map f.toLinearMap (fun g y => hI f g y) hfi hsatY

  obtain ⟨S, q, hqs⟩ := hq
  obtain ⟨s0, hs0⟩ := hqs x
  have hSs : IsSmooth S.toRepresentation := isSmooth_sub (isSmooth_parInd _ _) S
  set s := GlobalTheory.LocGL.idem hSs hc s0 with hsdef
  have hqs' : q s = x := by
    rw [hsdef, GlobalTheory.LocGL.map_idem hSs P.smooth hc q s0, hs0, GlobalTheory.LocGL.idem_of_mem P.smooth hc hx]
  have hsfix : s ∈ fixed S.toRepresentation (KO _ (Fin n)) := GlobalTheory.LocGL.idem_mem hSs hc s0
  have htfix : s.1 ∈ fixed (locProd h w σ) (KGL w (n := n)) := by
    rw [hKO]
    exact coe_mem_fixed S hsfix
  have ht0 : s.1 ≠ 0 := fun e => hx0 (by rw [← hqs', show s = 0 from Subtype.ext e, map_zero])
  obtain ⟨B, hB, hsat⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (fun i => (σ i).smooth) (fun i => (σ i).irred) htfix ht0
  have hsatS : IsSatVecGL w S.toRepresentation s (∑ i, B i) :=
    IsSatVecGL.of_map (S.toSubmodule.subtype) (fun _ _ => rfl) Subtype.val_injective hsat
  have hsatX' : IsSatVecGL w P.ρ x (∑ i, B i) := by
    have := hsatS.map q.toLinearMap (fun g y => hI q g y) (by
      show q s ≠ 0
      rw [hqs']; exact hx0)
    rwa [show q.toLinearMap s = x from hqs'] at this
  exact ⟨fun i => (hB i).1, B, hB, hsatX'.unique hsatX⟩

end PositivityTheory.Rg.BcB.N3.Psl
end
end

namespace PositivityTheory.Rg.BcB.N3.Final

open PositivityTheory.Rg.BcB.N3

theorem n3 : N3 :=
  Pee.galois_fixed_adelic_matrices_descend (fun k _ _ _ _ => Pee.expEmb k)
    (fun k _ _ _ _ => Pee.extremeSph_of k (Pee.sphConst k) (Pse.sphEmb k) (Pus.uniqSub k)) Psl.satLink

end PositivityTheory.Rg.BcB.N3.Final
