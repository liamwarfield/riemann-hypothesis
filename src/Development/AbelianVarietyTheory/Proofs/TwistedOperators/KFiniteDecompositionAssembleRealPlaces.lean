module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslationLiftEqLevelMoveUnitConst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementLatticeBetweenPrimeMulSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical

noncomputable section

namespace GlobalTheory.KFinDecomp

theorem assemble_finset {ι : Type} [DecidableEq ι] {U : ι → Type} [∀ τ, AddCommGroup (U τ)] [∀ τ, Module ℂ (U τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (𝒞 : Set E) (Ty : ι → E → Prop)
    (R : ∀ τ, U τ → U τ → (E → E) → Prop) (m : ι → ℕ) (a : ∀ τ, Fin (m τ) → U τ)
    (A : ∀ τ, Fin (m τ) → U τ → E → E)
    (hadd : ∀ τ j u, ∀ f ∈ 𝒞, ∀ f' ∈ 𝒞, A τ j u (f + f') = A τ j u f + A τ j u f')
    (hsmul : ∀ τ j u (c : ℂ), ∀ f ∈ 𝒞, A τ j u (c • f) = c • A τ j u f)
    (hmaps : ∀ τ j u, ∀ f ∈ 𝒞, A τ j u f ∈ 𝒞)
    (hkeep : ∀ τ j u τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A τ j u f))
    (hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f))
    (hadd' : ∀ τ j, ∀ f ∈ 𝒞, ∀ u u', A τ j (u + u') f = A τ j u f + A τ j u' f)
    (hsmul' : ∀ τ j, ∀ f ∈ 𝒞, ∀ (c : ℂ) u, A τ j (c • u) f = c • A τ j u f)
    (hR : ∀ τ j, ∀ f ∈ 𝒞, ∀ u w Φ, R τ u w Φ → A τ j w f = Φ (A τ j u f))
    (hsum : ∀ τ, ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A τ j (a τ j) f)
    (ψ : E) (hψ : ψ ∈ 𝒞) (hTy : ∀ τ, Ty τ ψ) (s : Finset ι) :
    ∃ (κ : Type) (_ : Fintype κ) (T : κ → (∀ τ, U τ) → E) (u : κ → ∀ τ, U τ),
      (∀ k v, T k v ∈ 𝒞) ∧ (∀ k v, ∀ τ ∉ s, Ty τ (T k v)) ∧
      (∀ k v, ∀ τ ∉ s, ∀ w, T k (Function.update v τ w) = T k v) ∧
      (∀ k v, ∀ τ ∈ s, ∀ x y, T k (Function.update v τ (x + y)) =
        T k (Function.update v τ x) + T k (Function.update v τ y)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ (c : ℂ) x, T k (Function.update v τ (c • x)) = c • T k (Function.update v τ x)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ w Φ, R τ (v τ) w Φ → T k (Function.update v τ w) = Φ (T k v)) ∧
      ψ = ∑ k, T k (u k) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ _ => ψ, fun _ _ => 0, fun _ _ => hψ, fun _ _ τ _ => hTy τ,
      fun _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · simp
  | @insert τ₀ s hτ₀ ih =>
    obtain ⟨κ, hκ, T, u, hT𝒞, hTTy, hTfix, hTadd, hTsmul, hTR, hψs⟩ := ih

    refine ⟨κ × Fin (m τ₀), inferInstance, fun p v => A τ₀ p.2 (v τ₀) (T p.1 v),
      fun p => Function.update (u p.1) τ₀ (a τ₀ p.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p v
      exact hmaps _ _ _ _ (hT𝒞 _ _)
    · intro p v τ hτ
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      exact hkeep τ₀ p.2 (v τ₀) τ hne _ (hT𝒞 _ _) (hTTy _ _ τ hs)
    · intro p v τ hτ w
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) = A τ₀ p.2 (v τ₀) (T p.1 v)
      rw [Function.update_of_ne hne.symm, hTfix p.1 v τ hs w]
    · intro p v τ hτ x y
      show A τ₀ p.2 (Function.update v τ (x + y) τ₀) (T p.1 (Function.update v τ (x + y))) =
        A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x)) +
          A τ₀ p.2 (Function.update v τ y τ₀) (T p.1 (Function.update v τ y))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hadd' τ p.2 _ (hT𝒞 _ _) x y
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          Function.update_of_ne (Ne.symm h), hTadd p.1 v τ hs x y]
        exact hadd τ₀ p.2 (v τ₀) _ (hT𝒞 _ _) _ (hT𝒞 _ _)
    · intro p v τ hτ c x
      show A τ₀ p.2 (Function.update v τ (c • x) τ₀) (T p.1 (Function.update v τ (c • x))) =
        c • A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hsmul' τ p.2 _ (hT𝒞 _ _) c x
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          hTsmul p.1 v τ hs c x]
        exact hsmul τ₀ p.2 (v τ₀) c _ (hT𝒞 _ _)
    · intro p v τ hτ w Φ hRw
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) =
        Φ (A τ₀ p.2 (v τ₀) (T p.1 v))
      by_cases h : τ = τ₀
      · subst h
        rw [Function.update_self, hTfix p.1 v τ hτ₀]
        exact hR τ p.2 _ (hT𝒞 _ _) (v τ) w Φ hRw
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), hTR p.1 v τ hs w Φ hRw]
        exact (hcomm τ₀ p.2 (v τ₀) τ h (v τ) w Φ hRw _ (hT𝒞 _ _)).symm ▸ rfl
    ·
      have hterm : ∀ k, T k (u k) = ∑ j, A τ₀ j (a τ₀ j) (T k (u k)) := fun k =>
        hsum τ₀ _ (hT𝒞 _ _) (hTTy _ _ τ₀ hτ₀)
      rw [Fintype.sum_prod_type, hψs]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm k]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A τ₀ j (a τ₀ j) (T k (u k)) =
        A τ₀ j (Function.update (u k) τ₀ (a τ₀ j) τ₀) (T k (Function.update (u k) τ₀ (a τ₀ j)))
      rw [Function.update_self, hTfix k (u k) τ₀ hτ₀]

theorem assemble_places : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  intro D θ N 𝒞 Ty hcont hdec ψ hψ hTy
  unfold GlobalTheory.KFinDecomp.DecompAt at hdec
  choose m a A hop hlin hsum using hdec

  have hK : ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, k ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := by
    intro τ k hk
    have hu : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (N.M.fr_unit τ)
    have h := (GlobalTheory.Chain.RealLine.Semi.conj_compact N.M τ (k := N.M.fr τ * k * (N.M.fr τ)⁻¹) hk).1
    have he : (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ = k :=
      calc (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ
          = ((N.M.fr τ)⁻¹ * N.M.fr τ) * k * ((N.M.fr τ)⁻¹ * N.M.fr τ) := by simp only [mul_assoc]
        _ = k := by rw [Matrix.nonsing_inv_mul _ hu, one_mul, mul_one]
    rwa [he] at h

  let R : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ →
      ((GA D N.V → ℂ) → (GA D N.V → ℂ)) → Prop := fun τ x y Φ =>
    (∃ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, (y : N.M.H τ) = N.M.rep τ k x ∧
        Φ = fun f => rTr N.V (atTau θ N.V τ k) f) ∨
      (∃ X ∈ lieAt N.V τ, (y : N.M.H τ) = dRep (N.M.rep τ) X x ∧ Φ = fun f => Rder θ N.V τ X f)
  have hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f) := by
    rintro τ j u τ' hne x y Φ (⟨k, hk, -, rfl⟩ | ⟨X, hX, -, rfl⟩) f hf
    · exact (hop τ j u).tr τ' hne k (hK τ' k hk) f hf
    · exact (hop τ j u).lie τ' hne X hX f hf
  have hRel : ∀ τ j, ∀ f ∈ 𝒞, ∀ x y Φ, R τ x y Φ → A τ j y f = Φ (A τ j x f) := by
    rintro τ j f hf x y Φ (⟨k, hk, hy, rfl⟩ | ⟨X, hX, hy, rfl⟩)
    · exact (hlin τ j f hf).2.2.1 k hk x y hy
    · exact (hlin τ j f hf).2.2.2 X hX x y hy
  obtain ⟨κ, hκ, T, u, hT𝒞, -, -, hTadd, hTsmul, hTR, hψT⟩ :=
    GlobalTheory.KFinDecomp.assemble_finset (U := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) 𝒞 Ty R m a A
      (fun τ j x f hf f' hf' => (hop τ j x).add f f' (hcont f hf) (hcont f' hf'))
      (fun τ j x c f hf => (hop τ j x).smul c f (hcont f hf))
      (fun τ j x f hf => (hop τ j x).maps f hf)
      (fun τ j x τ' hne f hf h' => (hop τ j x).keep τ' hne f hf h')
      hcomm
      (fun τ j f hf x x' => (hlin τ j f hf).1 x x')
      (fun τ j f hf c x => (hlin τ j f hf).2.1 c x)
      hRel hsum ψ hψ hTy Finset.univ

  let e := Fintype.equivFin κ
  let T₀ : Fin (Fintype.card κ) → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M := fun j =>
    (⟨T (e.symm j),
      fun v τ x y => by convert hTadd (e.symm j) v τ (Finset.mem_univ τ) x y,
      fun v τ c x => by convert hTsmul (e.symm j) v τ (Finset.mem_univ τ) c x⟩ :
      MultilinearMap (RingHom.id ℂ) (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) (GA D N.V → ℂ))
  refine ⟨Fintype.card κ, T₀, fun j => u (e.symm j), fun j v => hT𝒞 (e.symm j) v, ?_, ?_, ?_⟩
  · intro j τ k hk v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inl ⟨k, hk, hw, rfl⟩)
  · intro j τ X hX v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inr ⟨X, hX, hw, rfl⟩)
  · rw [hψT]
    exact (Equiv.sum_comp e.symm (fun k => T k (u k))).symm

end GlobalTheory.KFinDecomp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFiniteDecomposition_assemble_realPlaces : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @GlobalTheory.KFinDecomp.assemble_places | exact GlobalTheory.KFinDecomp.assemble_places | (intros; apply GlobalTheory.KFinDecomp.assemble_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetOfSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetRepHeckeElementPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetRepHeckeElementPrincipalLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

open Formalism.IndefR.Lev GlobalTheory.HeckeParts Formalism.L2.NTheta

theorem GlobalTheory.HeckeDC.exists_rep : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))) (e : AE D) (ϖ : 𝓞 D.host.E) (a₀ : GA D (Wc D i)),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt (Wc D i) e (ϖ : D.host.E) k a₀ →
    ∃ a ∈ Rc, a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc e ϖ a₀ hso hα hRc he hϖ hϖ2 ha₀
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨Lp, -, -, -, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨e', ϖ', he', h1', h2', hαe'⟩ := hα
  have hee : e' = e := idem_unique (Wc D i) he he'
  rw [hee] at hαe'
  obtain ⟨-, -, hloc⟩ := GlobalTheory.SplitPlace.split_local (Wc D i) P e he
  obtain ⟨x, hx, y, hy, hxy⟩ := ((hloc ϖ' h1' h2').2 k α hαe').2 ϖ a₀ hϖ hϖ2 ha₀
  obtain ⟨a, ⟨haR, haK⟩, -⟩ := hRc.2 a₀ ⟨⟨x, ((hK x).1 hx).1⟩, ⟨y, ((hK y).1 hy).1⟩, hxy⟩
  exact ⟨a, haR, haK⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetRepHeckeElementPrincipalLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coset_rep_hecke_element_principal_level : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))) (e : AE D) (ϖ : 𝓞 D.host.E) (a₀ : GA D (Wc D i)),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt (Wc D i) e (ϖ : D.host.E) k a₀ →
    ∃ a ∈ Rc, a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  first | exact @GlobalTheory.HeckeDC.exists_rep | exact GlobalTheory.HeckeDC.exists_rep | (intros; apply GlobalTheory.HeckeDC.exists_rep <;> assumption)
end
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckeLatCoset

theorem selfDual_eq : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.Col.conjPrime₂ P ≠ P → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
    (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → X = Y := by
  intro D V P X Y hP hX hY hXY hYX
  have hcc : ∀ s : 𝓞 D.host.E,
      ReciprocityTheory.ChartRestriction.G.FD.cc ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
    intro s
    show IsCMField.complexConj D.host.E (star (s : D.host.E)) = (s : D.host.E)
    exact star_star (s : D.host.E)
  have hcO : ∀ s : 𝓞 D.host.E, Formalism.L2.Col.cO D.host.E (Formalism.L2.Col.cO D.host.E s) = s := by
    intro s
    apply RingOfIntegers.ext
    show star (star (s : D.host.E)) = (s : D.host.E)
    exact star_star _
  have key : ∀ (s : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E),
      ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) (s • v) y =
        ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v (Formalism.L2.Col.cO D.host.E s • y) := by
    intro s v y
    unfold ReciprocityTheory.ChartRestriction.G.FD.herm
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have e1 : (s • v) a = (s : D.host.E) * v a := rfl
    have e2 : (Formalism.L2.Col.cO D.host.E s • y) b = ((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b := rfl
    have e3 : ReciprocityTheory.ChartRestriction.G.FD.cc (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E) * y b) =
        (s : D.host.E) * ReciprocityTheory.ChartRestriction.G.FD.cc (y b) := by
      rw [← hcc s]
      exact map_mul (IsCMField.complexConj D.host.E) _ _
    rw [e1, e2, e3]
    ring
  have hne : P.asIdeal ≠ (Formalism.L2.Col.conjPrime₂ P).asIdeal := fun h =>
    hP (IsDedekindDomain.HeightOneSpectrum.ext h.symm)
  have hcop : P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne P.isMaximal (Formalism.L2.Col.conjPrime₂ P).isMaximal hne
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ P.asIdeal ⊔ (Formalism.L2.Col.conjPrime₂ P).asIdeal)
  have hsc : Formalism.L2.Col.cO D.host.E s ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, hcO]
    exact hs
  have incl : ∀ X Y : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ X, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ X) → (∀ v : Fin (V).rank → D.host.E, (∀ y ∈ Y, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(V).gram.transpose) v y) = n) ↔ v ∈ Y) →
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • X ≤ Y → (Formalism.L2.Col.conjPrime₂ P).asIdeal • Y ≤ X → Y ≤ X := by
    intro X Y hX hY hXY hYX l hl
    have h1 : t • l ∈ X := hYX (Submodule.smul_mem_smul ht hl)
    have h2 : s • l ∈ X := by
      rw [← hX]
      intro x hx
      have hx' : Formalism.L2.Col.cO D.host.E s • x ∈ Y := hXY (Submodule.smul_mem_smul hsc hx)
      obtain ⟨n, hn⟩ := (hY l).2 hl _ hx'
      exact ⟨n, by rw [key]; exact hn⟩
    have e : l = s • l + t • l := by rw [← add_smul, hst, one_smul]
    rw [e]
    exact X.add_mem h2 h1
  exact le_antisymm (incl Y X hY hX hYX hXY) (incl X Y hX hY hXY hYX)

theorem latG_mul_levG : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (x κ : GA D (Wc D i)),
    κ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) → latG (Wc D i) (x * κ) = latG (Wc D i) x := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL i x κ hκ
  have hκ' : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 κ :=
    ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩
  have hS := GlobalTheory.DictMove.latGHat_eq (hL.βW i) hκ'
  ext v
  rw [(GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).1, (GlobalTheory.MarkCoset.latG_spec D _ x).1,
    (GlobalTheory.MarkCoset.latG_spec D _ (x * κ)).2, (GlobalTheory.MarkCoset.latG_spec D _ x).2]
  constructor
  · rintro ⟨y, hy, hyz⟩
    refine ⟨(finHom (Wc D i) κ).1.mulVec y, ?_, ?_⟩
    · rw [← hS]
      exact ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).2 ⟨y, hy, rfl⟩
    · rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]
  · rintro ⟨y, hy, hyz⟩
    rw [← hS] at hy
    obtain ⟨y', hy', rfl⟩ := ((GlobalTheory.MarkCoset.latG_spec D _ κ).2 _).1 hy
    exact ⟨y', hy', by rw [← hyz, map_mul, Units.val_mul, Matrix.mulVec_mulVec]⟩

theorem exists_coset_of_selfDual : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    ∀ (g : GA D (Wc D i)) (L' : Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E)),
    P.asIdeal • latG (Wc D i) g ≤ L' → (Formalism.L2.Col.conjPrime₂ P).asIdeal • L' ≤ latG (Wc D i) g →
    (∀ v : Fin (Wc D i).rank → D.host.E, (∀ y ∈ L', ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * ReciprocityTheory.ChartRestriction.G.FD.herm (-(Wc D i).gram.transpose) v y) = n) ↔ v ∈ L') →
    (L' ⊓ latG (Wc D i) g).toAddSubgroup.relIndex (latG (Wc D i) g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a ∈ Rc, latG (Wc D i) (g * a) = L' ∧ ∃ (e : AE D) (a₀ : GA D (Wc D i)), Formalism.L2.NTheta.IsIdemAt e P ∧
      SuppAt e (Wc D i) a₀ ∧ a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) ∧ latG (Wc D i) (g * a₀) = L' := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hα hRc g L' h1 h2 hsd hidx
  obtain ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ := hα
  have hP : Formalism.L2.Col.conjPrime₂ P ≠ P := by
    intro h
    apply hso.1
    rw [Formalism.L2.Col.conjIdeal_asIdeal, h]
  obtain ⟨a₀, ha₀, hT, hT2⟩ := GlobalTheory.T.exists_heckeElement_lattice_between_prime_mul_split D (Wc D i) P e ϖ k g (L' ⊓ latG (Wc D i) g) he hϖ1 hϖ2
    (le_inf h1 Submodule.smul_le_right) inf_le_right hidx
  obtain ⟨a, ha, hK⟩ := GlobalTheory.T.exists_coset_rep_hecke_element_principal_level D R hL hF i P k α Rc e ϖ a₀ hso ⟨e, ϖ, he, hϖ1, hϖ2, hαe⟩ hRc he hϖ1 hϖ2 ha₀
  have hTL : latG (Wc D i) (g * a₀) = L' := by
    refine selfDual_eq D (Wc D i) P _ _ hP (GlobalTheory.Member.latG_selfDual D (Wc D i) (g * a₀) _ rfl).2.2 hsd ?_ ?_
    · refine le_trans ?_ (inf_le_left : L' ⊓ latG (Wc D i) g ≤ L')
      rw [← hT]
      exact le_inf Submodule.smul_le_right hT2
    · refine le_trans ?_ (inf_le_left : latG (Wc D i) (g * a₀) ⊓ latG (Wc D i) g ≤ _)
      rw [hT]
      exact le_inf Submodule.smul_le_right h2
  have hga : latG (Wc D i) (g * a) = latG (Wc D i) (g * a₀) := by
    have := latG_mul_levG D R hL i (g * a) (a⁻¹ * a₀) hK
    rw [← this, mul_assoc, mul_inv_cancel_left]
  exact ⟨a, ha, hga.trans hTL, e, a₀, he, ha₀.2.1, hK, hTL⟩

end GlobalTheory.HeckeLatCoset
end
end
