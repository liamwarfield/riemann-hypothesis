module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.InfMatchOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.BlockCandidates.PowNeOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.IdentOf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.SpectralAccumulation
open PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] PositivityTheory.Rg.BcB.F.borelG PositivityTheory.Rg.BcB.F.borelF PositivityTheory.Rg.BcB.F.borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.BaseChangeIdentities.GelfandReading

set_option maxHeartbeats 2000000 in
theorem ident_of (hD : DerVal) (hI : InfMatch) : BC.Ident := by
  intro hR E _ _ _ n π S T F₀ F i χ hχ O
  have e0 : (F.t₀ i).val O.χa O.χb = 1 := (O.eigArch (.inl ()) (F.t₀ i) rfl rfl).symm.trans (hχ.2.1 (.inl ()))
  have e1 : ∀ v s m side, (F.tD i v s m side).val O.χa O.χb = F.dval (i, v, s, m, side) := fun v s m side =>
    (O.eigArch (.inr (.inl (i, v, s, m, side))) (F.tD i v s m side) (if_pos rfl) rfl).symm.trans
      (hχ.2.1 (.inr (.inl (i, v, s, m, side))))
  have key := fun v s m => hD E _ _ _ _ _ _ _ _ (F₀.A i) F.κ (F.ψ i (F.d.eL _)) (F.ψ i (F.d.eL _))
    (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) v s m O.χa O.χb
  refine ⟨fun τ => congrFun (hI E _ O.χa (F₀.A i).χa fun v s m _ _ => ?_) τ,
    fun τ => congrFun (hI E _ O.χb (F₀.A i).χb fun v s m _ _ => ?_) τ⟩
  · have h1 := e1 v s m false
    have h2 := (key v s m).1
    have h3 : F.tD i v s m false = (F₀.A i).pt (fun v' => if v' = v then [(s, m)] else []) (fun _ => []) (F.ψ i (F.d.eL _))
        (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) := by
      unfold RunFrame.tD
      congr 1 <;> funext v' <;> simp
    rw [h3] at h1
    have h4 := h2.symm.trans h1
    erw [e0] at h4
    simpa [RunFrame.dval, zVal] using h4
  · have h1 := e1 v s m true
    have h2 := (key v s m).2
    have h3 : F.tD i v s m true = (F₀.A i).pt (fun _ => []) (fun v' => if v' = v then [(s, m)] else []) (F.ψ i (F.d.eL _))
        (PositivityTheory.Rg.BcB.F.sizeOf (F.ψ i (F.d.eL _))) := by
      unfold RunFrame.tD
      congr 1 <;> funext v' <;> simp
    rw [h3] at h1
    have h4 := h2.symm.trans h1
    erw [e0] at h4
    simpa [RunFrame.dval, zVal] using h4

end UpperTheory.BaseChangeIdentities.GelfandReading

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.GelfandReading.GReadOf
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.CharacterIntegrability.ChiPin
noncomputable section

set_option synthInstance.maxHeartbeats 200000

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5

namespace PositivityTheory.Rg.BcB.F.R3

variable {ι : Type} {H : ι → Type} [∀ s, NormedAddCommGroup (H s)] [∀ s, InnerProductSpace ℂ (H s)]
  [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem chi_pin (gen : Γ → Prod' H d) (a₀ : Γ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (ha₀ : (gen a₀).2 v = v)
    (s : ι) (X : H s →L[ℂ] H s)
    (χ : StarAlgebra.adjoin ℂ (Set.range (fun a : StarAlgebra.adjoin ℂ (Set.range gen) => (a : Prod' H d).1 s) ∪ {X})
      →⋆ₐ[ℂ] ℂ)
    (heig : ∀ a : StarAlgebra.adjoin ℂ (Set.range gen), a.1.2 v ≠ 0 → ∃ c : ℂ, a.1.2 v = c • v ∧
      χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c)
    (a : StarAlgebra.adjoin ℂ (Set.range gen)) (c : ℂ) (hc : a.1.2 v = c • v) :
    χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ = c := by
  have hinj : ∀ {c₁ c₂ : ℂ}, c₁ • v = c₂ • v → c₁ = c₂ := fun h => smul_left_injective ℂ hv h
  let A₀ : StarAlgebra.adjoin ℂ (Set.range gen) := ⟨gen a₀, StarAlgebra.subset_adjoin ℂ _ ⟨a₀, rfl⟩⟩
  have hA₀ : A₀.1.2 v = v := ha₀
  obtain ⟨c₀, hc₀, hχ₀⟩ := heig A₀ (by rw [hA₀]; exact hv)
  have hc₀1 : c₀ = 1 := hinj (by rw [← hc₀, hA₀, one_smul])
  by_cases hc0 : c = 0
  · subst hc0
    have hsum : (a + A₀).1.2 v = v := by
      show a.1.2 v + A₀.1.2 v = v
      rw [hc, hA₀, zero_smul, zero_add]
    obtain ⟨c₁, hc₁, hχ₁⟩ := heig (a + A₀) (by rw [hsum]; exact hv)
    have hc₁1 : c₁ = 1 := hinj (by rw [← hc₁, hsum, one_smul])
    have hsplit : χ ⟨(a + A₀).1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a + A₀, rfl⟩)⟩ =
        χ ⟨a.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a, rfl⟩)⟩ +
          χ ⟨A₀.1.1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨A₀, rfl⟩)⟩ := by
      rw [← map_add χ]; exact congrArg χ (Subtype.ext rfl)
    rw [hsplit, hχ₀, hc₀1, hc₁1] at hχ₁
    linear_combination hχ₁
  · obtain ⟨c', hc', hχ'⟩ := heig a (by rw [hc]; exact smul_ne_zero hc0 hv)
    rw [hχ']; exact hinj (hc'.symm.trans hc)

end PositivityTheory.Rg.BcB.F.R3

end
end

noncomputable section

namespace UpperTheory.BaseChangeIdentities.GelfandReading

open PositivityTheory.Rg.BcB.F

theorem exists_transport {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S T : StarSubalgebra ℂ A}
    (h : S = T) (χ : S →⋆ₐ[ℂ] ℂ) : ∃ χ' : T →⋆ₐ[ℂ] ℂ, (∀ y : T, ∃ z : S, z.1 = y.1 ∧ χ' y = χ z) ∧
      ∀ x (hx : x ∈ T) (hx' : x ∈ S), χ' ⟨x, hx⟩ = χ ⟨x, hx'⟩ := by
  subst h
  exact ⟨χ, fun y => ⟨y, rfl, rfl⟩, fun _ _ _ => rfl⟩

theorem gRead_of {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
    [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type} (gen : Γ → Prod' H d)
    (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (v : EuclideanSpace ℂ (Fin d)) (hv : v ≠ 0) (a₀ : Γ) (c : Γ → ℂ)
    (hc : ∀ x, (gen x).2 v = c x • v) (h₀ : c a₀ = 1) (Q : Prop)
    (hQ : ∀ (s : ι) (χ : StarAlgebra.adjoin ℂ (Set.range (fun x => (gen x).1 s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      ((∀ y, ‖χ y‖ ≤ ‖(y : H s →L[ℂ] H s)‖) ∧
        (∀ x, χ ⟨(gen x).1 s, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)⟩ = c x) ∧
        χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ ≠ 0) → Q) : GRead gen β m v Q := by
  intro s χ hn heig hX
  obtain ⟨χ', h1, h2⟩ := exists_transport (Rd.projAdjoin gen s (star (β s ^ m) * β s ^ m)) χ
  have ha : (gen a₀).2 v = v := by rw [hc, h₀, one_smul]
  refine hQ s χ' ⟨fun y => ?_, fun x => ?_, fun h => hX ((h2 _ _ _).symm.trans h)⟩
  · obtain ⟨z, e1, e2⟩ := h1 y
    rw [e2, ← e1]
    exact hn z
  · exact (h2 _ _ _).trans
      (R3.chi_pin gen a₀ v hv ha s _ χ heig ⟨gen x, StarAlgebra.subset_adjoin ℂ _ ⟨x, rfl⟩⟩ (c x) (hc x))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem chiTr : BC.ChiTr := fun _ _ _ _ _ _ _ _ _ _ G Q h1 hQ =>
  gRead_of (H := G.H) G.gen G.βop G.m G.v G.v_ne G.a₀ (fun x => G.c x G.i₀) (fun x => (G.vblk x).1) h1 Q hQ

end UpperTheory.BaseChangeIdentities.GelfandReading

end
end
