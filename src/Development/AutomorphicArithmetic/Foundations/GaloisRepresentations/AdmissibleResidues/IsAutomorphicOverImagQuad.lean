module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SumThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def NoLink (x : GL (Fin n) (Qbar l)) (Q : ℕ) : Prop :=
  ∀ α β : Qbar l, (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot α → (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot β →
    ∀ k : ℕ, 1 ≤ k → α ^ k ≠ ((Q : Qbar l) * β) ^ k

def UnlinkAt (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) : Prop :=
  ∃ (s : G F Ω) (j : ℕ), 1 ≤ j ∧ IsFrob A (normV w ^ j) s ∧ NoLink (r s) (normV w ^ j)

def Unlinked (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (r '' (Ine (F := F) A : Set (G F Ω))).Finite → UnlinkAt r w A

def Wit [IsCMField F] (_ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := Unlinked r


omit [NumberField F] in
def WitQ (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

def AutPol [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ (∃ χ, GlobalTheory.ContraPair.PolarizedPair π χ) ∧ AttC ι r π

def AutCsd0 [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π


omit [NumberField F] in
def IsAutomorphicOverImagQuad (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π

def IsAutCsdN [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutCsd0 ι r ∧ (Continuous r → Wit ι r)


section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}


end Conv

end UpperTheory.GalN.V
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealDefs
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

section Local
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure AwR (x y : WD h) : Prop where
  pol : ∀ g : ↥(Weil h), x.charPol g = y.charPol g
  n0 : y.mono0 → x = y

theorem AwR.of_eq {x y : WD h} (e : x = y) : AwR x y := ⟨fun _ => by rw [e], fun _ => e⟩

theorem AwR.eq_unr {x y : WD h} (k : AwR x y) (hy : y.unr) : x = y := k.n0 (WD.unr_mono0 _ hy)

def RatioW (x : WD h) : Prop :=
  ∀ φ : ↥(Weil h), deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ < ((normV w : ℕ) : ℝ) * ‖β‖
end Local

section Real
variable {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {a : ℕ}

structure IsGalRU (π : TR.CuspSub F a) (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
    (HT : (F →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → AwR (wdOf h hl ι r) (rc (algNorm σ))
  ratio : ∀ (w : HeightOneSpectrum (𝓞 F)) (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → (rc (algNorm σ)).mono0 →
      RatioW (wdOf h hl ι r)
  weights : ∀ (τ : F →+* Qbar l) (m : Multiset ℂ), π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) m →
    (HT τ).map (fun n : ℤ => (n : ℂ)) = m.map fun z => ((a : ℂ) - 1) / 2 - z
  weights_sym : ∀ τ : F →+* Qbar l, HT τ = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw),
      IsdRAt P Bw (r.comp (Dec (F := F) A).subtype) ∧
      (∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw (r.comp (Dec (F := F) A).subtype) τ (HT τ)) ∧
      (∀ σ, π.IsLocComp w σ → GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin a)) ≠ ⊥ →
        GlobalTheory.SmGL.IsSpherical σ.ρ → ∀ rc, IsRec h rc →
          (∀ g : ↥(Weil h), (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol g = (rc (algNorm σ)).charPol g) ∧
          ((rc (algNorm σ)).mono0 → (wdAt P ι Bw h hj (r.comp (Dec (F := F) A).subtype)).mono0)) ∧
      ∀ σ, π.IsLocComp w σ → GlobalTheory.SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := F) A).subtype)
end Real

def ExRN : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F), π.IsRegAlg → π.Polarized χ →
    ∃ (r : G F Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ), IsGalRU π ι r wt HT ∧ AttR ι r π ∧
      ∀ r' : G F Ω →* GL (Fin n) (Qbar l), Continuous r' → AttR ι r' π → IsGalRU π ι r' wt HT

end UpperTheory.GalN.V
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinDefs
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp
open scoped Matrix
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.V.Af.Bc
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

namespace UpperTheory.GalN.V.Win

structure EigData (n q : ℕ) (m : Fin n → ℤ) (wt : ℤ) where

  S : Type
  fin : Finite S

  β : S → Multiset ℂ
  card : ∀ s, (β s).card = n
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, β (e s) = (β s).map σ
  pure : ∀ s, Win q wt (β s)
  int : ∀ a : ℤ, (∀ i, -a ≤ m i) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b)
  intInv : ∀ a : ℤ, (∀ i, m i ≤ a) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)

def EigData.Classifies {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n q : ℕ}
    {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F))
    (admitted : (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, FrobEig ι r.1 w ((D.β (cl r)).map (·⁻¹))

def RootSum : Prop :=
  ∀ (n p : ℕ), 0 < p → ∀ (m : Fin n → ℤ) (wt : ℤ) (I : Type) [Fintype I] (q f : I → ℕ), (∀ i, 1 ≤ f i ∧ f i ≤ 2 ∧ q i = p ^ f i) →
    ∀ D : ∀ i, EigData n (q i) m wt, ∃ D' : EigData n p m wt, Nat.card D'.S ≤ 2 ^ (n + 1) * ∑ i, Nat.card (D i).S ∧
      ∃ e : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) → D'.S,
        Function.Injective e ∧ ∀ x, D'.β (e x) = x.2.1.1.2

structure TrData (q e : ℕ) where

  S : Type
  fin : Finite S

  t : S → ℂ
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ u : S ≃ S, ∀ s, t (u s) = σ (t s)
  bd : ∀ s, ‖t s‖ ≤ Real.sqrt q + 2
  int : ∀ s, IsIntegral ℤ ((q : ℂ) ^ e * t s)

instance {q e : ℕ} : Inhabited (TrData q e) :=
  ⟨⟨Empty, inferInstance, fun s => s.elim, fun _ => ⟨.refl _, fun s => s.elim⟩, fun s => s.elim, fun s => s.elim⟩⟩

namespace TrData

variable {q e : ℕ}

def Classifies {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] (D : TrData q e) (ι : Qbar l ≃+* ℂ) (g : Γ)
    (admitted : (Γ →* GL (Fin 3) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r // admitted r} → D.S, (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, (r.1 g : Matrix (Fin 3) (Fin 3) (Qbar l)).trace = ι.symm (D.t (cl r))

def sum (D D' : TrData q e) : TrData q e where
  S := D.S ⊕ D'.S
  fin := by have := D.fin; have := D'.fin; infer_instance
  t := Sum.elim D.t D'.t
  conj σ := by
    obtain ⟨u, hu⟩ := D.conj σ
    obtain ⟨u', hu'⟩ := D'.conj σ
    exact ⟨u.sumCongr u', fun s => by cases s <;> simp [hu, hu']⟩
  bd s := by cases s; exacts [D.bd _, D'.bd _]
  int s := by cases s; exacts [D.int _, D'.int _]

theorem card_sum (D D' : TrData q e) : Nat.card (D.sum D').S = Nat.card D.S + Nat.card D'.S := by
  have := D.fin; have := D'.fin
  exact Nat.card_sum

theorem Classifies.sum {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {D D' : TrData q e} {ι : Qbar l ≃+* ℂ} {g : Γ}
    {P P' : (Γ →* GL (Fin 3) (Qbar l)) → Prop} (h : D.Classifies ι g P) (h' : D'.Classifies ι g P') :
    (D.sum D').Classifies ι g fun r => P r ∨ P' r := by
  classical
  obtain ⟨cl, h1, h2⟩ := h
  obtain ⟨cl', h1', h2'⟩ := h'
  let F : {r // P r ∨ P' r} → D.S ⊕ D'.S :=
    fun r => if hr : P r.1 then Sum.inl (cl ⟨r.1, hr⟩) else Sum.inr (cl' ⟨r.1, r.2.resolve_left hr⟩)
  have e1 : ∀ r (hr : P r.1), F r = Sum.inl (cl ⟨r.1, hr⟩) := fun r hr => dif_pos hr
  have e2 : ∀ r (hr : ¬ P r.1), F r = Sum.inr (cl' ⟨r.1, r.2.resolve_left hr⟩) := fun r hr => dif_neg hr
  refine ⟨F, fun r r' (H : F r = F r') => ?_, fun r => ?_⟩
  · by_cases hr : P r.1 <;> by_cases hr' : P r'.1
    · rw [e1 r hr, e1 r' hr'] at H; exact h1 _ _ (Sum.inl.inj H)
    · rw [e1 r hr, e2 r' hr'] at H; cases H
    · rw [e2 r hr, e1 r' hr'] at H; cases H
    · rw [e2 r hr, e2 r' hr'] at H; exact h1' _ _ (Sum.inr.inj H)
  · change _ = ι.symm (Sum.elim D.t D'.t (F r))
    by_cases hr : P r.1
    · rw [e1 r hr]; exact h2 ⟨r.1, hr⟩
    · rw [e2 r hr]; exact h2' ⟨r.1, _⟩

end TrData

theorem exists_eigData {P W : Type} (Sig : Set P) (Iso : P → P → Prop) (sys : P → W → Multiset ℂ)
    (hiso : ∀ a ∈ Sig, ∀ b ∈ Sig, Iso a b → sys a = sys b) (N : ℕ)
    (hcard : ∀ S : Finset P, (∀ a ∈ S, a ∈ Sig) → (∀ a ∈ S, ∀ b ∈ S, Iso a b → a = b) → S.card ≤ N)
    (hconj : ∀ σ : ℂ ≃+* ℂ, ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ v, sys b v = (sys a v).map σ)
    (w : W) {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (hn : ∀ a ∈ Sig, (sys a w).card = n)
    (hq : 0 < q) (hpure : ∀ a ∈ Sig, Win q (-(wt : ℝ)) (sys a w))
    (hint : ∀ a ∈ Sig, SlopesIn q m (sys a w)) :
    ∃ D : EigData n q m wt, Nat.card D.S ≤ N ∧ ∃ cl : ↥Sig → D.S, (∀ a b, cl a = cl b → sys a = sys b) ∧
      ∀ a, (D.β (cl a)).map (·⁻¹) = sys a w := by
  obtain ⟨hfin, hN⟩ := finite_image_of_card_le Sig Iso sys hiso N hcard
  refine ⟨⟨↥(sys '' Sig), hfin, fun s => (s.1 w).map (·⁻¹), ?_, ?_, ?_, ?_, ?_⟩, hN,
    fun a => ⟨sys a, a, a.2, rfl⟩, fun a b h => congrArg Subtype.val h, fun a => ?_⟩
  · rintro ⟨_, a, ha, rfl⟩
    simpa using hn a ha
  · intro σ
    have hmem : ∀ s : ↥(sys '' Sig), (fun v => (s.1 v).map σ) ∈ sys '' Sig := by
      rintro ⟨_, a, ha, rfl⟩
      obtain ⟨b, hb, h⟩ := hconj σ a ha
      exact ⟨b, hb, funext h⟩
    let F : ↥(sys '' Sig) → ↥(sys '' Sig) := fun s => ⟨_, hmem s⟩
    have hF : Function.Injective F := by
      intro s s' h
      refine Subtype.ext (funext fun v => ?_)
      exact Multiset.map_injective σ.injective (congrFun (congrArg Subtype.val h) v)
    refine ⟨Equiv.ofBijective F (Finite.injective_iff_bijective.1 hF), fun s => ?_⟩
    simp [F, Multiset.map_map]
  · rintro ⟨_, a, ha, rfl⟩
    exact (hpure a ha).inv hq
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    exact (hint a ha c hc).1 k hk
  · rintro k hk ⟨_, a, ha, rfl⟩ b hb
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hb
    rw [inv_inv]
    exact (hint a ha c hc).2 k hk
  · simp [Multiset.map_map]

end UpperTheory.GalN.V.Win
end
end
