module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.ExplicitConstants.SplitCharY
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.ExistsSqEqNegOfDiscr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.BcStmt
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br

def SelfIso : Prop :=
  StrongMultOneReal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ), 1 ≤ a → ∀ (π : TR.CuspSub F a) (η : HChar F),
    η ^ 2 = 1 → SelfTw π.HasSat η → IsoTwist π η

def BcAtt0 : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      (π.IsRegAlg → (CG.mk P).IsRegAlg) ∧ (AttR ι r π → IsSSRep (r.comp (Bc.res F Ω E)) → AttC ι (r.comp (Bc.res F Ω E)) P)

def BcConj0 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC0 π P →
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (Bc.cPl w) B

def BcDual0 : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ), 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.Polarized χ → IsBC0 π P →
    ∃ χ' : HChar (maximalRealSubfield K), (∀ v v' : InfinitePlace (maximalRealSubfield K), χ'.locInf v (-1) = χ'.locInf v' (-1)) ∧
      GlobalTheory.ContraPair.DualIsConjBy P (compNorm K χ')

def PlaceOf : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i →
    (∀ x : F, i (algebraMap F _ x) = algebraMap K _ (algebraMap F K x)) →
    w.under (𝓞 F) = v ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ IsPlaceOver A w ∧
      PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i

def WdAway : Prop :=
  ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i →
    ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)),
    ∀ (x : WD h) (y : WD h'), IsWDOf ι r x → IsWDOf ι (r.comp (Bc.res F Ω K)) y → WDRel (RingEquiv.refl Ω) x y

def RecInv : Prop :=
  GlobalTheory.Published.LocalLanglandsGL → ∀ (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K),
    PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (v.adicCompletion F)))
    (σ' : SmIrr (GL (Fin n) (w.adicCompletion K))) rc rc', IsRec h rc → IsRec h' rc' →
    WDRel (RingEquiv.refl Ω) (rc (algNorm σ)) (rc' (algNorm σ')) →
    ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

def SplitOf : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ExC → ExR →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ) [Fact (n = 2)], 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.IsRegAlg → π.Polarized χ →
      IsBC0 π P → SplitIso π P

end UpperTheory.V.Br
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
open UpperTheory.V.Af

theorem UpperTheory.V.Br.twCard :
    UpperTheory.V.Br.TwCard := by
  intro Γ k _ _ n r hirr S hS
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Submodule.eq_bot_of_subsingleton) hirr.1
    · exact h
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  choose! g hg using hS
  have key : ∀ δ ∈ S, ∀ s, ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
      = ((δ s : kˣ) : k) • ((r s : Matrix (Fin n) (Fin n) k) * (g δ : Matrix (Fin n) (Fin n) k)) := by
    intro δ hδ s
    have h1 := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) * (g δ : Matrix (Fin n) (Fin n) k))
      (hg δ hδ s)
    simp only [tw_val, Units.val_mul, mul_assoc, Units.inv_mul, mul_one] at h1
    rw [← h1, smul_mul_assoc]
  have hli : LinearIndependent k (fun δ : S => ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc δ0
    have hsum : ∀ s, ∑ δ : S, (c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      intro s
      have h2 : (r s : Matrix (Fin n) (Fin n) k) *
          ∑ δ : S, (c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
        rw [Finset.mul_sum]
        have e : ∑ δ : S, (r s : Matrix (Fin n) (Fin n) k) *
            ((c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
            (∑ δ : S, c δ • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) * (r s : Matrix (Fin n) (Fin n) k) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun δ _ => ?_
          rw [smul_mul_assoc, key δ.1 δ.2 s, mul_smul_comm, mul_smul]
        rw [e, hc, zero_mul]
      have h3 := congrArg (fun A => (((r s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * A) h2
      simpa [← mul_assoc] using h3
    have hD := (linearIndependent_monoidHom Γ k).comp (fun δ : S => (Units.coeHom k).comp δ.1)
      (fun a b hab => Subtype.ext (MonoidHom.ext fun s => Units.ext (DFunLike.congr_fun hab s)))
    rw [Fintype.linearIndependent_iff] at hD
    have hz : ∀ i j, ∀ δ : S, c δ * ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 := by
      intro i j
      apply hD
      funext s
      have e := congrFun (congrFun (hsum s) i) j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, MonoidHom.coe_comp,
        Units.coeHom_apply, Pi.zero_apply]
      rw [← e]
      exact Finset.sum_congr rfl fun δ _ => by ring
    by_contra hc0
    have h0 : ((g δ0 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      ext i j
      exact (mul_eq_zero.mp (hz i j δ0)).resolve_left hc0
    exact (g δ0).ne_zero h0
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, Fintype.card_coe] at hcard
  rw [sq]
  exact hcard
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ResTwo
open UpperTheory.V UpperTheory.V.Af

private theorem schur_scalar_of_commutes_irreducible {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (g : Matrix (Fin n) (Fin n) k)
    (hg : ∀ s, g * (r s : Matrix (Fin n) (Fin n) k) = (r s : Matrix (Fin n) (Fin n) k) * g) :
    ∃ c : k, g = c • (1 : Matrix (Fin n) (Fin n) k) := by
  obtain ⟨hne, -, hmin⟩ := hirr
  have hnt : Nontrivial (Fin n → k) := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' g : Module.End k (Fin n → k))
  refine ⟨c, ?_⟩
  rcases hmin (Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c) le_top (by
      intro t v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]) with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c := by
      rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]; simp

private theorem part_two {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] {n : ℕ} (φ : Γ' →* Γ)
    (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r r' : Γ →* GL (Fin n) k)
    (hirr : IsIrr (r.comp φ)) (hiso : RepIso (r.comp φ) (r'.comp φ)) : RepIso r r' ∨ RepIso (tw r δ) r' := by
  obtain ⟨g, hg⟩ := hiso
  have hH : ∀ s, δ s = 1 → r' s = g * r s * g⁻¹ := by
    intro s hs
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hg x
  by_cases hall : ∀ s, δ s = 1
  · exact Or.inl ⟨g, fun s => hH s (hall s)⟩
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = (r t)⁻¹ * g⁻¹ * r' t * g := ⟨_, rfl⟩
  have hrt : r' t = g * (r t * u) * g⁻¹ := by rw [hu]; group
  have hcomm : ∀ s, δ s = 1 → u * r s = r s * u := by
    intro s hs
    have e1 := hH s hs
    have e2 := hH (t * s * t⁻¹) (by simp [hs])
    simp only [map_mul, map_inv] at e2
    rw [e1, hrt] at e2
    have e3 : u * r s = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * r s * g⁻¹) * (g * (r t * u) * g⁻¹)⁻¹) * g * r t * u := by
      group
    rw [e3, e2]; group
  obtain ⟨c, hc⟩ := schur_scalar_of_commutes_irreducible (r.comp φ) hirr (u : Matrix (Fin n) (Fin n) k) (by
    intro x
    have := hcomm (φ x) ((h1 _).2 ⟨x, rfl⟩)
    simpa using congrArg Units.val this)
  have hcen : ∀ a : GL (Fin n) k, u * a = a * u := by
    intro a
    apply Units.ext
    simp [hc]
  have huu : u * u = 1 := by
    have e2 := hH (t * t) (by simp [ht'])
    simp only [map_mul] at e2
    rw [hrt] at e2
    have e3 : u * r t * u = (r t)⁻¹ * g⁻¹ * (g * (r t * u) * g⁻¹ * (g * (r t * u) * g⁻¹)) * g := by group
    rw [e2, hcen (r t)] at e3
    calc u * u = (r t)⁻¹ * (r t * u * u) := by group
      _ = 1 := by rw [e3]; group
  have hneg : ∀ s, δ s = -1 → r' s = g * (u * r s) * g⁻¹ := by
    intro s hs
    have e1 := hH (t⁻¹ * s) (by simp [hs, ht'])
    have e2 : r' s = r' t * r' (t⁻¹ * s) := by rw [← map_mul]; simp
    rw [e2, e1, hrt, ← hcen (r t), map_mul, map_inv]; group
  have hu2 : u = 1 ∨ u = -1 := by
    have e := congrArg Units.val huu
    rw [Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.val_one] at e
    have hn : Nonempty (Fin n) := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      exact hirr.1 (Subsingleton.elim _ _)
    obtain ⟨i⟩ := hn
    have e' := congrFun (congrFun e i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e'
    rcases mul_self_eq_one_iff.1 e' with h | h
    · left; apply Units.ext; simp [hc, h]
    · right; apply Units.ext; simp [hc, h]
  rcases hu2 with h | h
  · refine Or.inl ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · exact hH s hs
    · rw [hneg s hs, h, one_mul]
  · refine Or.inr ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · rw [hH s hs]; congr 2; apply Units.ext; simp [tw_val, hs]
    · rw [hneg s hs, h]; congr 2; apply Units.ext; simp [tw_val, hs]

private theorem part_one {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (φ : Γ' →* Γ)
    (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range) (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (hn : ¬ RepIso r (tw r δ)) : IsIrr (r.comp φ) := by
  refine ⟨hirr.1, fun _ _ _ => trivial, ?_⟩
  intro W _ hW
  by_contra hcon
  push Not at hcon
  obtain ⟨hW0, hW1⟩ := hcon
  apply hn
  by_cases hall : ∀ s, δ s = 1
  · refine ⟨1, fun s => ?_⟩
    apply Units.ext; simp [tw_val, hall s]
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) := fun s => Matrix.toLin' (r s : Matrix (Fin n) (Fin n) k)
  have hmul : ∀ a b v, ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v
    simp [ρ, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
  have a1 : ∀ s, δ s = 1 → ∀ v ∈ W, ρ s v ∈ W := by
    intro s hs v hv
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hW x v hv
  have a2 : ∀ s, δ s = -1 → ∀ v ∈ W, ρ s v ∈ W.map (ρ t) := by
    intro s hs v hv
    refine ⟨ρ (t⁻¹ * s) v, a1 _ (by simp [hs, ht']) v hv, ?_⟩
    rw [hmul]; simp
  have a3 : ∀ s, δ s = 1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W.map (ρ t) := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a2 _ (by simp [hs, ht']) v hv
  have a4 : ∀ s, δ s = -1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a1 _ (by simp [hs, ht']) v hv
  have hinf : W ⊓ W.map (ρ t) = ⊥ := by
    refine (hirr.2.2 _ le_top ?_).resolve_right (fun h => hW1 (top_le_iff.1 (h ▸ inf_le_left)))
    intro s v hv
    rcases h2 s with hs | hs
    · exact ⟨a1 s hs v hv.1, a3 s hs v hv.2⟩
    · exact ⟨a4 s hs v hv.2, a2 s hs v hv.1⟩
  have hsup : W ⊔ W.map (ρ t) = ⊤ := by
    refine (hirr.2.2 _ le_top ?_).resolve_left (fun h => hW0 (le_bot_iff.1 (h ▸ le_sup_left)))
    intro s v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    show ρ s (a + b) ∈ _
    rw [map_add (f := _)]
    rcases h2 s with hs | hs
    · exact Submodule.add_mem_sup (a1 s hs a ha) (a3 s hs b hb)
    · rw [add_comm]; exact Submodule.add_mem_sup (a4 s hs b hb) (a2 s hs a ha)
  have hc : IsCompl W (W.map (ρ t)) := IsCompl.of_eq hinf hsup
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.ofIsCompl hc W.subtype (-(W.map (ρ t)).subtype)
  have p1 : ∀ v ∈ W, P v = v := fun v hv => LinearMap.ofIsCompl_apply_left hc (u := ⟨v, hv⟩)
  have p2 : ∀ v ∈ W.map (ρ t), P v = -v := fun v hv => LinearMap.ofIsCompl_apply_right hc (v := ⟨v, hv⟩)
  have hdec : ∀ v : Fin n → k, ∃ a ∈ W, ∃ b ∈ W.map (ρ t), a + b = v := fun v =>
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hPP : P ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    simp [p1 a ha, p2 b hb]
  have hPr : ∀ s, (δ s : k) • (ρ s ∘ₗ P) = P ∘ₗ ρ s := by
    intro s
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rcases h2 s with hs | hs
    · simp [p1 a ha, p2 b hb, hs, p1 _ (a1 s hs a ha), p2 _ (a3 s hs b hb)]
    · simp [p1 a ha, p2 b hb, hs, p2 _ (a2 s hs a ha), p1 _ (a4 s hs b hb), add_comm]
  have hM : LinearMap.toMatrix' P * LinearMap.toMatrix' P = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPP, LinearMap.toMatrix'_id]
  refine ⟨⟨LinearMap.toMatrix' P, LinearMap.toMatrix' P, hM, hM⟩, fun s => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  have := congrArg LinearMap.toMatrix' (hPr s)
  simp only [map_smul, LinearMap.toMatrix'_comp, ρ, LinearMap.toMatrix'_toLin'] at this
  simp only [Units.val_mul, tw_val, Matrix.smul_mul]
  exact this

theorem UpperTheory.V.Br.resTwo :
    UpperTheory.V.Br.ResTwo := by
  intro Γ Γ' k _ _ _ _ _ n φ δ h1 h2 r
  exact ⟨part_one φ δ h1 h2 r, fun r' => part_two φ δ h1 h2 r r'⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SatOfPol
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Matrix

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G V} {ρ : Representation ℂ G W} {K : Subgroup G} {h : G → ℂ} {x : V} {y : W}

private theorem pair_heckeVec (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed σ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G ≃* G) (hθ : ∀ k, k ∈ K ↔ θ k ∈ K)
    (hi : ∀ g v w, β (σ (θ g) v) (ρ g w) = β v w)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t⁻¹ = t ∧ g = a * t * b) :
    β (heckeVec σ K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y := fun a ha b hb t => by
    obtain ⟨a, rfl⟩ := θ.surjective a
    rw [map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)
  have inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y) := fun t => by
    rw [← hi t⁻¹ x (ρ t y)]; simp
  have e1 := (β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]

private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : W →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : W) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in
private theorem sat_eq_of_pair {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hρ : IsSmooth ρ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n g) x) (ρ g y) = β x y)
    {x : V} {B C : Multiset ℂˣ} (hx : IsSatVecGL w σ x B) (hC : HasSatGL w ρ C) : B = C := by
  classical
  have hKc : IsCompact (KGL w (n := n) : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  obtain ⟨y₀, hy₀⟩ : ∃ y, β x y ≠ 0 := by
    by_contra hn
    exact hx.1 (hβ x fun y => by_contra fun h => hn ⟨y, h⟩)
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨y, hyK, hy⟩ := exists_fixed_pair hρ hKc (β x) (fun k hk v => by
    have := hi k x v
    rwa [GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ ((hK k).1 hk)] at this) y₀
  have hne : β x y ≠ 0 := hy ▸ hy₀
  have hy' := hC.2 y hyK fun h0 => hne (by rw [h0, map_zero])
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  refine eq_of_satEig_eq (qV_ne_zero w) hx.2.2.1 hy'.2.2.1 fun j hj => ?_
  have key := pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 hyK β
    (GlobalTheory.LFun.ConjPlace.invT c n) hK hi
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)
  rw [hx.2.2.2 _ hp j hj, hy'.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul] at key
  exact mul_right_cancel₀ hne key

open Neutral.B1 ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published

private theorem conj_locGL {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) ((cPl w).adicCompletion E)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g) =
      locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cPl v)) (locGL E a (cPl w) g)) := fun v => rfl
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin a) (v.adicCompletion E) => u.val i j) (key2 v)

private theorem conjLoc_surjective {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (GlobalTheory.ThetaPull.cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (GlobalTheory.ThetaPull.cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem UpperTheory.V.Br.satOfPol :
    UpperTheory.V.Br.SatOfPol := by
  intro E _ _ _ n P ψ hd w hu B B' hB hB'
  have hu' : (ψ⁻¹).UnrAt w := fun x hx => by
    have h3 : ψ.loc w x = 1 := hu x hx
    exact (congrArg Inv.inv h3).trans inv_one
  have hC := GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' hB
  rw [CG.hasSat_mk] at hB'
  let c : (cPl w).adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surjective w⟩
  have hq : Formalism.UG.qV E w = Formalism.UG.qV E (cPl w) := by
    change Ideal.absNorm w.asIdeal = Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv w).asIdeal
    rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
    rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
    exact (Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)) w.asIdeal (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)
      (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv).symm
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB'
  have hx' := GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c (conjLoc_spec _ w).2.2 hq hx
  obtain ⟨β, -, hr, hf, -⟩ := hd
  refine sat_eq_of_pair ((P.twist ψ⁻¹).isSmooth_locRep w) β.flip hr (fun g u v => ?_) hx' hC
  obtain ⟨g, rfl⟩ : ∃ g', Matrix.GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g' = g :=
    ⟨Matrix.GeneralLinearGroup.map c.symm.toRingHom g, Units.ext (Matrix.ext fun i j => c.apply_symm_apply _)⟩
  have e1 : GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      GlobalTheory.LFun.ConjPlace.invT c n g := Units.ext (Matrix.ext fun i j => by
    rw [GlobalTheory.LFun.ConjPlace.invT_val, GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]; rfl)
  rw [e1]
  change β ((P.twist ψ⁻¹).locRep w _ v) (P.locRep (cPl w) ((GlobalTheory.LFun.ConjPlace.invT c n).symm (GlobalTheory.LFun.ConjPlace.invT c n g)) u) = β v u
  rw [MulEquiv.symm_apply_apply, CuspSub.locRep_eq, CuspSub.locRep_eq, ← conj_locGL, ← hf (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) v u]
  have e2 : Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) = locGL E n (cPl w) g :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.ThetaPull.cFin_cFin _)
  exact congrArg (fun k => β _ (P.op (.fin k) u)) e2.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.QuadFam
open NumberField

private theorem quadFam_one (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(p : ℤ) := by
  obtain ⟨K, hF, hN, hr, hd⟩ := KStar.Consta.exists_quadField hp h4
  have hp0 : p ≠ 0 := hp.ne_zero
  have htc : IsTotallyComplex K :=
    (KStar.Choice.exists_sq_eq_neg_of_discr hr hp0 hd).2
  have hq : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hr }
  exact ⟨K, hF, hN, IsCMField.ofCMExtension ℚ K, hr, hd⟩

theorem UpperTheory.V.Br.quadFam :
    UpperTheory.V.Br.QuadFam := by
  intro N
  have hS : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨p, hpn, hpp, hmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq n (q := 4) (a := 3) (by norm_num) (by norm_num)
    exact ⟨p, ⟨hpp, hmod⟩, hpn⟩
  let e := hS.natEmbedding
  let q : Fin N → ℕ := fun i => (e i.val).1
  have hq : ∀ i, (q i).Prime ∧ q i % 4 = 3 := fun i => (e i.val).2
  have hinj : ∀ i j, q i = q j → i = j := fun i j h =>
    Fin.ext (e.injective (Subtype.ext h))
  choose K hF hN hC hr hd using fun i => quadFam_one (q i) (hq i).1 (hq i).2
  refine ⟨K, hF, hN, hC, hr, ?_⟩
  intro i j hij
  rw [hd i, hd j]
  have hne : q i ≠ q j := fun h => hij (hinj i j h)
  have hcop : Nat.Coprime (q i) (q j) := (Nat.coprime_primes (hq i).1 (hq j).1).2 hne
  exact (Nat.isCoprime_iff_coprime.2 hcop).neg_neg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SignNe
open NumberField UpperTheory.V.Af.Bc

private theorem range_res_eq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] :
    (res F Ω K).range = (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨τ, rfl⟩ y hy
    obtain ⟨k, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact τ.commutes k
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) fun k => h _ (AlgHom.mem_fieldRange.mpr ⟨k, rfl⟩), ?_⟩
    ext y
    rfl

private theorem equiv_of_range {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω] (K K' : Type) [Field K] [Algebra F K]
    [Algebra K Ω] [IsScalarTower F K Ω] [Field K'] [Algebra F K'] [Algebra K' Ω] [IsScalarTower F K' Ω]
    (h : (res F Ω K).range = (res F Ω K').range) : Nonempty (K ≃ₐ[F] K') := by
  have hK := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K Ω).fieldRange
  have hK' := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K' Ω).fieldRange
  rw [range_res_eq, range_res_eq] at h
  have he : (IsScalarTower.toAlgHom F K Ω).fieldRange = (IsScalarTower.toAlgHom F K' Ω).fieldRange := by
    rw [← hK, ← hK', h]
  have he' : (IsScalarTower.toAlgHom F K Ω).range = (IsScalarTower.toAlgHom F K' Ω).range := by
    rw [← AlgHom.fieldRange_toSubalgebra, ← AlgHom.fieldRange_toSubalgebra, he]
  exact ⟨(AlgEquiv.ofInjectiveField _).trans
    ((Subalgebra.equivOfEq _ _ he').trans (AlgEquiv.ofInjectiveField _).symm)⟩

theorem UpperTheory.V.Br.signNe :
    UpperTheory.V.Br.SignNe := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ hK hcop heq
  obtain ⟨e⟩ := equiv_of_range K K' heq
  rw [← NumberField.discr_eq_discr_of_algEquiv (K := K) e, isCoprime_self, Int.isUnit_iff] at hcop
  have := NumberField.abs_discr_gt_two (K := K) (by omega)
  rcases hcop with h | h <;> rw [h] at this <;> norm_num at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotMove
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst UpperTheory.V UpperTheory.V.Af
open scoped Pointwise

theorem UpperTheory.V.Br.potMove :
    UpperTheory.V.Br.PotMove := by
  intro F Ω _ _ _ _ _ l _ n r A A' g hg hA
  obtain ⟨O, i1, i2, i3, Bw, hj, LL', r', ⟨hle, hmap⟩, K', hK', hcr⟩ := hA
  have hmem : ∀ s : G F Ω, s ∈ Dec (F := F) A' ↔ g * s * g⁻¹ ∈ Dec (F := F) A := fun s => by
    have hgA : g • A' = A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hg]
      simp [AlgEquiv.smul_def]
    rw [mem_Dec, mem_Dec, ← hgA, mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff]
  let φ : ↥(Dec (F := F) A') ≃* ↥(Dec (F := F) A) :=
    { toFun := fun s => ⟨g * s * g⁻¹, (hmem s).1 s.2⟩
      invFun := fun t => ⟨g⁻¹ * t * g, (hmem _).2 (by
        have e : g * (g⁻¹ * (t : G F Ω) * g) * g⁻¹ = t := by group
        rw [e]; exact t.2)⟩
      left_inv := fun s => Subtype.ext (by dsimp only; group)
      right_inv := fun t => Subtype.ext (by dsimp only; group)
      map_mul' := fun s t => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφ : Continuous φ :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hφs : Continuous φ.symm :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hjE : ∀ x : F, Bw.j (g (algebraMap F Ω x)) = Bw.j (algebraMap F Ω x) := fun x => by
    rw [AlgEquiv.commutes]
  let Bw' : LocBridge l F Ω (Dec (F := F) A') O :=
    { Kw := Bw.Kw, j := Bw.j.comp (g : Ω →+* Ω)
      j_E := fun x => by
        change Bw.j (g (algebraMap F Ω x)) ∈ _
        rw [hjE]; exact Bw.j_E x
      j_dense := Bw.j_dense.trans (closure_mono (by
        rintro _ ⟨x, rfl⟩
        exact ⟨x, hjE x⟩))
      e := φ.trans Bw.e
      e_cont := Bw.e_cont.comp hφ, e_symm_cont := hφs.comp Bw.e_symm_cont
      e_comm := fun s x => by
        refine (Bw.e_comm (φ s) (g x)).trans ?_
        change Bw.j ((g * (s : G F Ω) * g⁻¹) (g x)) = Bw.j (g ((s : G F Ω) x))
        simp
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  have h1 : PotCrysAt (r.comp (MulAut.conj g).toMonoidHom) A' := by
    refine ⟨O, i1, i2, i3, Bw', fun x => (hg x).trans (hj (g x)), LL', r'.comp φ.toMonoidHom,
      ⟨hle, MonoidHom.ext fun s => DFunLike.congr_fun hmap (φ s)⟩, K', hK', ?_⟩
    have e : Bw'.repE LL' (r'.comp φ.toMonoidHom) = Bw.repE LL' r' := by
      refine MonoidHom.ext fun t => ?_
      simp [LocBridge.repE, Bw']
    rw [e]
    exact hcr
  refine h1.of_iso ⟨(r g)⁻¹, fun s => ?_⟩
  simp [mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.PotRes
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal UpperTheory.V.Loc UpperTheory.V.Af UpperTheory.V.Af.Bc NumberField

private theorem ex_bridge {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} (j : Ω →+* Om l) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) :
    ∃ (L : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL L)), Bw.j = j := by
  let K : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)),
    GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap E Ω))⟩
  have := K.2
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := E) hj K rfl
  exact ⟨⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩,
    { Kw := K
      j := j
      j_E := fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
      j_dense := GlobalTheory.PlaceBridge.adjoin_range_subset_closure (j.comp (algebraMap E Ω))
      e := e
      e_cont := he
      e_symm_cont := he'
      e_comm := hec
      LL := ⟨IntermediateField.normalClosure ℚ_[l] K.1 (PadicAlgCl l), inferInstance⟩
      LL_split := fun τ x => AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩
      eO := RingEquiv.refl _
      eO_alg := fun _ => rfl
      eO_cont := continuous_id
      eO_symm_cont := continuous_id }, rfl⟩

theorem UpperTheory.V.Br.potRes :
    UpperTheory.V.Br.PotRes := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ n r A hr
  obtain ⟨O, i1, i2, i3, Bw, hj, hp⟩ := hr
  obtain ⟨L, Bw', hBj⟩ := ex_bridge (E := K) (A := A) Bw.j hj
  refine ⟨↥(OL L), inferInstance, inferInstance, inferInstance, Bw', fun x => by rw [hBj]; exact hj x, ?_⟩
  obtain ⟨L₀, r₀, hm₀, -⟩ := id hp
  have hm₁ := hm₀.enlarge (L₂ := GlobalTheory.Pst.supExt L₀ Bw'.LL) le_sup_left
  have hL : Bw'.LL.1 ≤ (GlobalTheory.Pst.supExt L₀ Bw'.LL).1 := le_sup_right
  obtain ⟨r₁, hm, hc⟩ : ∃ r₁, GlobalTheory.Pst.IsModel Bw (r.comp (Dec (F := F) A).subtype) (GlobalTheory.Pst.supExt L₀ Bw'.LL) r₁ ∧
      Bw.IsPotCrysE (PP l) _ r₁ := ⟨_, hm₁, (hm₁.isPotCrysAt_iff (PP l)).1 hp⟩
  clear hm₁
  generalize GlobalTheory.Pst.supExt L₀ Bw'.LL = L₁ at hL r₁ hm hc
  obtain ⟨K₁, h₁, hc⟩ := hc
  have hmem : ∀ σ : G K Ω, σ ∈ Dec (F := K) A ↔ res F Ω K σ ∈ Dec (F := F) A := fun σ => by
    rw [mem_Dec, mem_Dec]
    exact Iff.rfl
  let f : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A) :=
    ((res F Ω K).comp (Dec (F := K) A).subtype).codRestrict _ fun σ => (hmem σ).1 σ.2
  refine ⟨L₁, r₁.comp f, ⟨hL, MonoidHom.ext fun g => DFunLike.congr_fun hm.2 (f g)⟩, ?_⟩
  have h₂ : K₁.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1 := le_sup_left
  have h₃ : Bw'.Kw.1 ≤ (GlobalTheory.Pst.supExt K₁ Bw'.Kw).1 := le_sup_right
  refine ⟨_, h₃, ?_⟩
  obtain ⟨T⟩ := tiedP l
  have hres := (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (PP l) (AIP l) T K₁ _ L₁ h₂ _ _).1 hc
  convert hres using 1
  refine MonoidHom.ext fun g => ?_
  have hg : f (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) =
      Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g)) := by
    refine Subtype.ext (AlgEquiv.ext fun x => Bw.j.injective ?_)
    have a1 := Bw'.e_comm (Bw'.e.symm (Subgroup.inclusion (GK_le h₃) g)) x
    have a2 := Bw.e_comm (Bw.e.symm (Subgroup.inclusion (GK_le h₁) (Subgroup.inclusion (GK_le h₂) g))) x
    rw [MulEquiv.apply_symm_apply] at a1 a2
    rw [hBj] at a1
    exact a1.symm.trans a2
  exact congrArg (fun s => Matrix.toLinAlgEquiv' (r₁ s : Matrix (Fin n) (Fin n) ↥L₁.1)) hg
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharConj
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af
open GlobalTheory.CuspRep (Af finId pFin)
open ReciprocityTheory.Neutral.Bridge.HCFR (infIdele)

section

variable {F : Type} [Field F] [NumberField F]

private theorem cc_finId_local (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)) = localIdele F w x := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    simp
  · change (1 : Af F) - 1 + _ = _
    rw [sub_self, zero_add]
    rfl

private theorem cc_pFin_inf (v : InfinitePlace F) (x : (v.Completion)ˣ) :
    Units.map (pFin F).toMonoidHom (infIdele F v x) = 1 := Units.ext rfl

private theorem cc_split (k : Fˣ) :
    infDiag k * finId F (Units.map (algebraMap F (Af F)).toMonoidHom k) = diagUnits F k := by
  classical
  have h : ((infDiag k : Ideles F) : AdeleRing (𝓞 F) F) = (algebraMap F (InfiniteAdeleRing F) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace F, w.Completion) →* AdeleRing (𝓞 F) F :=
      MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
    change ∏ w : InfinitePlace F, ι (Pi.mulSingle w (algebraMap F w.Completion k)) =
      ι (fun w => algebraMap F w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [Units.val_mul, h]
  refine Prod.ext ?_ ?_
  · change algebraMap F (InfiniteAdeleRing F) k * (1 - 0 + 0) = algebraMap F (InfiniteAdeleRing F) k
    simp
  · change (1 : Af F) * (1 - 1 + algebraMap F (Af F) k) = algebraMap F (Af F) k
    simp

private theorem cc_inf_fixed (hF : Module.finrank ℚ F = 1) (χ : HChar F) (a : (F →+* ℂ) → ℤ) (h : IsAlgPos χ a)
    (σ : ℂ ≃+* ℂ) (k : Fˣ) : σ ((χ.inf k : ℂˣ) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
  have hs : Function.Surjective (algebraMap ℚ F) := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hF).2
  obtain ⟨q, hq⟩ := hs (k : F)
  have h1 := h (k ^ 2) fun φ => by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_two_pos_of_ne_zero ((map_ne_zero φ).2 k.ne_zero)
  have h2 : ((χ.inf k : ℂˣ) : ℂ) ^ 2 = (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) ^ 2 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, h1, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun φ _ => ?_
    rw [Units.val_pow_eq_pow_val, map_pow, ← hq, eq_ratCast, map_ratCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, mul_comm]
  have h3 : σ (∏ φ : F →+* ℂ, (q : ℂ) ^ a φ) = ∏ φ : F →+* ℂ, (q : ℂ) ^ a φ := by
    simp only [map_prod, map_zpow₀, map_ratCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with e | e
  · rw [e, h3]
  · rw [e, map_neg, h3]

end

theorem UpperTheory.V.Br.charConj :
    UpperTheory.V.Br.CharConj := by
  intro F _ _ hF χ a ha σ
  have hσ : ∀ k : Fˣ, σ ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) =
      ((χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) : ℂˣ) : ℂ) := fun k => by
    have h1 := χ.2.2 k
    rw [← cc_split k, map_mul] at h1
    have h2 : χ.1 (finId F (Units.map (algebraMap F (Af F)).toMonoidHom k)) = (χ.inf k)⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    rw [h2, Units.val_inv_eq_inv_val, map_inv₀, cc_inf_fixed hF χ a ha σ k]
  let ψ : (Af F)ˣ →* ℂˣ := χ.1.comp (finId F)
  have hψ : Continuous ψ := χ.2.1.comp (GlobalTheory.CuspRep.continuous_finId F)
  let ψ' : (Af F)ˣ →* ℂˣ := (Units.map (σ : ℂ →+* ℂ).toMonoidHom).comp ψ
  have hψ' : Continuous ψ' := by
    refine continuous_of_continuousAt_one ψ' ?_
    have h1 : {u | ψ u = 1} ∈ nhds (1 : (Af F)ˣ) :=
      (GlobalTheory.CuspRep.isOpen_ker_finIdele F ψ hψ).mem_nhds (map_one ψ)
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [h1] with u hu
    change 1 = Units.map _ (ψ u)
    rw [hu, map_one]
  let p := Units.map (pFin F).toMonoidHom
  have hp : Continuous p := Continuous.units_map _ continuous_snd
  let χ' : HChar F := ⟨χ.1 * (ψ.comp p)⁻¹ * ψ'.comp p, (χ.2.1.mul (hψ.comp hp).inv).mul (hψ'.comp hp), fun k => by
    have e : ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = ψ (Units.map (algebraMap F (Af F)).toMonoidHom k) :=
      Units.ext (hσ k)
    change χ.1 _ * (ψ (Units.map (algebraMap F (Af F)).toMonoidHom k))⁻¹ *
      ψ' (Units.map (algebraMap F (Af F)).toMonoidHom k) = 1
    rw [χ.2.2 k, e, one_mul, inv_mul_cancel]⟩
  have hloc : ∀ w x, χ'.loc w x = Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.loc w x) := fun w x => by
    have e := cc_finId_local w x
    change χ.1 (localIdele F w x) * (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x))))⁻¹ *
      Units.map (σ : ℂ →+* ℂ).toMonoidHom (χ.1 (finId F (Units.map (pFin F).toMonoidHom (localIdele F w x)))) = _
    rw [e, mul_inv_cancel, one_mul]
    rfl
  refine ⟨χ', fun v => ?_, fun w hw => ⟨fun x hx => ?_, ?_⟩⟩
  · change χ.1 (infIdele F v (-1)) * (ψ (Units.map (pFin F).toMonoidHom (infIdele F v (-1))))⁻¹ *
      ψ' (Units.map (pFin F).toMonoidHom (infIdele F v (-1))) = χ.1 (infIdele F v (-1))
    rw [cc_pFin_inf, map_one, map_one, inv_one, mul_one, mul_one]
  · rw [hloc, hw x hx, map_one]
  · exact congrArg Units.val (hloc w (atFin w (unif w)))
end
