module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.CompOfEig
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2SmulKey
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.AboveW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PseudoLocalLanglandsDescent

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NonemptyUnitaryHeckeParts
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem UpperTheory.V.Hi.module_structure_of_commuting {A R P G : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Group G]
    (ρ : Representation A G P) (α : R →+* Module.End A P) (hc : ∀ t g z, α t (ρ g z) = ρ g (α t z)) :
    ∃ (_ : Module R P) (ρR : Representation R G P), (∀ (t : R) (z : P), t • z = α t z) ∧ ∀ g z, ρR g z = ρ g z := by
  letI : Module R P := Module.compHom P α
  have hs : ∀ (t : R) (z : P), t • z = α t z := fun _ _ => rfl
  refine ⟨inferInstance,
    { toFun := fun g =>
        { toFun := fun z => ρ g z
          map_add' := fun x y => map_add _ x y
          map_smul' := fun t z => by rw [hs, RingHom.id_apply, hs, hc] }
      map_one' := by ext z; simp
      map_mul' := fun g h => by ext z; simp }, hs, fun _ _ => rfl⟩
theorem UpperTheory.V.Hi.levelUR2ModPack_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V₀ : s.Lev) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V₀.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : Pa.TWBase (Pa.pairOf B.u) J Empty D) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V₀)) (q : ℕ) (w : Fin q → Plc L) (rN : Resid (Pa.globOf r V).frame O n), Pa.Glob.Compat h rN (Pa.residOf r) → ∀ (R : Type) [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair rN R) (A : Type) [CommRing A] [Algebra O A] (e : Pa.abelian₂ O Empty D ≃ₐ[O] A) (lam : A →ₐ[O] R), (∀ k, lam (e (MvPowerSeries.X (.inr k))) = algebraMap O R (b.wt.c k) * (p.ψ (b.wt.v k) (b.wt.i k) (b.wt.γ k) : R) - 1) → ∀ β : R →ₐ[O] B.B, p.Maps β.toRingHom ((Pa.pairOf B.u).D.comap h.p₀) (Pa.pairOf B.u).ψ → ∀ (P : Type) [AddCommGroup P] [Module A P] (ρ : Representation A (GV n w) P) (α : R →+* Module.End A P), (∀ a z, α (lam a) z = a • z) → (∀ t g z, α t (ρ g z) = ρ g (α t z)) → Module.Finite A (fixd ρ (Pa.UIw1 l n w)) → ∀ [((Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)).Normal] (ρ' : Representation A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) (fixd ρ (Pa.UIw1 l n w))), (∀ (u : Pa.UIw n w) f, (ρ' (u : Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w)) f).1 = ρ u f) → Module.Projective (MonoidAlgebra A (Pa.UIw n w ⧸ (Pa.UIw1 l n w).subgroupOf (Pa.UIw n w))) ρ'.asModule → ∀ eM : fixd ρ (Pa.UK n w) ≃+ b.M, (∀ (t : R) (m m' : fixd ρ (Pa.UK n w)), (m' : P) = α t m → eM m' = β t • eM m) → ∀ ι : Qbar l ≃+* ℂ, (∀ z : P, z ≠ 0 → ∃ (x : R →+* Qbar l) (ρx : (Pa.globOf r V).G₀ →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n w) Y) (sp : P →+ Y) (σ : ∀ j, SmIrr (GLw n (w j))), sp z ≠ 0 ∧ Continuous ρx ∧ p.D.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ j, IsoSum (π.comp (Pa.atJ n w j)) ⊤ (σ j)) ∧ ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL (k := (w j).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp V.pr) (rc (algNorm (σ j)))) → ∃ M : Pa.LevMod b h w, M.ClassicalAlt := by
  intro l _ L Ω _ _ _ _ _ _ s V₀ O _ _ _ n r B J D b V h q w rN hcomp R _ _ _ p A _ _ e lam hlam β hβ P _ _ ρ α hα hc hfin
    hN ρ' hρ' hproj eM heM ι hcl
  obtain ⟨modR, ρR, hs, hρR⟩ := UpperTheory.V.Hi.module_structure_of_commuting ρ α hc
  letI algL : Algebra (Pa.abelian₂ O Empty D) R := (lam.toRingHom.comp e.toRingEquiv.toRingHom).toAlgebra
  have halg : ∀ a : Pa.abelian₂ O Empty D, algebraMap (Pa.abelian₂ O Empty D) R a = lam (e a) := fun _ => rfl
  haveI towO : IsScalarTower O (Pa.abelian₂ O Empty D) R := IsScalarTower.of_algebraMap_eq fun x => by
    rw [halg, e.commutes, lam.commutes]
  letI modL : Module (Pa.abelian₂ O Empty D) P := Module.compHom P e.toRingEquiv.toRingHom
  have hL : ∀ (a : Pa.abelian₂ O Empty D) (z : P), a • z = e.toRingEquiv a • z := fun _ _ => rfl
  haveI tow : IsScalarTower (Pa.abelian₂ O Empty D) R P := ⟨fun a t z => by
    rw [Algebra.smul_def, halg, mul_smul, hs, hα, hL]; rfl⟩
  obtain ⟨hF, hP⟩ := UpperTheory.V.Hi.levelUR2ProjTr (Pa.abelian₂ O Empty D) A R P (GV n w) e.toRingEquiv hL ρ ρR hρR
    (Pa.UIw n w) (Pa.UIw1 l n w)
  obtain ⟨ρ'', h1, h2⟩ := hP ρ' hρ' hproj
  have hmem : ∀ z : P, z ∈ fixd ρR (Pa.UK n w) ↔ z ∈ fixd ρ (Pa.UK n w) := fun z =>
    forall_congr' fun u => forall_congr' fun _ => by rw [hρR]
  let φ : fixd ρR (Pa.UK n w) ≃+ fixd ρ (Pa.UK n w) :=
    { toFun := fun v => ⟨v.1, (hmem _).1 v.2⟩
      invFun := fun v => ⟨v.1, (hmem _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let M : Pa.LevMod b h w :=
    { rN := rN
      compat := hcomp
      R := R
      p := p
      segmentWeightExponent := fun k => (halg _).trans (hlam k)
      β := β
      β_pair := hβ
      P := P
      ρ := ρR
      fin := hF hfin
      proj := ⟨hN, ρ'', h1, h2⟩
      eM := φ.trans eM
      eM_smul := fun t m => heM t (φ m) (φ (t • m)) (hs t m.1) }
  refine ⟨M, ι, fun m hm => ?_⟩
  by_contra h0
  obtain ⟨x, ρx, Y, iY, mY, π, sp, σ, hne, hcont, hdet, hsm, hact, hiso, hlg⟩ := hcl m h0
  exact hne (hm
    { θ := x
      rep := ρx
      cont := hcont
      det := hdet
      Y := Y
      π := π
      sp := sp
      sp_smul := fun t y => (congrArg sp (hs t y)).trans (hsm t y)
      sp_act := fun g y => (congrArg sp (hρR g y)).trans (hact g y)
      σ := σ
      iso := hiso
      lg := hlg })
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCompOfEig
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocSub
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
private theorem torusChar_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {a b : Fin n → kˣ →* ℂˣ} (h : torusChar a = torusChar b) : a = b := by
  funext i
  ext x
  have e := DFunLike.congr_fun h (Pi.mulSingle i x)
  simp only [torusChar_apply] at e
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp),
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp)] at e
  simpa using congrArg Units.val e
private theorem sdom_of_step {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (s : Fin n → kˣ) (c : kˣ)
    (h1 : valuation k (c : k) ≤ 1)
    (h2 : ∀ i j : Fin n, i < j → valuation k (s i : k) * valuation k (c : k) < valuation k (s j : k)) :
    Sig.SDom fun i : Fin n => s i * c ^ (n - (i : ℕ)) := by
  intro i j hij
  have hj := j.2
  have hij' : (i : ℕ) < j := hij
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  have hc0 : 0 < valuation k (c : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 c.ne_zero)
  beta_reduce
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  calc valuation k (s i : k) * valuation k (c : k) *
        (valuation k (c : k) ^ (n - (j : ℕ)) * valuation k (c : k) ^ ((j : ℕ) - i - 1))
      ≤ valuation k (s i : k) * valuation k (c : k) * valuation k (c : k) ^ (n - (j : ℕ)) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_right' (pow_le_one' h1 _)
    _ < valuation k (s j : k) * valuation k (c : k) ^ (n - (j : ℕ)) :=
        mul_lt_mul_of_pos_right (h2 i j hij) (pow_pos hc0 _)
private theorem exists_sdom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ d : Fin n → kˣ, Sig.SDom d ∧ Sig.SDom (t * d) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun i => h.elim i, fun i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min
    (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  obtain ⟨x, q, hq, hx⟩ := UpperTheory.V.AlgebraTools.exists_isUnif (k := k)
  have hx1 : valuation k (x : k) < 1 := by
    have h0 : valuation k (q : k) ≤ 1 := q.2
    have hne : valuation k (q : k) ≠ 1 := fun h =>
      hq.not_isUnit ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h)
    rw [← hx]
    exact lt_of_le_of_ne h0 hne
  set c₀ : kˣ := t p.2 * (t p.1)⁻¹ with hc₀
  have hc1 : valuation k (c₀ : k) ≤ 1 := by simpa using hp (p.1, p.1)
  have hcx : valuation k ((c₀ * x : kˣ) : k) < 1 := by
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc1) hx1
  refine ⟨fun i => (c₀ * x) ^ (n - (i : ℕ)), ?_, ?_⟩
  · simpa using sdom_of_step (1 : Fin n → kˣ) (c₀ * x) hcx.le fun i j _ => by simpa using hcx
  · refine sdom_of_step t (c₀ * x) hcx.le fun i j _ => ?_
    have hle : valuation k (t i : k) * valuation k (c₀ : k) ≤ valuation k (t j : k) := by
      refine (mul_le_mul_right (hp (i, j)) (valuation k (t i : k))).trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
    have hj0 : 0 < valuation k (t j : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 (t j).ne_zero)
    rw [Units.val_mul, map_mul, ← mul_assoc]
    calc valuation k (t i : k) * valuation k (c₀ : k) * valuation k (x : k)
        ≤ valuation k (t j : k) * valuation k (x : k) := mul_le_mul_left hle _
      _ < valuation k (t j : k) * 1 := mul_lt_mul_of_pos_left hx1 hj0
      _ = valuation k (t j : k) := mul_one _
theorem UpperTheory.V.Z.Sym.Al.subquotient_prin_series_of_iwahori_eigenvector :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
        IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ ((Sig.Lev.iw k).J n) →
        (∀ d, Sig.SDom d → Hi.dc τ ((Sig.Lev.iw k).J n) ((Sig.Lev.iw k).J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ) := by
  intro H k _ _ _ _ n ψ T _ _ τ hs hi v hv0 hvJ heig
  have hJ : (Sig.Lev.iw k).J n = UpperTheory.V.AlgebraTools.iwC k n ⊤ := (UpperTheory.V.Z.Sym.Sig.link k n).1
  rw [hJ] at hvJ heig
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := UpperTheory.V.AlgebraTools.thetaEx k n ⊤ ℂ T τ hq
  let δ : (Fin n → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  let χ : (Fin n → kˣ) →* ℂˣ := torusChar ψ * δ⁻¹
  let w : Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤) := ⟨v, hvJ⟩
  have hw0 : w ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hsd : ∀ d, Sig.SDom d →
      (θ d : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) w = (χ d : ℂ) • w := by
    intro d hd
    have hD : UpperTheory.V.AlgebraTools.Dom d := fun i j hij => by
      rcases hij.eq_or_lt with rfl | h
      · exact le_rfl
      · exact (hd i j h).le
    rw [hθ d hD]
    refine Subtype.ext ?_
    have h1 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ T τ _ _ (Sig.dg d)
      ((UpperTheory.V.AlgebraTools.heckePairIwC k n ⊤).1 (Sig.dg d))).1 w
    exact h1.trans (heig d hd)
  have ht : ∀ t, (θ t : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) w = (χ t : ℂ) • w := by
    intro t
    obtain ⟨d, hd, htd⟩ := exists_sdom t
    have h1 := hsd d hd
    have h2 := hsd (t * d) htd
    rw [map_mul, Units.val_mul, Module.End.mul_apply, h1, map_smul, map_mul, Units.val_mul, mul_comm, mul_smul] at h2
    exact smul_right_injective _ (Units.ne_zero (χ d)) h2
  have hne : (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (Hi.fixd τ (UpperTheory.V.AlgebraTools.iwC k n ⊤))) (χ t : ℂ)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨w, (Submodule.mem_iInf _).2 fun t => ?_, hw0⟩
    refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩
    simp [ht t]
  obtain ⟨ψ', -, -, e, h2⟩ := UpperTheory.V.AlgebraTools.jqEmbed H.loc.bz k n ⊤ T τ hs hi θ hθ χ hne
  have hψ : ψ' = ψ := torusChar_injective (e.trans (by
    change torusChar ψ * δ⁻¹ * δ = torusChar ψ
    simp))
  exact hψ ▸ h2
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
theorem UpperTheory.V.Z.Sym.Al.comp_sub_of_eigen_vector_fixed_by_j :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π → ∀ w, IsSplitAt w →
        ∀ φ : UA L n → V, φ ≠ 0 → CoefIn φ π → (∀ x ∈ locU n w, cLoc w x ∈ (iw w).J n → ∀ g, φ (g * x) = φ g) →
        ∀ ψ, (∀ i, IsSmoothChar (ψ i)) → EigT φ w (iw w) ψ → CompSub π w ψ := by
  intro H L _ _ _ unr n hn V _ _ π hπ w hw φ h0 hc hJ ψ hψ he
  obtain ⟨s1, s2, -⟩ := secSpec L n w hw
  obtain ⟨τ, hτ⟩ := _root_.UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut H L unr n hn π hπ w hw
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[ℂ] ℂ, f ∘ φ ≠ 0 := by
    obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hg
    exact ⟨f, Function.ne_iff.2 ⟨g, hf⟩⟩
  obtain ⟨p, hp, hp0⟩ := (isoCopy _ _ _ τ.ρ _ τ.irred (isoTypic L n π hπ w hw τ hτ)).1 ⟨f ∘ φ, hc f⟩ fun h => hf (congrArg Subtype.val h)
  refine ⟨hψ, τ, hτ, _root_.UpperTheory.V.Z.Sym.Al.subquotient_prin_series_of_iwahori_eigenvector H _ n ψ _ τ.ρ τ.smooth τ.irred _ hp0 (fun u hu => ?_) fun d hd => ?_⟩
  · rw [← hp]
    congr 1
    exact Subtype.ext (funext fun g => congrArg f (hJ _ (s1 u) (by rwa [s2]) g))
  · rw [← dcMap (iw w) _ τ.ρ p hp, ← map_smul]
    congr 1
    apply Subtype.ext
    have a := dcMap (iw w) ((repOn hπ).comp (secW n w)) ((RU L n).comp (secW n w)) π.subtype (fun _ _ => rfl) (Sig.dg d) ⟨f ∘ φ, hc f⟩
    have b := dcMap (iw w) ((rightReg ℂ (UA L n) V).comp (secW n w)) ((RU L n).comp (secW n w)) (f.compLeft (UA L n))
      (fun _ _ => rfl) (Sig.dg d) φ
    rw [show UpperTheory.V.Hi.dc _ _ _ _ φ = _ • φ from he d hd, map_smul] at b
    exact a.trans b.symm
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2SmulKey
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2BaseEq
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem cu_ext {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) [IsHausdorff I R] {S : Set Γ}
    (hS : Dense S) {f g : Γ → R} (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (h : ∀ x ∈ S, f x = g x) : f = g := by
  funext x
  refine IsHausdorff.eq_iff_smodEq (I := I).2 fun N => ?_
  rw [smul_eq_mul, Ideal.mul_top]
  letI : TopologicalSpace (R ⧸ I ^ N) := ⊥
  haveI : DiscreteTopology (R ⧸ I ^ N) := ⟨rfl⟩
  exact congrFun (Continuous.ext_on hS (hf N).continuous (hg N).continuous fun y hy => by simp only [h y hy]) x
private theorem cu_prod {n : ℕ} {M : Type} [CommGroup M] (f g : Fin n → M)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) : ∀ j, f j = g j := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hj : j ∈ Finset.univ.filter fun i => i ≤ j := by simp
    have e := h j
    rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ g hj,
      Finset.prod_congr rfl (g := g) fun i hi => ih i (by
        rw [Finset.mem_erase, Finset.mem_filter] at hi
        exact lt_of_le_of_ne hi.2.2 hi.1)] at e
    exact mul_right_cancel e
private theorem cu_gen {W M k : Type} [Group W] [Group M] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : W →* kˣ) (ha : Function.Surjective a) (f g : W →* M)
    (h1 : ∀ s (y : Uo k), a s = y → f s = g s) (h2 : ∀ s, a s = Hi.unif k → f s = g s) (s : W) : f s = g s := by
  obtain ⟨p, hp⟩ := ha (Hi.unif k)
  have e := h1 (s * (p ^ ord k (a s))⁻¹) ⟨_, GlAx.val_div_ord (a s)⟩ (by
    rw [map_mul, map_inv, map_zpow, hp]
    exact (div_eq_mul_inv _ _).symm)
  rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, h2 p hp] at e
  exact mul_right_cancel e
private theorem push_cont {Γ O T T₀ : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T]
    [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀] (φ : T →ₐ[O] T₀) {f : Γ → T}
    (hf : Alg.AdicCont (maximalIdeal T) f) : Alg.AdicCont (maximalIdeal T₀) fun g => φ (f g) := fun N => by
  have hle : maximalIdeal T ^ N ≤ (maximalIdeal T₀ ^ N).comap (φ : T →+* T₀) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show φ y ∈ maximalIdeal T₀
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (hf N).comp (Ideal.quotientMap _ (φ : T →+* T₀) hle)
private theorem abs_det {n : ℕ} {G G₀ O T T₀ : Type} [Group G] [TopologicalSpace G] [Group G₀] [TopologicalSpace G₀]
    [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T] [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀]
    (φ : T →ₐ[O] T₀) (p : G →* G₀) (hp : Continuous p) (D : W.GDet n T G) (D₀ : W.GDet n T₀ G₀)
    (hD : D.IsCont (maximalIdeal T)) (hD₀ : D₀.IsCont (maximalIdeal T₀)) {S : Set G} (hS : Dense S)
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map φ.toRingHom = D₀.chi (MonoidAlgebra.single (p g) 1)) :
    D.map φ.toRingHom = D₀.comap p := by
  have e : ∀ g, (D.map φ.toRingHom).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map φ.toRingHom :=
    fun g => by
      rw [← (AlgebraTools.Det.mapApi D _).1]
      simp
  refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
  have h1 := congrFun (cu_ext _ hS (push_cont φ (hD i)) (fun N => (hD₀ i N).comp_continuous hp) fun g hg => by
    simp only [W.GDet.lam, ← h g hg, coeff_map, map_mul, map_pow, map_neg, map_one]
    rfl) g
  simp only [W.GDet.lam, map_mul, map_pow, map_neg, map_one] at h1
  simp only [W.GDet.lam, e, LvR.chi_comap, coeff_map]
  exact h1
private theorem abs_chr {n : ℕ} {Wl Dc O T T₀ k : Type} [Group Wl] [Group Dc] [TopologicalSpace Dc] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T] [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀]
    (φ : T →ₐ[O] T₀) (inc : Wl →* Dc) (hd : DenseRange inc) (art : Wl →* kˣ) (ha : Function.Surjective art)
    (ψ : Fin n → Dc →* Tˣ) (ψ₀ : Fin n → Dc →* T₀ˣ) (c1 : ∀ i, Alg.AdicCont (maximalIdeal T) fun g => (ψ i g : T))
    (c0 : ∀ i, Alg.AdicCont (maximalIdeal T₀) fun g => (ψ₀ i g : T₀)) (ε : Dc → Tˣ) (ε₀ : Dc → T₀ˣ)
    (hε : ∀ g, φ (ε g) = ε₀ g) (u : Fin n → Uo k → T) (u₀ : Fin n → Uo k → T₀) (hu : ∀ i y, φ (u i y) = u₀ i y)
    (γ : Fin n → T) (γ₀ : Fin n → T₀) (hγ : ∀ i, φ (γ i) = γ₀ i)
    (a1 : ∀ i s (y : Uo k), art s = y → (ψ i (inc s) * ε (inc s) ^ (i : ℕ) : Tˣ) * u i y = 1)
    (a0 : ∀ i s (y : Uo k), art s = y → (ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ) : T₀ˣ) * u₀ i y = 1)
    (b1 : ∀ j s, art s = Hi.unif k → ((∏ i with i ≤ j, ψ i (inc s) * ε (inc s) ^ (i : ℕ) : Tˣ) : T) = γ j)
    (b0 : ∀ j s, art s = Hi.unif k → ((∏ i with i ≤ j, ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ) : T₀ˣ) : T₀) = γ₀ j) (i : Fin n) :
    W.pushCh φ.toRingHom (ψ i) = ψ₀ i := by
  have hm : ∀ i g, φ ((ψ i g * ε g ^ (i : ℕ) : Tˣ) : T) = ((W.pushCh φ.toRingHom (ψ i) g * ε₀ g ^ (i : ℕ) : T₀ˣ) : T₀) :=
    fun i g => by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hε]
      rfl
  refine MonoidHom.ext fun g => Units.ext (congrFun (cu_ext _ hd (push_cont φ (c1 i)) (c0 i) ?_) g)
  rintro _ ⟨s, rfl⟩
  refine congrArg Units.val (cu_gen art ha ((W.pushCh φ.toRingHom (ψ i)).comp inc) ((ψ₀ i).comp inc)
    (fun s y hy => ?_) (fun s hs => ?_) s)
  · have e := congrArg φ (a1 i s y hy)
    rw [map_mul, hm, hu, map_one] at e
    have e' := a0 i s y hy
    exact mul_right_cancel (inv_injective (Units.ext
      ((Units.eq_inv_of_mul_eq_one_left e).symm.trans (Units.eq_inv_of_mul_eq_one_left e'))))
  · refine mul_right_cancel (cu_prod (fun i => W.pushCh φ.toRingHom (ψ i) (inc s) * ε₀ (inc s) ^ (i : ℕ))
      (fun i => ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have e := congrArg φ (b1 j s hs)
    rw [Units.coe_prod, map_prod, hγ] at e
    rw [b0 j s hs, ← e, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => (hm i _).symm
private theorem heckePol_map' {T T₀ : Type} [CommRing T] [CommRing T₀] (f : T →+* T₀) (n q : ℕ) (g : ℕ → T) :
    (heckePol n q g).map f = heckePol n q fun j => f (g j) := JEx.heckePol_map _ _ _ _
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2BaseEq_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q₀ τ₀).X.I.T →* Aˣ), (hset Q₀ τ₀).IsWt θ → ∀ (a : (hset Q₀ τ₀).Op → c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q τ₀).Op → (hset Q₀ τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → ∀ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O), (hset Q τ₀).IsWt θ' → @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ → (∀ i, a' i = a (j i)) → ∀ [Fact (CommOn ((hset Q₀ τ₀).MK θ a K₀) ((hset Q₀ τ₀).op A))] [Alg.IsCO c.O ((hset Q₀ τ₀).TK θ a K₀)] [Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A))] [Alg.IsCO c.O ((hset Q τ₀).TK θ' a' K)] (D₀ : W.GDet n ((hset Q₀ τ₀).TK θ a K₀) V₀.frame.G₀) (ψ₀ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* ((hset Q₀ τ₀).TK θ a K₀)ˣ), (hset Q₀ τ₀).IsUniv θ a K₀ (maximalIdeal _) D₀ ψ₀ → ∀ (D : W.GDet n ((hset Q τ₀).TK θ' a' K) V.frame.G₀) (ψ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* ((hset Q τ₀).TK θ' a' K)ˣ), (hset Q τ₀).IsUniv θ' a' K (maximalIdeal _) D ψ → ∀ φ : (hset Q τ₀).TK θ' a' K →ₐ[A] (hset Q₀ τ₀).TK θ a K₀, (∀ i, φ ((hset Q τ₀).gen θ' a' K i) = (hset Q₀ τ₀).gen θ a K₀ (j i)) → D.map φ.toRingHom = D₀.comap p ∧ ∀ v i, W.pushCh φ.toRingHom (ψ v i) = ψ₀ v i := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ A _ _ _ θ _ a K₀ K p hp _ hpr j hj hjw θ' a' _ hθ _ _ _ _ _ D₀ ψ₀ hU₀ D ψ hU φ hφ
  have hAx := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  refine ⟨abs_det (φ.restrictScalars c.O) p hp D D₀ hU.cont hU₀.cont hAx.dense ?_, fun v i => ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    obtain ⟨hw₀, -⟩ := hjw ⟨w, hw⟩ ⟨0, hn⟩
    have e1 := hU.frob ⟨w, hw⟩ B σ hB hσ
    have e0 := hU₀.frob ⟨w, hw₀⟩ B σ hB hσ
    refine ((congrArg (Polynomial.map _) e1).trans ((heckePol_map' _ _ _ _).trans ?_)).trans
      (e0.symm.trans (congrArg (fun g => D₀.chi (MonoidAlgebra.single g 1)) (hpr σ⁻¹).symm))
    refine congrArg (heckePol n (normV w)) (funext fun k => ?_)
    unfold HSet.genW
    split_ifs with h
    · obtain ⟨_, e⟩ := hjw ⟨w, hw⟩ ⟨k - 1, h.2⟩
      exact (hφ _).trans (congrArg ((hset Q₀ τ₀).gen θ a K₀) e)
    · exact map_one _
  · exact abs_chr (k := ((hset Q τ₀).Sl v).adicCompletion L) (φ.restrictScalars c.O) (Subgroup.inclusion (Weil_le_Dec (s.hw v.1))) (UpperTheory.weil_group_dense_in_galois_group L Ω _ _ (s.hw v.1))
      ((hset Q τ₀).art v) (hAx.art_spec v).surj (ψ v) (ψ₀ v) (hU.ψ_cont v) (hU₀.ψ_cont v)
      ((hset Q τ₀).epsV _ v) ((hset Q₀ τ₀).epsV _ v) (fun g => (φ.restrictScalars c.O).commutes _)
      (fun i y => algebraMap A _ (θ' (eV n (hset Q τ₀).Sl v i y))) (fun i y => algebraMap A _ (θ (eV n (hset Q₀ τ₀).Sl v i y)))
      (fun i y => (φ.commutes _).trans (congrArg (fun u : Aˣ => algebraMap A _ (u : A))
        (congrArg (fun t : (hset Q τ₀).X.I.T →* Aˣ => t (eV n (hset Q τ₀).Sl v i y)) hθ)))
      _ _ (fun k => (hφ _).trans (congrArg ((hset Q₀ τ₀).gen θ a K₀) (hj (v, k))))
      (fun i x y h => hU.ψ_unit v i x _ y rfl h) (fun i x y h => hU₀.ψ_unit v i x _ y rfl h)
      (fun k x h => hU.ψ_unif v k x _ rfl h) (fun k x h => hU₀.ψ_unif v k x _ rfl h) i
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem sk_hecke {A M ι ι₀ : Type} [CommRing A] [AddCommGroup M] [Module A M] (Y Y₀ : Submodule A M)
    (op : ι → Module.End A M) (op₀ : ι₀ → Module.End A M) [h : Fact (CommOn Y op)] [h₀ : Fact (CommOn Y₀ op₀)] (j : ι → ι₀)
    (hop : ∀ i, op i = op₀ (j i)) (hm : ∀ f, f ∈ Y ↔ f ∈ Y₀) :
    ∃ φ : heckeAlg Y op →ₐ[A] heckeAlg Y₀ op₀, (∀ i, φ (heckeGen Y op i) = heckeGen Y₀ op₀ (j i)) ∧
      ∀ (t : heckeAlg Y op) (y : Y) (y₀ : Y₀), y.1 = y₀.1 →
        ((t : Module.End A Y) y).1 = ((φ t : Module.End A Y₀) y₀).1 := by
  have hle : Y₀ ≤ Y := fun f hf => (hm f).2 hf
  obtain ⟨φ, h1, h2⟩ := levelUR2HeckeMap A M M ι₀ ι Y₀ Y op₀ op (Submodule.inclusion hle) j
    (Submodule.inclusion_injective hle) fun i y => by
      rw [hop]
      rfl
  refine ⟨φ, h1, fun t y y₀ e => ?_⟩
  have e' : y = Submodule.inclusion hle y₀ := Subtype.ext e
  rw [e', ← h2]
  rfl
private theorem sk_bot {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y Y₀ : Submodule A M}
    (hm : ∀ f, f ∈ Y ↔ f ∈ Y₀) : Y = ⊥ ↔ Y₀ = ⊥ := by
  rw [Submodule.ext hm]
private theorem sk_zero {A M R : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y Y₀ : Submodule A M}
    (hY : Y = ⊥) (ν : R → Y → M) (hν : ∀ t, ν t 0 = 0) (μ : Module.End A Y₀) (t : R) (y : Y) (y₀ : Y₀) (e : y.1 = y₀.1) :
    ν t y = (μ y₀).1 := by
  have h : y = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hY _ y.2)
  have h₀ : y₀ = 0 := Subtype.ext (e.symm.trans (congrArg Subtype.val h))
  rw [h, h₀, hν, map_zero]
  rfl
private theorem sk_comp {O : Type} [CommRing O] {R R₀ T T₀ : Type} [CommRing R] [Algebra O R] [CommRing R₀] [Algebra O R₀]
    [CommRing T] [Algebra O T] [CommRing T₀] [Algebra O T₀] (f : R →ₐ[O] T) (f₀ : R₀ →ₐ[O] T₀) (β : R →ₐ[O] R₀)
    (Φ : T →ₐ[O] T₀) (φ : T →+* T₀) (hφ : ∀ x, Φ x = φ x) {n : ℕ} {G G₀ V : Type} {Γ : V → Type} [Group G] [Group G₀]
    [∀ v, Group (Γ v)] (p : G →* G₀) (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (D₀ : W.GDet n R₀ G₀) (ψ₀ : ∀ v, Fin n → Γ v →* R₀ˣ)
    (hD : D.map β.toRingHom = D₀.comap p) (hψ : ∀ v i, W.pushCh β.toRingHom (ψ v i) = ψ₀ v i)
    (hu : ∀ f g : R →ₐ[O] T₀, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : (D.map f.toRingHom).map φ = (D₀.map f₀.toRingHom).comap p ∧
      ∀ v i, W.pushCh φ (W.pushCh f.toRingHom (ψ v i)) = W.pushCh f₀.toRingHom (ψ₀ v i)) (t : R) :
    φ (f t) = f₀ (β t) := by
  obtain rfl : φ = Φ.toRingHom := RingHom.ext fun x => (hφ x).symm
  have e : Φ.comp f = f₀.comp β := by
    refine hu _ _ ?_ fun v i => ?_
    · have e1 : D.map (Φ.comp f).toRingHom = (D.map f.toRingHom).map Φ.toRingHom := ((CA.d_gmap D).2.1 _ _).symm
      have e2 : D.map (f₀.comp β).toRingHom = (D.map β.toRingHom).map f₀.toRingHom := ((CA.d_gmap D).2.1 _ _).symm
      rw [e1, e2, h.1, hD]
      rfl
    · have e := h.2 v i
      rw [← hψ] at e
      exact e
  exact DFunLike.congr_fun e t
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2SmulKey_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q₀ τ₀).X.I.T →* Aˣ), (hset Q₀ τ₀).IsWt θ →  ∀ (a : (hset Q₀ τ₀).Op → c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q τ₀).Op → (hset Q₀ τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → ∀ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O), (hset Q τ₀).IsWt θ' → @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ → (∀ i, a' i = a (j i)) → (∀ i, (hset Q τ₀).op A i = (hset Q₀ τ₀).op A (j i)) → (∀ f : (hset Q₀ τ₀).X.Fn A m, f ∈ (hset Q τ₀).MK θ' a' K ↔ f ∈ (hset Q₀ τ₀).MK θ a K₀) → ∀ (R₀ R : Type) [CommRing R₀] [Algebra c.O R₀] [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R₀ V₀.frame.G₀) (ψ₀ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* R₀ˣ) (D : W.GDet n R V.frame.G₀) (ψ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* Rˣ) (β : R →ₐ[c.O] R₀), D.map β.toRingHom = D₀.comap p → (∀ v i, W.pushCh β.toRingHom (ψ v i) = ψ₀ v i) → (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D.map f.toRingHom = D.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g) → ∀ μ : R₀ →+* Module.End A ((hset Q₀ τ₀).MK θ a K₀), ((hset Q₀ τ₀).MK θ a K₀ = ⊥ ∨ ∃ (_ : Fact (CommOn ((hset Q₀ τ₀).MK θ a K₀) ((hset Q₀ τ₀).op A))) (_ : Alg.IsCO c.O ((hset Q₀ τ₀).TK θ a K₀)) (f : R₀ →ₐ[c.O] (hset Q₀ τ₀).TK θ a K₀), (hset Q₀ τ₀).IsMap θ a K₀ D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A ((hset Q₀ τ₀).MK θ a K₀))) → ∀ ν : R → (hset Q τ₀).MK θ' a' K → (hset Q₀ τ₀).X.Fn A m, (∀ t, ν t 0 = 0) → (∀ [Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A))] [Alg.IsCO c.O ((hset Q τ₀).TK θ' a' K)], ∃ f : R →ₐ[c.O] (hset Q τ₀).TK θ' a' K, (hset Q τ₀).IsMap θ' a' K D ψ f ∧ ∀ t y, ν t y = ((f t : Module.End A ((hset Q τ₀).MK θ' a' K)) y).1) → ∀ t (y : (hset Q τ₀).MK θ' a' K) (y₀ : (hset Q₀ τ₀).MK θ a K₀), y.1 = y₀.1 → ν t y = (μ (β t) y₀).1 := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ A _ _ _ θ hθ a K₀ K p hp hps hpr j hj1 hj2 θ' a' hθ' hθθ ha hop hm
    R₀ R _ _ _ _ D₀ ψ₀ D ψ β hD hψ hu μ hμ ν hν0 hν t y y₀ hy
  by_cases hne : (hset Q τ₀).MK θ' a' K = ⊥
  · exact sk_zero hne ν hν0 (μ (β t)) t y y₀ hy
  have hAx := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c m τ₀
  haveI hF : Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A)) :=
    ⟨((hiComm L Ω l n c _ hAx A θ' hθ' K).2.2.2 a').1⟩
  obtain ⟨hCO, -⟩ := hiAlg L Ω l n c _ hAx A θ' hθ' a' K hne
  obtain ⟨f, hf, hνf⟩ := hν
  obtain ⟨hF₀, hCO₀, f₀, hf₀, hμf⟩ := hμ.resolve_left fun h => hne ((sk_bot hm).2 h)
  obtain ⟨φ, hg, hφ⟩ : ∃ φ : (hset Q τ₀).TK θ' a' K →ₐ[A] (hset Q₀ τ₀).TK θ a K₀,
      (∀ i, φ ((hset Q τ₀).gen θ' a' K i) = (hset Q₀ τ₀).gen θ a K₀ (j i)) ∧
      ∀ (t : (hset Q τ₀).TK θ' a' K) (y : (hset Q τ₀).MK θ' a' K) (y₀ : (hset Q₀ τ₀).MK θ a K₀), y.1 = y₀.1 →
        ((t : Module.End A ((hset Q τ₀).MK θ' a' K)) y).1 = ((φ t : Module.End A ((hset Q₀ τ₀).MK θ a K₀)) y₀).1 :=
    sk_hecke _ _ _ _ (h := hF) (h₀ := hF₀) j hop hm
  have hB := _root_.UpperTheory.V.Hi.levelUR2BaseEq_alt hN l L Ω s n hn V₀ V Q₀ Q c m τ₀ A θ hθ a K₀ K p hp hps hpr j hj1 hj2 θ' a' hθ' hθθ ha
    _ _ hf₀ _ _ hf φ hg
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (hset Q τ₀).TK θ' a' K →ₐ[c.O] (hset Q₀ τ₀).TK θ a K₀, ∀ x, Φ x = φ x :=
    ⟨φ.restrictScalars c.O, fun _ => rfl⟩
  have e := sk_comp f f₀ β Φ φ.toRingHom hΦ p D ψ D₀ ψ₀ hD hψ (hu _) hB t
  refine (hνf t y).trans ((hφ (f t) y y₀ hy).trans ?_)
  exact congrArg (fun u : Module.End A ((hset Q₀ τ₀).MK θ a K₀) => (u y₀).1)
    ((congrArg Subtype.val e).trans (hμf (β t)).symm)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAboveW
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc Lp)
open scoped Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.Z.Sym.AboveWeight
section
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}
private theorem noLk_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (u : kˣ →* ℂˣ) (H : ∀ i j : Fin 3, i ≠ j → (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) j ∧
      (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) j * absPow k 1) :
    UpperTheory.V.Z.Sym.W.NoLk u := by
  intro j hj e he hE
  have e1 : absPow k (((1 : ℤ) : ℂ)) = absPow k 1 := by simp
  have e2 : absPow k (((-1 : ℤ) : ℂ)) = (absPow k 1)⁻¹ := by
    rw [show (((-1 : ℤ) : ℂ)) = -1 by simp, absPow_neg]
  rcases hj with rfl | rfl <;> rcases he with rfl | rfl
  · rw [pow_one, e1] at hE
    exact (H 0 1 (by decide)).2 (by simpa using hE)
  · rw [pow_one, e2] at hE
    exact (H 1 0 (by decide)).2 (by simp [hE])
  · rw [e1] at hE
    refine (H 0 2 (by decide)).2 ?_
    simp [← hE, pow_two]
  · rw [e2] at hE
    refine (H 2 0 (by decide)).2 ?_
    have hp : absPow k 1 = (u ^ 2)⁻¹ := by rw [hE, inv_inv]
    simp [hp, pow_two]
private theorem noLk_above (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (ha : IsLocalArtin h a) (hv : A.valuation (l : Ω) < 1) {m : ℕ} (hm : 2 ≤ m) {b : ℤ} {k : ℕ} (hk : 0 < k)
    {ω₀ ω₁ : (w.adicCompletion L)ˣ →* ℂˣ} {κ₀ κ₁ : Dec (F := L) A →* (Qbar l)ˣ}
    (h₀ : OrdChar ι a ω₀ (fun _ => -(b + m)) κ₀) (h₁ : OrdChar ι a ω₁ (fun _ => -b) κ₁)
    (hκ : ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
      κ₀ s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ₁ s ^ k = (cycBar L Ω l s ^ b) ^ k) :
    UpperTheory.V.Z.Sym.W.NoLk (ω₀ / ω₁) := by
  let u := ω₀ / ω₁
  let c : Fin 3 → ℤ := ![m, 0, -m]
  let ψ : Fin 3 → Dec (F := L) A →* (Qbar l)ˣ := ![κ₀ / κ₁, 1, κ₁ / κ₀]
  let hh : Fin 3 → (L →+* Qbar l) → ℤ := fun i _ => (![-(m : ℤ), 0, (m : ℤ)] : Fin 3 → ℤ) i
  have hq : ∀ {p q y : (Qbar l)ˣ} {e f : ℤ}, p ^ k = (y ^ e) ^ k → q ^ k = (y ^ f) ^ k →
      (p / q) ^ k = (y ^ (e - f)) ^ k := fun h1 h2 => by
    rw [div_pow, h1, h2, ← div_pow, zpow_sub, div_eq_mul_inv]
  have hp : ∀ (i : Fin 3) (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A →
      ψ i s ^ k = (cycBar L Ω l s ^ c i) ^ k := fun i s hs => by
    obtain ⟨h1, h2⟩ := hκ s hs
    fin_cases i
    · have := hq h1 h2
      simpa [ψ, c] using this
    · simp [ψ, c]
    · have := hq h2 h1
      simpa [ψ, c] using this
  have hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := fun i j => by
    refine not_link hv hk (hp i) (hp j) ?_
    fin_cases i <;> fin_cases j <;> simp [c] <;> omega
  have H0 : OrdChar ι a u (fun _ => -(m : ℤ)) (κ₀ / κ₁) := by
    have := ord_div h₀ h₁
    have e : ((fun _ => -(b + m)) - fun _ => -b : (L →+* Qbar l) → ℤ) = fun _ => -(m : ℤ) := by
      funext t
      simp
    rwa [e] at this
  have H1 : OrdChar ι a (1 : (w.adicCompletion L)ˣ →* ℂˣ) (fun _ => 0) (1 : Dec (F := L) A →* (Qbar l)ˣ) := by
    have := ord_div h₀ h₀
    rw [div_self', div_self', sub_self] at this
    exact this
  have H2 : OrdChar ι a u⁻¹ (fun _ => (m : ℤ)) (κ₁ / κ₀) := by
    have := ord_div h₁ h₀
    have e : ((fun _ => -b) - fun _ => -(b + m) : (L →+* Qbar l) → ℤ) = fun _ => (m : ℤ) := by
      funext t
      simp
    rw [e] at this
    rwa [show u⁻¹ = ω₁ / ω₀ from inv_div _ _]
  have hO : ∀ i, OrdChar ι a ((![u, 1, u⁻¹] : Fin 3 → (w.adicCompletion L)ˣ →* ℂˣ) i) (hh i) (ψ i) := fun i => by
    fin_cases i
    · exact H0
    · exact H1
    · exact H2
  have hmono : ∀ t : L →+* Qbar l, StrictMono fun j : Fin 3 => hh j t := fun t => by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> simp [hh] <;> omega
  exact noLk_of u (not_linked H ι hw ha hmono hO hne)
private theorem above' (P : _root_.UpperTheory.V.Af.Hypotheses') (hl : l ≠ 2) {n : ℕ} {ι : Qbar l ≃+* ℂ} {ρ : G L Ω →* GL (Fin n) (Qbar l)}
    {HT : (L →+* Qbar l) → Multiset ℤ} (hρ : Continuous ρ) (HG : HasHTAt ρ HT w) (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {τ : SmIrr (GL (Fin n) (w.adicCompletion L))} (H : LocGlobT ι ρ w τ)
    {rc : IrrGL (k := w.adicCompletion L) → WD h} (hrc : IsRecT h rc)
    (hp : GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred)) (hg : Gd (rc (algNorm τ)))
    {hh : Fin n → (L →+* Qbar l) → ℤ} (hm : ∀ t, StrictMono fun j => hh j t) {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hψ : ∀ i, W.IsLocAlg h (ψ i) fun t => hh i (t.1.comp (algebraMap L _)))
    (hf : W.HasFlag (ρ.comp (Dec (F := L) A).subtype) ψ)
    (hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) :
    ∃ (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a ∧
    (∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, Nonempty (τ.ρ.Equiv (PS ω)) ∧ ∀ i, OrdChar ι a (ω i) (hh i) (ψ i)) ∧
    ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = Finset.univ.val.map fun i => hh i (j.1.comp (algebraMap L _)) := by
  obtain ⟨a, ha⟩ : ∃ a, IsLocalArtin h a := by
    obtain ⟨a, ha, -⟩ := hrc
    exact ⟨a, ha⟩
  have hc : Continuous (ρ.comp (Dec (F := L) A).subtype) := hρ.comp continuous_subtype_val
  choose ω hω using fun i => (Loc.ordCharIff P.litN.aut.art h ι _ ha (hh i) (ψ i)).1.2 ⟨flag_cont' hc hf i, hψ i⟩
  have hD : DRat ι h (ρ.comp (Dec (F := L) A).subtype) HT fun s => (rc (algNorm τ)).charPol s := fun O _ _ _ Bw hj =>
    have h1 := HG A h O Bw hj
    ⟨h1.1, h1.2, fun s => by rw [((H A h rc hrc).2 O Bw hj hg).2]⟩
  have hD' := _root_.UpperTheory.V.Loc.flag_weil_deligne_of_literal_automorphy_n P.litN L Ω l hl ι n w hw A h _ ha _ hc _ ω ψ hω hf _ _ hD
  refine ⟨a, ha, ⟨ω, ?_, hω⟩, jumps_eq h hw hD hD'⟩
  have hs : IsSubquotient τ.ρ (PS ω) := by
    obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
    exact _root_.UpperTheory.V.Z.Desc.W.pseudo_local_langlands_descent P.litN L Ω n w A h _ ha rc hrc τ hp ω (fun i => (hω i).smooth) fun s =>
      ((hD O Bw hj).2.2 s).symm.trans ((hD' O Bw hj).2.2 s)
  exact (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient P.litN _ n ω (fun i => (hω i).smooth)
    (not_linked P.litN.aut.art ι hw ha (fun t i j hij => hm t hij) hω hne)).2 _ τ.ρ τ.irred hs
end
end
theorem UpperTheory.V.Z.Sym.W.above_w_statement : _root_.UpperTheory.V.Z.Sym.W.AboveWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι hl r hr m hm w hw HT hHT A h ⟨b, k, κ, hk, hf, hκ⟩ τ H hPT
  have hv : A.valuation (l : Ω) < 1 := by
    have := (h ((l : ℕ) : 𝓞 L)).2 hw
    simpa only [map_natCast] using this
  let c : Fin 2 → ℤ := ![b + m, b]
  have hκ' : ∀ (i : Fin 2) (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s ^ k = (cycBar L Ω l s ^ c i) ^ k := by
    intro i s hs
    fin_cases i
    · exact (hκ s hs).1
    · exact (hκ s hs).2
  have hcont : Continuous (r.comp (Dec (F := L) A).subtype) := hr.comp continuous_subtype_val
  have hfc : ∀ i, Continuous (κ i) := flag_cont' hcont hf
  have hmono : ∀ t : L →+* Qbar l, StrictMono fun j : Fin 2 => (fun (i : Fin 2) (_ : L →+* Qbar l) => -c i) j t := by
    intro t
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i
    simp [c]
    omega
  have hne : ∀ i j, κ i ≠ κ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
    intro i j
    refine not_link hv hk (hκ' i) (hκ' j) ?_
    fin_cases i <;> fin_cases j <;> simp [c] <;> omega
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt P.litN h
  have hg : Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc 2 τ hPT
  obtain ⟨a, ha, ⟨ω, he, hO⟩, hj⟩ := above' P hl hr hHT h hw H hrc hPT hg hmono
    (fun i => locAlg P.litN.aut.art h hw (κ i) (hfc i) hk (c i) (hκ' i)) hf hne
  refine ⟨⟨_, fun i => (hO i).smooth.mul (isSmoothChar_of_isUnram (isUnram_absPow _ _)), he, ?_⟩, -(b + m), fun j => ?_⟩
  · have := noLk_above P.litN.aut.art ι hw ha hv hm hk (hO 0) (hO 1) hκ
    simpa [mul_div_mul_right_eq_div] using this
  · rw [hj j]
    simp [c]
    rfl
end
end
end
