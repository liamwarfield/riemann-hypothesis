module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead ValuativeRel

namespace GlobalTheory.SatakeExists

theorem exists_eigenform {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hcomm : ∀ a b : G, a * b = b * a)
    (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    [FiniteDimensional ℂ (fixed ρ H)] [Nontrivial (fixed ρ H)] :
    ∃ (χ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (χ g : ℂ) * l v) ∧
      ∀ h ∈ H, χ h = 1 := by
  have hc := LocGL.isCompl_fixed_twKer hρ hH
  let T : Subrepresentation ρ := ⟨twKer ρ H 1, fun g _ hv => twKer_le_comap ρ H g (hn g) hv⟩
  let σ := onFixed ρ H (MonoidHom.id G) hn
  let p : ρ.IntertwiningMap σ :=
    ⟨Submodule.projectionOnto _ _ hc, fun g => LinearMap.ext fun v => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
      have e1 := Submodule.projectionOnto_apply_left hc ⟨a, ha⟩
      have e2 := Submodule.projectionOnto_apply_right hc ⟨b, hb⟩
      have e3 := Submodule.projectionOnto_apply_left hc (σ g ⟨a, ha⟩)
      have e4 := Submodule.projectionOnto_apply_right hc ⟨ρ g b, T.apply_mem_toSubmodule g hb⟩
      simp only [LinearMap.comp_apply, map_add (f := _)]
      rw [e1, e2, e4, map_zero]
      exact congrArg (· + 0) e3⟩
  have hp : ∀ x : fixed ρ H, p x.1 = x := fun x => Submodule.projectionOnto_apply_left hc x
  obtain ⟨ψ, m, hm0, hm⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ G _ σ.dual fun a b => by
    rw [← map_mul, hcomm, map_mul]
  have hm' : ∀ g x, m (σ g x) = ((ψ g)⁻¹ : ℂˣ) * m x := fun g x => by
    have := LinearMap.congr_fun (hm g⁻¹) x
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using this
  obtain ⟨x₀, hx₀⟩ : ∃ x, m x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (LinearMap.ext fun x => by simpa using h x)
  refine ⟨ψ⁻¹, m ∘ₗ p.toLinearMap, fun h => hx₀ ?_, fun g v => ?_, fun h hh => ?_⟩
  · have := LinearMap.congr_fun h x₀.1
    simpa [hp] using this
  · show m (p (ρ g v)) = _
    rw [p.isIntertwining, hm']
    rfl
  · have h1 : σ h x₀ = x₀ := by
      apply Subtype.ext
      show ρ h x₀.1 = x₀.1
      simpa using x₀.2 ⟨h, hh⟩
    have h2 := hm' h x₀
    rw [h1] at h2
    have h3 : (((ψ h)⁻¹ : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hx₀ (show (1 : ℂ) * m x₀ = (((ψ h)⁻¹ : ℂˣ) : ℂ) * m x₀ by rw [one_mul]; exact h2)
      exact this.symm
    exact Units.ext (by simpa using h3)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_torusChar {n : ℕ} (μ : (Fin n → kˣ) →* ℂˣ) (hμ : ∀ t ∈ torusO k (Fin n), μ t = 1) :
    ∃ α : Fin n → ℂˣ, SmGL.torusChar (fun i => unrChar k (α i)) = μ := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k)
    refine ⟨Units.mk0 c fun h => ?_, hc⟩
    rw [h, map_zero] at hc
    exact IwahoriInj.unif_pos.ne hc
  let c : Fin n → kˣ →* ℂˣ := fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)
  have hc : ∀ i, IsUnram (c i) := fun i x hx => hμ _ fun j => by
    by_cases h : j = i
    · subst h; simpa using hx
    · simp [Pi.mulSingle_eq_of_ne h]
  refine ⟨fun i => c i ϖ, MonoidHom.ext fun t => ?_⟩
  rw [SmGL.torusChar_apply]
  simp only [← GlobalTheory.SmGL.eq_unrChar (hc _) hϖ]
  conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
  rfl

theorem isSubquotient_of_eigenform {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π) (hirr : π.IsIrreducible)
    (μ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t x, l (jacB π t x) = (μ t : ℂ) * l x) :
    IsSubquotient π (indB (ofChar μ)) := by
  let ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ :=
    (ofChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (SmGL.jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨l, fun g => LinearMap.ext fun x => by
      obtain ⟨t, rfl⟩ := (leviTorus k (Fin n)).surjective g
      have e : (ρ (leviTorus k (Fin n) t)) (l x) = (μ t : ℂ) * l x := by
        show ofChar μ ((leviTorus k (Fin n)).symm (leviTorus k (Fin n) t)) _ = _
        rw [MulEquiv.symm_apply_apply, ofChar_apply]
      exact (hl t x).trans e.symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  have hne : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    refine hl0 (LinearMap.ext fun x => ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : φ (Submodule.Quotient.mk v) = (f v).1.1 1 := by rw [← hf]; rfl
    have h2 : l (Submodule.Quotient.mk v) = φ (Submodule.Quotient.mk v) := rfl
    rw [h2, h1, h v]
    rfl
  refine IsSubquotient.of_injective f ((injective_iff_map_eq_zero f.toLinearMap).2 ?_)
  let K : Subrepresentation π := ⟨LinearMap.ker f.toLinearMap, fun g v hv => by
    show f (π g v) = 0
    rw [f.isIntertwining]
    have : f v = 0 := hv
    rw [this, map_zero]⟩
  haveI := hirr
  rcases eq_bot_or_eq_top K with h | h
  · intro v hv
    have : v ∈ K.toSubmodule := hv
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · obtain ⟨v, hv⟩ := hne
    exact absurd (show v ∈ K.toSubmodule by rw [h]; trivial) hv

theorem exists_eigenform_jacBU {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hadm : IsAdmissible π)
    (hI : fixed π (iwahori k (Fin n)) ≠ ⊥) :
    ∃ (χ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 ∧
      (∀ g v, l (jacBU π g v) = (χ g : ℂ) * l v) ∧ ∀ h ∈ torusO k (Fin n), χ h = 1 := by
  haveI := hadm.2 _ (SmGL.IwahoriOnto.isOpen_iwahori k (Fin n))
    (SmGL.IwahoriOnto.isCompact_iwahori k (Fin n))
  have hb := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hadm
  haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) :=
    Module.Finite.of_surjective _ hb.2
  haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 hI
  haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial
  exact exists_eigenform (isSmooth_jacBU hadm.1) (SmGL.UnramFixed.isCompact_torusO k (Fin n)) mul_comm
    fun _ => by rw [Subgroup.normalizer_eq_top]; trivial

theorem exists_isSubquotient_prinSeries {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hadm : IsAdmissible π) (hirr : π.IsIrreducible)
    (hI : fixed π (iwahori k (Fin n)) ≠ ⊥) :
    ∃ α : Fin n → ℂˣ, IsSubquotient π (prinSeries fun i => unrChar k (α i)) := by
  obtain ⟨χ, l, hl0, hl, hχ⟩ := exists_eigenform_jacBU hadm hI
  let δ : (Fin n → kˣ) →* ℂˣ :=
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  obtain ⟨α, hα⟩ := exists_eq_torusChar (χ * δ⁻¹) fun t ht => by
    have : δ t = 1 := SmGL.UnramFixed.deltaHalf_torusO k ht
    simp [hχ t ht, this]
  refine ⟨α, ?_⟩
  have key := isSubquotient_of_eigenform hadm.1 hirr (χ * δ⁻¹) l hl0 fun t x => by
    rw [SmGL.UnramFixed.jacB_apply, map_smul, hl, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul,
      MonoidHom.inv_apply]
    ring
  rw [← hα] at key
  exact key

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), IsSpherical π.π → ∃ α : Fin n → ℂˣ, HasSatake π.π α := by
  intro hBZ k _ _ _ _ n π hs
  have hadm : IsAdmissible π.π := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hI : fixed π.π (iwahori k (Fin n)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := exists_isSubquotient_prinSeries hadm π.irr hI
  exact ⟨α, π.irr, hs, hα⟩

end GlobalTheory.SatakeExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParametersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalRepGL_exists_satakeParameters : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), IsSpherical π.π → ∃ α : Fin n → ℂˣ, HasSatake π.π α := by
  first | exact @GlobalTheory.SatakeExists.main | exact GlobalTheory.SatakeExists.main | (intros; apply GlobalTheory.SatakeExists.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SplitMatch

open Formalism.L2.NTheta

variable {D : D7}

theorem exists_isIdemAt {P : Pl D.host.E} (hP : conjPl P ≠ P) : ∃ e : AE D, IsIdemAt e P := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  rcases h with ⟨h, -⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact ⟨e, h⟩
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem idem_unique {P : Pl D.host.E} {e e' f' : AE D} (he : IsIdemAt e P) (h : IsPrimeIdem P e' f') :
    e' = e ∧ f' = e + cA D e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨hd, ε, hε, h1⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨hd', ε', hε', h1'⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  exact ⟨GlobalTheory.IdemSupport.delta_unique hΦ hd' hd, by rw [h1, h1', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]⟩

theorem mem_hyp {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {V : HSp D} {k : GA D V} (hk : k ∈ hyp V P) :
    k ∈ locPart V (KsphC V ∅) e := by
  obtain ⟨h1, e', f', h2, h3⟩ := hk
  rw [(idem_unique he h2).2] at h3
  exact ⟨h1, h3⟩

theorem one_mem_hyp {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) (V : HSp D) : (1 : GA D V) ∈ hyp V P := by
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, e + cA D e,
    Or.inl ⟨he, rfl⟩, GlobalTheory.SplitHecke.suppAt_one V⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

theorem unr {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {χ : (AE D)ˣ →* Circle} (hχ : UnrPl P χ)
    (y : (AE D)ˣ) (h : (1 - e) * (y : AE D) = 1 - e) (h1 : finPart D (e * (y : AE D)) ∈ intAE D)
    (h2 : finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D) : χ y = 1 := by
  have h' : (1 - e) * ((y⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
    conv_lhs => rw [← h, mul_assoc, Units.mul_inv, mul_one]
  have e0 : finPart D e ∈ intAE D := by
    by_contra hc
    have := (he.2 1 one_ne_zero).2 (by
      rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have key : ∀ z : AE D, (1 - e) * z = 1 - e → finPart D (e * z) ∈ intAE D → finPart D z ∈ intAE D := fun z a b => by
    have : z = e * z + 1 - e := by linear_combination a
    rw [this, RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_one]
    exact sub_mem (add_mem b (GlobalTheory.SplitDivisors.one_mem_int D)) e0
  refine hχ e _ (Or.inl ⟨he, rfl⟩) y ?_ (key _ h h1) (key _ h' h2)
  linear_combination (cA D e - 1) * h + ((y : AE D) - 1) * he.1.2.1

theorem sphOp_of {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) {V : HSp D} {d : List ℤ} (hd : d.Pairwise fun a b => b ≤ a) {α : GA D V}
    (hα : SuppAt e V α) (hD : DivAt V e (ϖ : D.host.E) d α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (hc : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : SphOp V P d R :=
  ⟨e, e + cA D e, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), Or.inl ⟨he, rfl⟩, h1, h2, hd,
    fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hD, hR, hc⟩

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise fun a b => b ≤ a := by
  simp [splitLab, List.pairwise_append, List.pairwise_replicate]

theorem dual_splitLab_pairwise (n k : ℕ) : (dualLab (splitLab n k)).Pairwise fun a b => b ≤ a := by
  simp [dualLab, splitLab, List.pairwise_append, List.pairwise_replicate]

theorem exists_data {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) (V : HSp D) : ∃ (α : ℕ → GA D V) (R R' : ℕ → Finset (GA D V)),
      (∀ j, j ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) j (α j) ∧ (∀ γ ∈ R j, SuppAt e V γ) ∧
        IsCosetRep V (locPart V (KsphC V ∅) e) (α j) (R j)) ∧
      (∀ j, j ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) j (α j) ∧ (∀ γ ∈ R' j, SuppAt e V γ) ∧
        IsCosetRep V (locPart V (KsphC V ∅) e) (α j)⁻¹ (R' j)) ∧
      (∀ j, j ≤ V.rank → SphOp V P (dualLab (splitLab V.rank j)) (R j)) ∧
      ∀ j, j ≤ V.rank → SphOp V P (splitLab V.rank j) (R' j) := by
  obtain ⟨-, hrep, hH⟩ := GlobalTheory.SplitPlace.split_local V P e he
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
  choose! α hα using (hH ϖ h1 h2).1
  choose! ρ hρ using hrep
  have hD := fun j hj => GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V P e ϖ j (α j) he h1 h2 hj (hα j hj)
  have s := fun j hj => (hα j hj).2.1
  have s' := fun j hj => GlobalTheory.SplitHecke.suppAt_inv (s j hj)
  refine ⟨α, fun j => ρ (α j), fun j => ρ (α j)⁻¹, fun j hj => ⟨hα j hj, hρ _ (s j hj)⟩,
    fun j hj => ⟨hα j hj, hρ _ (s' j hj)⟩, fun j hj => ?_, fun j hj => ?_⟩
  · refine sphOp_of he h1 h2 (dual_splitLab_pairwise _ _) (s j hj) ?_ (hρ _ (s j hj)).1 (hρ _ (s j hj)).2
    have := (GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 (hD j hj)).1
    rwa [inv_inv] at this
  · exact sphOp_of he h1 h2 (splitLab_pairwise _ _) (s' j hj) (hD j hj) (hρ _ (s' j hj)).1 (hρ _ (s' j hj)).2

section

variable {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)

theorem opOf_single (d : List ℤ) (z : ℂ) : opOf π P (Finsupp.single d z) = z • ∑ γ ∈ rep V P d, π γ := by
  unfold opOf
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem opOf_sum (s : Finset ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) :
    opOf π P (∑ j ∈ s, Finsupp.single (d j) (z j)) = ∑ j ∈ s, z j • opOf π P (Finsupp.single (d j) 1) := by
  simp only [opOf_single, one_smul]
  unfold opOf
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (zero_smul _ _)

theorem opOf_trunc (n k : ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) (u : M) :
    opOf π P (∑ j ∈ Finset.range (n + 1), Finsupp.single (d j) (if j ≤ k then z j else 0)) u =
      ∑ j ∈ Finset.range (min k n + 1), z j • opOf π P (Finsupp.single (d j) 1) u := by
  rw [opOf_sum, LinearMap.sum_apply]
  symm
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_)
  · rw [Finset.mem_range] at hj
    rw [if_pos (by omega), LinearMap.smul_apply]
  · rw [Finset.mem_range] at hj hj'
    rw [if_neg (by omega), zero_smul, LinearMap.zero_apply]

end

theorem dualC_splitC (n : ℕ) (z : ℕ → ℂ) :
    dualC (splitC n z) = ∑ j ∈ Finset.range (n + 1), Finsupp.single (dualLab (splitLab n j)) (z j) := by
  unfold dualC splitC
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]


set_option maxHeartbeats 1000000 in
theorem match_split : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P ≠ P → UnrPl P χS → UnrPl P χT → VacFix ψ om P ∧ ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → (T.rank = S.rank + t → ∀ k, k ≤ T.rank → Match ψ om P (dualC (splitC S.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ k * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank) ^ j else 0)) (Finsupp.single (splitLab T.rank k) 1)) ∧ (S.rank = T.rank + t → ∀ k, k ≤ S.rank → Match ψ om P (dualC (Finsupp.single (splitLab S.rank k) 1)) (splitC T.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((T.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank) ^ j else 0)) := by
  intro D ψ S T χS χT om P hW hP hS hT
  have main : ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ) (he : IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal)
      (h2 : ϖ ∉ P.asIdeal ^ 2) (hx : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)) f (hf : IsVacAt ψ S T P f)
      αS αT RS RT a b, _ := fun e ϖ x t he h1 h2 hx f hf αS αT RS RT a b =>
    GlobalTheory.SplitHecke.hecke_identity_split ψ S T χS χT om P e ϖ x f αS αT RS RT t hW he h1 h2 hx
      (fun y a b c => ⟨unr he hS y a b c, unr he hT y a b c⟩) hf.1 (hf.2 e _ (Or.inl ⟨he, rfl⟩)) a b
  have fix : VacFix ψ om P := by
    intro f hf k hk k' hk'
    obtain ⟨e, he⟩ := exists_isIdemAt hP
    obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
      (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
    have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
      rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
    have hi : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by
      rw [← RingHom.map_mul, mul_inv_cancel₀ h0, RingHom.map_one]
    obtain ⟨αS, RS, -, a, -, -, -⟩ := exists_data he h1 h2 S
    obtain ⟨αT, -, RT, -, b, -, -⟩ := exists_data he h1 h2 T
    exact (main e ϖ (Units.mkOfMulEqOne _ _ (GlobalTheory.SplitHecke.idem_mul_inv he.1.1 hi)) 0 he h1 h2 rfl f hf
      αS αT RS RT a b).1 k (mem_hyp he hk) k' (mem_hyp he hk')
  refine ⟨fix, fun e ϖ x t he h1 h2 hx => ?_⟩
  obtain ⟨αS, RS, -, a, -, a', -⟩ := exists_data he h1 h2 S
  obtain ⟨αT, -, RT, -, b, -, b'⟩ := exists_data he h1 h2 T
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ j, j ≤ S.rank → ∑ γ ∈ RS j, om (γ, 1) f =
      opOf (om.comp (MonoidHom.inl _ _)) P (Finsupp.single (dualLab (splitLab S.rank j)) 1) f := fun f hf j hj =>
    ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors S P).1 _ _ (a' j hj)).2 _ (om.comp (MonoidHom.inl _ _)) f
      fun k hk => fix f hf k hk 1 (one_mem_hyp he T)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ j, j ≤ T.rank → ∑ γ ∈ RT j, om (1, γ) f =
      opOf (om.comp (MonoidHom.inr _ _)) P (Finsupp.single (splitLab T.rank j) 1) f := fun f hf j hj =>
    ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors T P).1 _ _ (b' j hj)).2 _ (om.comp (MonoidHom.inr _ _)) f
      fun k hk => fix f hf 1 (one_mem_hyp he S) k hk
  refine ⟨fun hr k hk f hf => ?_, fun hr k hk f hf => ?_⟩
  · rw [dualC_splitC, opOf_trunc, ← eT f hf k hk, (main e ϖ x t he h1 h2 hx f hf αS αT RS RT a b).2.1 hr k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [eS f hf j (by rw [Finset.mem_range] at hj; omega)]
  · rw [splitC, opOf_trunc, dualC, Finsupp.mapDomain_single, ← eS f hf k hk,
      (main e ϖ x t he h1 h2 hx f hf αS αT RS RT a b).2.2 hr k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [eT f hf j (by rw [Finset.mem_range] at hj; omega)]

end GlobalTheory.Hk3.SplitMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.L2.DIV hiding conjPl
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuum_heckeIdentity_splitPlace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P ≠ P → UnrPl P χS → UnrPl P χT → VacFix ψ om P ∧ ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → (T.rank = S.rank + t → ∀ k, k ≤ T.rank → Match ψ om P (dualC (splitC S.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ k * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank) ^ j else 0)) (Finsupp.single (splitLab T.rank k) 1)) ∧ (S.rank = T.rank + t → ∀ k, k ≤ S.rank → Match ψ om P (dualC (Finsupp.single (splitLab S.rank k) 1)) (splitC T.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((T.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank) ^ j else 0)) := by
  first | exact @GlobalTheory.Hk3.SplitMatch.match_split | exact GlobalTheory.Hk3.SplitMatch.match_split | (intros; apply GlobalTheory.Hk3.SplitMatch.match_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
noncomputable section

namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def adj (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x : Matrix (Fin n') (Fin n) L) :
    Matrix (Fin n) (Fin n') L :=
  ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L)

def HomA (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) ∧
    ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ (adj σ JS JT x *ᵥ w)) i ∈ Formalism.UG.intL L

def GramEq (σ : L →+* L) {n n' : ℕ} (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  ∀ m m' : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → (∀ i, m' i ∈ Formalism.UG.intL L) → ∀ c ∈ Formalism.UG.intL L,
    (∀ i, (x *ᵥ (c • m)) i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • m')) i ∈ Formalism.UG.intL L) →
      c * (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ m) (y *ᵥ m') -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ m) (x *ᵥ m')) ∈ Formalism.UG.intL L

def SelfDual (σ : L →+* L) {n : ℕ} (JS : GL (Fin n) L) (a : GL (Fin n) L) : Prop :=
  (∀ i j, (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) i j ∈
      Formalism.UG.intL L) ∧
    ∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L

end GlobalTheory.Hk3.HoweG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTransp
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTransp
noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.ConjDualPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}


variable (L a) in
def phiA : GA L a := finGL L a (PhiU a (Af L)) * infGL L a (PhiU a (Cinf L))

theorem toUnits_PhiK : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl

theorem invT_map_invT (c : Af L →+* Af L) (k : GL (Fin a) (Af L)) :
    invT a (Af L) (GeneralLinearGroup.map c (invT a (Af L) k)) = GeneralLinearGroup.map c k := by
  ext i j
  rfl

theorem rt_phiA_act (o : Op L a) :
    rt L a (phiA L a) * act (conjOp o) = act (thetaOp (invTOp o)) * rt L a (phiA L a) := by
  cases o with
  | fin k =>
    change rt L a (phiA L a) * rt L a (finGL L a _) = rt L a (finGL L a (thetaGL a _ (invT a (Af L) k))) * rt L a (phiA L a)
    rw [← map_mul, ← map_mul]
    congr 1
    have h : thetaGL a (conjFin (IsCMField.complexConj L).toRingEquiv) (invT a (Af L) k) =
        PhiU a (Af L) * GeneralLinearGroup.map (conjFin (IsCMField.complexConj L).toRingEquiv) k * (PhiU a (Af L))⁻¹ := by
      change PhiU a (Af L) * invT a (Af L) (GeneralLinearGroup.map _ (invT a (Af L) k)) * (PhiU a (Af L))⁻¹ = _
      rw [invT_map_invT]
    rw [h, phiA, map_mul, map_mul, map_inv, mul_assoc, infGL_comm]
    group
  | cpt k =>
    change rt L a (phiA L a) * rt L a (infGL L a (Unitary.toUnits _)) =
      rt L a (infGL L a (Unitary.toUnits (PhiK L a * barK k * (PhiK L a)⁻¹))) * rt L a (phiA L a)
    rw [← map_mul, ← map_mul]
    congr 1
    rw [phiA, map_mul, map_mul, map_inv, toUnits_PhiK, map_mul, map_mul, map_inv]
    have e := infGL_comm (E := L) (a := a) (PhiU a (Cinf L) * Unitary.toUnits (barK k) * (PhiU a (Cinf L))⁻¹)
      (PhiU a (Af L))
    rw [map_mul, map_mul, map_inv] at e
    rw [toUnits_PhiK, ← mul_assoc (_ * _ * _) (finGL L a _), e]
    group
  | lie X =>
    change rt L a (phiA L a) * lie L a (fun i j => star (X i j)) =
      lie L a (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ))) *
        rt L a (phiA L a)
    rw [phiA, map_mul, mul_assoc,
      show (fun i j => star (X i j) : Lie L a) = toL (Matrix.of fun i j => star (X i j)) from rfl,
      GlobalTheory.CapAdInv.rt_lie, ← mul_assoc, ← lie_rt_fin, mul_assoc]
    refine congrArg (fun Y => lie L a (toL Y) * _) ?_
    have h : (Matrix.of (toL (-(Matrix.of X)ᵀ)))ᴴ = -(Matrix.of fun i j => star (X i j)) := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    change GlobalTheory.Tw.Phi a (Cinf L) * _ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ = _
    rw [h, mul_neg, neg_mul, neg_neg]

theorem rt_inv_phiA (f : Sm L a) : rt L a (phiA L a)⁻¹ (rt L a (phiA L a) f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem dualIsConjBy_of_paired_invT : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a)
    (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  intro L _ _ _ a π ψ ⟨B, hl, hr, hf, hc, hX⟩ ⟨T, hT⟩
  let u : π.V →ₗ[ℂ] π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  have hu : ∀ χ : π.V, (u χ).1 = rt L a (phiA L a) χ.1 := fun χ => by
    change rt L a (finGL L a _) (rt L a (infGL L a (Unitary.toUnits (PhiK L a))) χ.1) = _
    rw [toUnits_PhiK, phiA, map_mul]
    rfl
  have hkey : ∀ o χ, u (π.op (conjOp o) χ) = π.op (thetaOp (invTOp o)) (u χ) := fun o χ =>
    Subtype.ext (by rw [hu, CuspSub.op_val, CuspSub.op_val, hu]; exact LinearMap.congr_fun (rt_phiA_act o) χ.1)
  have hinj : ∀ χ, u χ = 0 → χ = 0 := fun χ h => Subtype.ext (by
    have e := congrArg (fun ξ : π.V => rt L a (phiA L a)⁻¹ ξ.1) h
    simp only [hu, rt_inv_phiA, ZeroMemClass.coe_zero, map_zero] at e
    exact e)
  have hsurj : ∀ χ : π.V, ∃ ξ, u ξ = χ := fun χ =>
    ⟨π.op (.cpt (PhiK L a)⁻¹) (π.op (.fin (PhiU a (Af L))⁻¹) χ), Subtype.ext (by
      rw [hu]
      change rt L a (phiA L a) (rt L a (infGL L a (Unitary.toUnits (PhiK L a)⁻¹)) (rt L a (finGL L a _) χ.1)) = _
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, map_inv, toUnits_PhiK, phiA, map_inv,
        map_inv]
      simp)⟩
  refine ⟨B.compl₂ (T.toLinearMap ∘ₗ u), fun φ h => hl φ fun ψ' => ?_, fun χ h => hinj χ ?_,
    fun k φ χ => ?_, fun k φ χ => ?_, fun X φ χ => ?_⟩
  · obtain ⟨χ, rfl⟩ := T.surjective ψ'
    obtain ⟨ξ, rfl⟩ := hsurj χ
    exact h ξ
  · exact (LinearEquiv.map_eq_zero_iff T).1 (hr _ h)
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hf k φ _
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hc k φ _
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hkey, hT]
    exact hX X φ _

end GlobalTheory.ConjDualPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  first | exact @GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | exact GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | (intros; apply GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.MuIntegral

theorem muInt_of_charTied : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D)
    (Tp : Formalism.L2.Host.TupTied D C nch),
    Formalism.L2.Host.NCharTied D C nch Tp → GlobalTheory.SplitRead.MuInt D.nd D.naut := by
  intro D C nch Tp hT i τ z hz
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hmu := hT.muC i j hjj
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin (D.nd.mu i)
  have hinf : (Tp.tup (D.nd.mu i) j).HasInfQ (Formalism.L2.Host.embPsi D.host) (fun g => -Formalism.L2.Host.eExp D j g) :=
    (C.isMu0 j).inf.mul_triv (GlobalTheory.TypeValues.inf_eq_one _ hn ho)
  rw [← hmu] at hinf
  have key := hT.infG _ _ hinf
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
  obtain ⟨m, hm⟩ := (D.hc (D.eTau.symm (D.eTau ρ))).e_int j
  have hm' : Formalism.L2.Host.eExp D j (D.eTau ρ) = m := hm
  rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
  · have ht : τ = Formalism.L2.Host.embPsi D.host (D.eTau ρ) := h.symm
    rw [ht, (key (D.eTau ρ)).1] at hz
    refine ⟨-m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring
  · have ht : τ = (starRingEnd ℂ).comp (Formalism.L2.Host.embPsi D.host (D.eTau ρ)) := by
      rw [← h]; ext x; rfl
    rw [ht, (key (D.eTau ρ)).2] at hz
    refine ⟨m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring

end GlobalTheory.MuIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousMapGL
noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.ContraPair
open GlobalTheory.ThetaPull (cFin pInf_conjAd pFin_conjAd conjAd_conjAd continuous_conjAd)
open scoped ContDiff

namespace GlobalTheory.BarPull

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

theorem map_map_comm (p : R →+* S) (c : R →+* R) (c' : S →+* S) (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map p g) := by
  ext i j
  exact h _

theorem continuous_mapGL [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R) (h : Continuous c) :
    Continuous (GeneralLinearGroup.map (n := Fin a) c) :=
  Continuous.units_map _ (continuous_matrix fun i j => h.comp (continuous_id.matrix_elem i j))

theorem map_unip {r : ℕ} (c : R →+* R) (x : BlockIx a r → R) :
    GeneralLinearGroup.map c (unip x) = unip fun p => c (x p) := by
  ext i j
  change c ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM fun p => c (x p) : Matrix (Fin a) (Fin a) R) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add (f := _)]
  split_ifs <;> simp

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}


omit [IsCMField E] in
def barL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => star (X i j)
      map_add' := fun X Y => by funext i j; simp
      map_smul' := fun t X => by funext i j; simp }


variable (E a) in
def barA : GA E a →* GA E a := GeneralLinearGroup.map (conjAd E)

theorem barA_barA (g : GA E a) : barA E a (barA E a g) = g := by
  ext i j : 2
  exact conjAd_conjAd _

theorem barA_infGL (y : GL (Fin a) (Cinf E)) :
    barA E a (infGL E a y) = infGL E a (GeneralLinearGroup.map (starRingEnd (Cinf E)) y) :=
  ga_ext (by rw [barA, map_map_comm _ _ _ pInf_conjAd, pInf_infGL, pInf_infGL])
    (by rw [barA, map_map_comm _ _ _ pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

theorem barA_finGL (k : GL (Fin a) (Af E)) : barA E a (finGL E a k) = finGL E a (GeneralLinearGroup.map (cFin E) k) :=
  ga_ext (by rw [barA, map_map_comm _ _ _ pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
    (by rw [barA, map_map_comm _ _ _ pFin_conjAd, pFin_finGL, pFin_finGL])

theorem barA_ratGL (γ : GL (Fin a) E) :
    barA E a (ratGL E a γ) =
      ratGL E a (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom γ) :=
  (map_map_comm _ _ _ (fun x => (conjAd_algebraMap x).symm) γ).symm

theorem chart_bar (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (barA E a g)) g x = chart φ (barA E a g) (barL x) ∧ barL x ∈ invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [show barL (toL u.val) = toL (GeneralLinearGroup.map (starRingEnd (Cinf E)) u).val from rfl,
    chart_val, chart_val, map_mul, barA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem bar_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun g => φ (barA E a g)) ∈ Sm E a := fun g =>
  ((hφ (barA E a g)).comp (barL (E := E) (a := a)).contDiff.contDiffOn
    fun _ hx => (chart_bar φ g hx).2).congr fun _ hx => (chart_bar φ g hx).1


variable (E a) in
def pull : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun g => φ.1 (barA E a g), bar_mem_Sm φ.2⟩
  invFun φ := ⟨fun g => φ.1 (barA E a g), bar_mem_Sm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (barA_barA g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (barA_barA g)

theorem pull_apply (φ : Sm E a) (g : GA E a) : (pull E a φ).1 g = φ.1 (barA E a g) := rfl

theorem pull_pull (φ : Sm E a) : pull E a (pull E a φ) = φ := (pull E a).left_inv φ

theorem rt_pull (h : GA E a) (φ : Sm E a) : rt E a h (pull E a φ) = pull E a (rt E a (barA E a h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (barA E a) g h)

theorem lie_pull (X : Lie E a) (φ : Sm E a) : lie E a X (pull E a φ) = pull E a (lie E a (barL X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (pull E a φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (barA E a g) ∘ barL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_bar φ.1 g hx).1
  have h1 : barL (oneL E a) = oneL E a := by
    funext i j
    change star ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) = (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have h2 := HasFDerivAt.comp (oneL E a) (f := barL)
    (by rw [h1]; exact (differentiableAt_chart φ.2 (barA E a g)).hasFDerivAt) barL.hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, h2.fderiv]
  rfl

theorem act_pull (o : Op E a) (φ : Sm E a) : act o (pull E a φ) = pull E a (act (conjOp o) φ) := by
  cases o with
  | fin k => exact (rt_pull _ φ).trans (by rw [barA_finGL]; rfl)
  | cpt k =>
    have e : GeneralLinearGroup.map (starRingEnd (Cinf E)) (Unitary.toUnits k) = Unitary.toUnits (barK k) :=
      Units.ext rfl
    exact (rt_pull (infGL E a (Unitary.toUnits k)) φ).trans (by rw [barA_infGL, e]; rfl)
  | lie X => exact lie_pull X φ

theorem pull_act (o : Op E a) (φ : Sm E a) : pull E a (act o φ) = act (conjOp o) (pull E a φ) := by
  conv_lhs => rw [← pull_pull φ, act_pull, pull_pull]

theorem Eop_pull (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (pull E a φ) = pull E a (Eop (ComplexEmbedding.conjugate τ) i j φ) := by
  have h2 : ∀ z, lieS E a i j (atEmb τ z) (pull E a φ) =
      pull E a (lieS E a i j (atEmb (ComplexEmbedding.conjugate τ) z) φ) := fun z => by
    have e : star (atEmb τ z) = atEmb (ComplexEmbedding.conjugate τ) z := by
      classical
      rw [atEmb_conj]
      unfold atEmb
      rw [Pi.star_single]
      split_ifs <;> rfl
    have e' : barL (toL (Matrix.single i j (atEmb τ z))) = toL (Matrix.single i j (star (atEmb τ z))) := by
      funext k l
      change star (Matrix.single i j (atEmb τ z) k l) = Matrix.single i j (star (atEmb τ z)) k l
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [lieS_apply, lie_pull, e', e, lieS_apply]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, h2, map_smul, map_sub]

theorem cap_pull (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (pull E a φ) = pull E a (cap (ComplexEmbedding.conjugate τ) u φ) := by
  have h := map_qdet ((pull E a).conjAlgEquiv ℂ).toAlgHom
    (Eop (ComplexEmbedding.conjugate τ)) (u + ((a : ℂ) - 1) / 2)
  have e : (fun i j => ((pull E a).conjAlgEquiv ℂ).toAlgHom (Eop (ComplexEmbedding.conjugate τ) i j)) = Eop τ := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (pull E a).surjective ψ
    rw [Eop_pull]
    change pull E a (Eop (ComplexEmbedding.conjugate τ) i j ((pull E a).symm (pull E a ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e] at h
  rw [cap, ← h, cap]
  generalize Formalism.REAL.qdet (Eop (a := a) (ComplexEmbedding.conjugate τ)) (u + ((a : ℂ) - 1) / 2) = z
  change pull E a (z ((pull E a).symm (pull E a φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem Zalg_pull {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (pull E a φ) = pull E a (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩


omit [IsCMField E] in
theorem height_bar (y : GL (Fin a) (Cinf E)) :
    height (GeneralLinearGroup.map (starRingEnd (Cinf E)) y) = height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf E), ‖toL (GeneralLinearGroup.map (starRingEnd (Cinf E)) y).val‖ = ‖toL y.val‖ :=
    fun y => norm_star (toL y.val)
  unfold height
  rw [← map_inv, h1, h1]

theorem isAutForm_pull {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (pull E a φ) := by
  constructor
  case left =>
    intro γ g
    rw [pull_apply, map_mul, barA_ratGL, h.left, pull_apply]
  case level =>
    convert h.level.preimage (continuous_mapGL (cFin E) (continuous_conjFin _)) using 1
    ext k
    exact (Eq.congr_left (act_pull (.fin k) φ)).trans (pull E a).injective.eq_iff
  case kfin =>
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (pull E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull (.cpt k) φ).symm⟩
  case zfin =>
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (pull E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_pull hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  case growth =>
    intro g
    obtain ⟨C, N, h1⟩ := h.growth (barA E a g)
    refine ⟨C, N, fun y => ?_⟩
    rw [pull_apply, map_mul, barA_infGL, ← height_bar]
    exact h1 _

theorem bar_mem_ratN {r : ℕ} {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) :
    (fun p => conjAd E (x p)) ∈ ratN E a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => IsCMField.complexConj E (y p), funext fun p => (conjAd_algebraMap (y p)).symm⟩


open MeasureTheory in
theorem isCuspidal_pull {φ : GA E a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (barA E a g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  let β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad E) :=
    { toFun := fun x p => conjAd E (x p)
      invFun := fun x p => conjAd E (x p)
      left_inv := fun x => funext fun p => conjAd_conjAd _
      right_inv := fun x => funext fun p => conjAd_conjAd _
      map_add' := fun x y => funext fun p => map_add (conjAd E) _ _
      continuous_toFun := continuous_pi fun p => continuous_conjAd.comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => continuous_conjAd.comp (continuous_apply p) }
  let e : ratN E a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, bar_mem_ratN y.2⟩
      invFun := fun x => ⟨β x, bar_mem_ratN x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply]) (barA E a g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, barA, map_unip]
  rfl

end GlobalTheory.BarPull

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterCmInfinityType
noncomputable section

namespace GlobalTheory.KerJ.RatPts

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Host NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.Mem.Chr (finPartI)

theorem isFin_finPart {L : Type} [Field L] [NumberField L] (a : Ideles L) : IsFinIdele (finPartI L a) := fun _ => rfl

end GlobalTheory.KerJ.RatPts

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host NumberField Classical Formalism.FrobeniusOrbits GlobalTheory.KerJ.RatPts

end GlobalTheory.KerJ
end
end
