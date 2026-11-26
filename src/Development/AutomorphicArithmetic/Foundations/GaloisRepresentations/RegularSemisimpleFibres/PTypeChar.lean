module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.FiniteCuspidalOfIsCuspidal
public import Development.DiscreteGroups.GlobalIrreducibility.DzGalRes
public import Development.DiscreteGroups.GlobalIrreducibility.DzKSchur
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularLocalOfDepthZero
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.GreenCuspLabels.GreenCuspidal
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndDetK

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PTypeChar
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.Gal.InertialTypesAlt.TypeCharacters

open Matrix GlobalTheory.GLq GlobalTheory.SerSys GlobalTheory.IwahoriInj GlobalTheory.DepthZeroJac

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

private def resE : 𝓀[w.adicCompletion E] ≃+* ZMod g :=
  RingEquiv.ofBijective (DiscreteGroups.sglob.DzTw.resMap i hi) ⟨RingHom.injective _, fun a => by
    obtain ⟨y, rfl⟩ := DiscreteGroups.sglob.DzIso.redO_surjective i hi a
    exact ⟨IsLocalRing.residue _ y, rfl⟩⟩

private theorem resE_redK {n : ℕ} (x : KO (w.adicCompletion E) (Fin n)) (κ : GL (Fin n) ℤ_[g])
    (hκ : GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) = x) :
    GeneralLinearGroup.map (resE i hi).toRingHom (redK (w.adicCompletion E) (Fin n) x) = GlobalTheory.GLp.red g n κ := by
  ext a b
  have hx : ((x : GL (Fin n) (w.adicCompletion E)) : Matrix _ _ _) a b = i (κ a b : ℚ_[g]) := by
    rw [← hκ]; rfl
  simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, redK_apply]
  have key : ∀ y : 𝒪[w.adicCompletion E], (y : w.adicCompletion E) = i (κ a b : ℚ_[g]) →
      (resE i hi).toRingHom (IsLocalRing.residue _ y) = PadicInt.toZMod (κ a b) := by
    intro y hy
    show PadicInt.toZMod (DiscreteGroups.sglob.DzIso.toInt i hi y) = _
    congr 1
    apply Subtype.ext
    rw [DiscreteGroups.sglob.DzIso.coe_toInt, hy, RingEquiv.symm_apply_apply]
  exact key _ hx

private theorem finCusp_comp {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) :
    PositivityTheory.Rg.DzCount.FinCusp (τ.ρ.comp (GeneralLinearGroup.map (n := Fin n) (resE i hi).toRingHom)) := by
  intro s d e hne v hv
  have hF : PositivityTheory.Rg.DzCount.FinCusp τ.ρ :=
    PositivityTheory.Rg.DzCount.finite_cuspidal_of_isCuspidal τ (PositivityTheory.GreenCharacters.isCuspidal_of_isCusp τ hτ)
  refine hF s d e (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.mpr (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.mp hne)) v ?_
  intro u hu
  have hback : GeneralLinearGroup.map (resE i hi).toRingHom
      (GeneralLinearGroup.map (resE i hi).symm.toRingHom u) = u := by
    ext a b
    simp
  rw [← hback]
  apply hv
  rw [GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries] at hu ⊢
  intro a b hab
  have h1 := hu a b hab
  simp only [GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h1]
  by_cases hab' : a = b
  · subst hab'; simp
  · simp [Matrix.one_apply_ne hab']

private theorem fixed_eq_range {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character)
    (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ) (hω : HasCentralChar σ.ρ ω)
    (φ : τ →ₗ[ℂ] σ.V) (h0 : φ ≠ 0)
    (hφ : ∀ (k : GL (Fin n) ℤ_[g]) (u : τ), φ (τ.ρ (GlobalTheory.GLp.red g n k) u) =
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ u)) :
    Function.Injective φ ∧ fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) = LinearMap.range φ := by
  haveI hirr : Representation.IsIrreducible τ.ρ :=
    GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ (DiscreteGroups.sglob.DzType.Kon.simple_of_isIrr τ hτ.2.1)
  let U : Subrepresentation τ.ρ := ⟨LinearMap.ker φ, fun x v hv => by
    obtain ⟨k, rfl⟩ := GlobalTheory.GLp.Model.red_surjective n x
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hφ, hv, map_zero]⟩
  have hinj : Function.Injective φ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top U with h | h
    · have hk : LinearMap.ker φ = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.ker_eq_bot.1 hk
    · exfalso
      have hk : LinearMap.ker φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact h0 (LinearMap.ker_eq_top.1 hk)
  obtain ⟨u0, hu0⟩ : ∃ u, φ u ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h0 (LinearMap.ext hcon)
  haveI : Nontrivial τ := ⟨⟨u0, 0, fun e => hu0 (by rw [e, map_zero])⟩⟩
  have hT : PositivityTheory.Rg.DzCount.IsTypeMap (τ.ρ.comp (GeneralLinearGroup.map (n := Fin n) (resE i hi).toRingHom)) σ.ρ φ :=
    ⟨hinj, fun x v => by
      obtain ⟨κ, hκ⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KO i hi x.2
      rw [MonoidHom.comp_apply, resE_redK i hi x κ hκ, hφ, hκ]⟩
  exact ⟨hinj, PositivityTheory.Rg.DzCount.B.st6 (w.adicCompletion E) τ n _ (finCusp_comp i hi τ hτ) σ ω hω φ hT⟩

omit hi in
private theorem ringEquiv_eq {F : Type} [Field F] (r r' : F ≃+* ZMod g) : r = r' := by
  have h : (r.symm : ZMod g →+* F) = (r'.symm : ZMod g →+* F) := Subsingleton.elim _ _
  have hs : r.symm = r'.symm := RingEquiv.ext fun y => RingHom.congr_fun h y
  rw [← RingEquiv.symm_symm r, ← RingEquiv.symm_symm r', hs]

omit hi in
private theorem central (y : IrrGL (k := w.adicCompletion E)) : ∃ ω : (w.adicCompletion E)ˣ →* ℂˣ, HasCentralChar y.rep ω :=
  (GlobalTheory.T.centralCharacter_subquotient_productIrreducibles (w.adicCompletion E)).1 y

private theorem trace_eq {n : ℕ} (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character)
    (σ : IrrRep (GL (Fin n) (w.adicCompletion E))) (ω : (w.adicCompletion E)ˣ →* ℂˣ) (hω : HasCentralChar σ.ρ ω)
    (φ : τ →ₗ[ℂ] σ.V) (h0 : φ ≠ 0)
    (hφ : ∀ (k : GL (Fin n) ℤ_[g]) (u : τ), φ (τ.ρ (GlobalTheory.GLp.red g n k) u) =
      σ.ρ (GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n k)) (φ u))
    (γ : GL (Fin n) 𝓀[w.adicCompletion E]) :
    τ.character (GeneralLinearGroup.map (resE i hi).toRingHom γ) = LinearMap.trace ℂ _ (levelZero σ.ρ γ) := by
  obtain ⟨hinj, hfix⟩ := fixed_eq_range i hi τ hτ σ ω hω φ h0 hφ
  obtain ⟨x, rfl⟩ := GlobalTheory.LocGL.redK_surjective γ
  obtain ⟨κ, hκ⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KO i hi x.2
  rw [resE_redK i hi x κ hκ]
  let e : τ ≃ₗ[ℂ] fixed σ.ρ (KOne (w.adicCompletion E) (Fin n)) :=
    (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hfix.symm)
  have he : ∀ u : τ, ((e u : fixed σ.ρ (KOne (w.adicCompletion E) (Fin n))) : σ.V) = φ u := fun u => rfl
  have hc : e.conj (τ.ρ (GlobalTheory.GLp.red g n κ)) = levelZero σ.ρ (redK (w.adicCompletion E) (Fin n) x) := by
    ext v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    rw [he, hφ, hκ, levelZero_apply]
    congr 1
    have := he (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  show LinearMap.trace ℂ τ (τ.ρ (GlobalTheory.GLp.red g n κ)) = _
  rw [← hc, LinearMap.trace_conj']

end UpperTheory.Gal.InertialTypesAlt.TypeCharacters

open UpperTheory.Gal.InertialTypesAlt.TypeCharacters Matrix in
theorem UpperTheory.Gal.InertialTypesAlt.typeChar :
    TypeChar := by
  intro E _ _ v g _ i hi r y τ hτ hinf γ
  obtain ⟨φ, h0, hφ⟩ := hinf
  obtain ⟨ω, hω⟩ := central y
  have hr : r = resE i hi := ringEquiv_eq _ _
  rw [hr]
  exact trace_eq i hi τ hτ y.2.rep ω hω φ h0 hφ γ
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLblIso
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

section SlopeTestRemainingChoices

open GlobalTheory.Parabolic (mem_fixed)

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def intEquiv (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) : 𝒪[k] ≃+* 𝒪[K] where
  toFun x := ⟨i x, (hi x).2 x.2⟩
  invFun y := ⟨i.symm y, (hi _).1 (by rw [i.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private def resEquiv (i₀ : 𝒪[k] ≃+* 𝒪[K]) : 𝓀[k] ≃+* 𝓀[K] := IsLocalRing.ResidueField.mapEquiv i₀

private def glEquiv {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv g := by ext a b; simp
  right_inv g := by ext a b; simp

variable (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) {n : ℕ}

include hi

private theorem map_alg (u : GL (Fin n) 𝒪[k]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) =
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[K] K)
        (Matrix.GeneralLinearGroup.map (intEquiv i hi).toRingHom u) := by
  ext a b; rfl

private theorem map_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KO K (Fin n) := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨_, (map_alg i hi u).symm⟩

private theorem exists_KO {y : GL (Fin n) K} (hy : y ∈ KO K (Fin n)) :
    ∃ g ∈ KO k (Fin n), Matrix.GeneralLinearGroup.map i.toRingHom g = y := by
  obtain ⟨u, rfl⟩ := hy
  refine ⟨_, ⟨Matrix.GeneralLinearGroup.map (intEquiv i hi).symm.toRingHom u, rfl⟩, ?_⟩
  rw [map_alg i hi]
  congr 1
  ext a b
  simp

private theorem red_map (g : KO k (Fin n)) :
    redK K (Fin n) ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, map_mem_KO i hi g.2⟩ =
      Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) g) := by
  ext a b
  rw [redK_apply]
  show _ = resEquiv (intEquiv i hi) ((redK k (Fin n) g : Matrix (Fin n) (Fin n) 𝓀[k]) a b)
  rw [redK_apply]
  rfl

private theorem map_mem_KOne_iff {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KOne K (Fin n) ↔ g ∈ KOne k (Fin n) := by
  rw [← redK_eq_one_iff ⟨g, hg⟩, ← redK_eq_one_iff ⟨_, map_mem_KO i hi hg⟩, red_map i hi ⟨g, hg⟩]
  constructor
  · intro h
    have := congrArg (glEquiv (resEquiv (intEquiv i hi)) n).symm h
    rw [show Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) ⟨g, hg⟩) =
      glEquiv (resEquiv (intEquiv i hi)) n (redK k (Fin n) ⟨g, hg⟩) from rfl, Equiv.symm_apply_apply] at this
    rw [this]
    exact map_one (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).symm.toRingHom)
  · intro h
    rw [h, map_one]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) K) W) (e : V ≃ₗ[ℂ] W)
  (he : ∀ g x, e (π g x) = P (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x))

include he in
private theorem map_fixed :
    (fixed π (KOne k (Fin n))).map (e : V →ₗ[ℂ] W) = fixed P (KOne K (Fin n)) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_fixed.2 fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := exists_KO i hi (GlobalTheory.StepData.KOne_le_KO hy)
    show P _ (e x) = e x
    rw [← he, mem_fixed.1 hx g ((map_mem_KOne_iff i hi hg).1 hy)]
  · intro hw
    refine ⟨e.symm w, mem_fixed.2 fun g hg => ?_, by simp⟩
    apply e.injective
    rw [he, e.apply_symm_apply,
      mem_fixed.1 hw _ ((map_mem_KOne_iff i hi (GlobalTheory.StepData.KOne_le_KO hg)).2 hg)]

private def fixEquiv : fixed π (KOne k (Fin n)) ≃ₗ[ℂ] fixed P (KOne K (Fin n)) :=
  e.ofSubmodules _ _ (map_fixed i hi π P e he)

private theorem fixEquiv_level (γ : GL (Fin n) 𝓀[k]) (x : fixed π (KOne k (Fin n))) :
    fixEquiv i hi π P e he (levelZero π γ x) =
      levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)
        (fixEquiv i hi π P e he x) := by
  obtain ⟨g, rfl⟩ := redK_surjective γ
  rw [← red_map i hi g]
  apply Subtype.ext
  rw [levelZero_apply]
  show e (levelZero π (redK k (Fin n) g) x : V) = P _ (e x)
  rw [levelZero_apply, he]

include he in
private theorem trace_level (γ : GL (Fin n) 𝓀[k]) :
    LinearMap.trace ℂ _ (levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)) =
      LinearMap.trace ℂ _ (levelZero π γ) := by
  have h : levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ) =
      (fixEquiv i hi π P e he).conj (levelZero π γ) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (fixEquiv i hi π P e he).surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, fixEquiv_level]
  rw [h, LinearMap.trace_conj']

end SlopeTestRemainingChoices

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
theorem UpperTheory.Gal.InertialTypesAlt.lblIso :
    JDIso → LblIso := by
  intro hJ k _ _ _ _ K _ _ _ _ i hi j hj θ N V W _ _ _ _ π P e he a ha
  obtain ⟨hok, hq, hn, hm⟩ := ha
  have hjr : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (resEquiv (intEquiv i hi) x) := by
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact hj y (intEquiv i hi y) rfl
  refine ⟨hok, hq.trans (Nat.card_congr (resEquiv (intEquiv i hi)).toEquiv), hn, ?_⟩
  unfold Meets at hm ⊢
  rw [← finsum_comp_equiv (glEquiv (resEquiv (intEquiv i hi)) N)]
  have key : ∀ γ : GL (Fin N) 𝓀[k],
      star (JD θ a.D a.L N (glEquiv (resEquiv (intEquiv i hi)) N γ)) *
          LinearMap.trace ℂ _ (levelZero P (glEquiv (resEquiv (intEquiv i hi)) N γ)) =
        star (JD (θ.comp j.toMonoidHom) a.D a.L N γ) * LinearMap.trace ℂ _ (levelZero π γ) := by
    intro γ
    rw [← hJ _ _ (resEquiv (intEquiv i hi)) j hjr θ a.D a.L N γ, ← trace_level i hi π P e he γ]
    rfl
  rw [finsum_congr key]
  exact hm
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PResCl
noncomputable section

open GlobalTheory.Shin

namespace UpperTheory.Gal.InertialTypesAlt

section Blocks

variable {F : Type} [Field F] {a b : ℕ}

private def blk (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) F :=
  M.submatrix finSumFinEquiv finSumFinEquiv

private theorem blk_mul (M N : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    blk (M * N) = blk M * blk N :=
  (Matrix.submatrix_mul_equiv M N _ _ _).symm

private theorem tl_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    tl a M = (blk M).toBlocks₁₁ := by
  ext i j
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp [tl, ent, blk, Matrix.toBlocks₁₁, hi, hj]
  rfl

private theorem br_eq (M : Matrix (Fin (a + b)) (Fin (a + b)) F) :
    br a b M = (blk M).toBlocks₂₂ := by
  ext i j
  simp [br, ent, blk, Matrix.toBlocks₂₂]
  rfl

private theorem inPar_iff (x : GL (Fin (a + b)) F) :
    InPar a x ↔ (blk (x : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁ = 0 := by
  constructor
  · intro h
    ext i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    rcases j' with j' | j'
    · rcases i' with i' | i'
      · simp at hi; omega
      · exact congrFun (congrFun h i') j'
    · simp at hj

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private def dg (a : ℕ) (z : GL (Fin b) F) : GL (Fin (a + b)) F where
  val := (Matrix.fromBlocks 1 0 0 (z : Matrix (Fin b) (Fin b) F)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  inv := (Matrix.fromBlocks 1 0 0 ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F)).submatrix
    finSumFinEquiv.symm finSumFinEquiv.symm
  val_inv := by
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  inv_val := by
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private theorem blk_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    blk (((dg a z)⁻¹ * p * dg a z : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₁₁
        ((blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₁₂ * (z : Matrix (Fin b) (Fin b) F))
        (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) *
          (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₁)
        (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) *
          (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F)).toBlocks₂₂ *
            (z : Matrix (Fin b) (Fin b) F)) := by
  have h1 : blk (((dg a z)⁻¹ : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks 1 0 0 ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) := by
    ext i j
    simp [blk, dg, Units.inv_mk]
  have h2 : blk ((dg a z : GL (Fin (a + b)) F) : Matrix (Fin (a + b)) (Fin (a + b)) F) =
      Matrix.fromBlocks 1 0 0 (z : Matrix (Fin b) (Fin b) F) := by
    ext i j
    simp [blk, dg]
  rw [Units.val_mul, Units.val_mul, blk_mul, blk_mul, h1, h2,
    ← Matrix.fromBlocks_toBlocks (blk (p : Matrix (Fin (a + b)) (Fin (a + b)) F))]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.fromBlocks_multiply]
  simp

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private theorem toG_conj (z : GL (Fin b) F) (M : Matrix (Fin b) (Fin b) F) :
    toG (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M * (z : Matrix (Fin b) (Fin b) F)) =
      z⁻¹ * toG M * z := by
  by_cases h : IsUnit M
  · have h' : IsUnit (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M *
        (z : Matrix (Fin b) (Fin b) F)) :=
      ((Units.isUnit _).mul h).mul (Units.isUnit _)
    apply Units.ext
    simp [toG, h, h']
  · have h' : ¬ IsUnit (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M *
        (z : Matrix (Fin b) (Fin b) F)) := by
      intro hu
      apply h
      have : M = (z : Matrix (Fin b) (Fin b) F) *
          (((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) * M * (z : Matrix (Fin b) (Fin b) F)) *
            ((z⁻¹ : GL (Fin b) F) : Matrix (Fin b) (Fin b) F) := by
        simp [mul_assoc]
      rw [this]
      exact ((Units.isUnit _).mul hu).mul (Units.isUnit _)
    simp [toG, h, h']

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
  UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin
  UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self in
private theorem inPar_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    InPar a ((dg a z)⁻¹ * p * dg a z) ↔ InPar a p := by
  rw [inPar_iff, inPar_iff, blk_conj, Matrix.toBlocks_fromBlocks₂₁]
  constructor
  · intro h
    have := congrArg (fun X => (z : Matrix (Fin b) (Fin b) F) * X) h
    simpa [← mul_assoc] using this
  · intro h
    rw [h]
    exact Matrix.mul_zero _

private theorem tlG_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    tlG a ((dg a z)⁻¹ * p * dg a z) = tlG a p := by
  unfold tlG
  rw [tl_eq, tl_eq, blk_conj, Matrix.toBlocks_fromBlocks₁₁]

private theorem brG_conj (z : GL (Fin b) F) (p : GL (Fin (a + b)) F) :
    brG a b ((dg a z)⁻¹ * p * dg a z) = z⁻¹ * brG a b p * z := by
  unfold brG
  rw [br_eq, br_eq, blk_conj, Matrix.toBlocks_fromBlocks₂₂, toG_conj]

end Blocks

theorem resCl : ResCl := by
  intro F _ _ a b n hn T hT x y z
  subst hn
  unfold resT
  rw [← finsum_comp_equiv (MulAut.conj (dg a z)⁻¹).toEquiv]
  refine finsum_congr fun p => ?_
  have e : (MulAut.conj (dg a z)⁻¹).toEquiv p = (dg a z)⁻¹ * p * dg a z := by
    show (dg a z)⁻¹ * p * ((dg a z)⁻¹)⁻¹ = _
    rw [inv_inv]
  rw [e, inPar_conj, tlG_conj, brG_conj, hT]
  have : z⁻¹ * brG a b p * z = z⁻¹ * y * z ↔ brG a b p = y := by
    simp
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.1, h1.2.1, this.1 h1.2.2⟩ h2
  · exact absurd ⟨h2.1, h2.2.1, this.2 h2.2.2⟩ h1
  · rfl

end UpperTheory.Gal.InertialTypesAlt
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftOk
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Gal.InertialTypesAlt.coprime_pow_sub_one_self {q m : ℕ} (hm : 0 < m) (hq : 2 ≤ q) : Nat.Coprime (q ^ m - 1) q := by
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have e : q ^ m - 1 + 1 = q ^ m := by omega
  have a := Nat.gcd_dvd_left (q ^ m - 1) q
  have b := Nat.gcd_dvd_right (q ^ m - 1) q
  have c : Nat.gcd (q ^ m - 1) q ∣ q ^ m - 1 + 1 := by
    rw [e]
    exact b.trans (dvd_pow_self q hm.ne')
  exact Nat.dvd_one.1 ((Nat.dvd_add_right a).1 c)

private theorem UpperTheory.Gal.InertialTypesAlt.reg_dvd {q l m k : ℕ} (i : ℕ) (hq : 2 ≤ q) (hl : 0 < l) (hm : 0 < m) (hd : l ∣ m)
    (h : GlobalTheory.Shin.Reg q m k) : GlobalTheory.Shin.Reg (q ^ l) (m / l) (k * q ^ i) := by
  obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left c hl]
  intro j hj hjc hmod
  have hcop : Nat.gcd (q ^ (l * c) - 1) (q ^ i) = 1 :=
    Nat.Coprime.pow_right i (UpperTheory.Gal.InertialTypesAlt.coprime_pow_sub_one_self hm hq)
  refine h (l * j) (Nat.mul_pos hl hj) (Nat.mul_lt_mul_of_pos_left hjc hl) ?_
  rw [← pow_mul] at hmod
  apply Nat.ModEq.cancel_right_of_coprime hcop
  have e : k * q ^ (l * j) * q ^ i = k * q ^ i * (q ^ l) ^ j := by
    rw [← pow_mul]; ring
  rw [e]
  exact hmod

private theorem UpperTheory.Gal.InertialTypesAlt.reg_ndvd {q l m k : ℕ} (hq : 2 ≤ q) (hl : l.Prime) (hm : 0 < m) (hd : ¬ l ∣ m)
    (h : GlobalTheory.Shin.Reg q m k) : GlobalTheory.Shin.Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) := by
  intro j hj hjm hmod
  have hpos : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
  have hgt : 1 < q ^ m := Nat.one_lt_pow hm.ne' (by omega)
  have hx : q ^ m - 1 + 1 = q ^ m := by omega
  have hgeo := geom_sum_mul_add (q ^ m - 1) l
  rw [hx] at hgeo
  have hS : (∑ i ∈ Finset.range l, q ^ (m * i)) = ∑ i ∈ Finset.range l, (q ^ m) ^ i :=
    Finset.sum_congr rfl fun i _ => pow_mul q m i
  rw [← hS] at hgeo
  set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef
  have hbig : 1 < (q ^ m) ^ l := Nat.one_lt_pow hl.ne_zero hgt
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0] at hgeo
    omega
  have hmodulus : (q ^ l) ^ m - 1 = (q ^ m - 1) * S := by
    have : (q ^ l) ^ m = (q ^ m) ^ l := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [this, ← hgeo, Nat.mul_comm]
    simp
  rw [hmodulus] at hmod
  have e1 : k * (q ^ l) ^ j ≡ k [MOD q ^ m - 1] := by
    apply Nat.ModEq.mul_right_cancel' hS0
    have e : k * (q ^ l) ^ j * S = k * S * (q ^ l) ^ j := by ring
    rw [e]
    exact hmod
  have hone : q ^ m ≡ 1 [MOD q ^ m - 1] := by
    have : (q ^ m - 1) + 1 ≡ 0 + 1 [MOD q ^ m - 1] :=
      Nat.ModEq.add_right 1 (by simp [Nat.ModEq])
    rwa [hx] at this
  have hcop : Nat.Coprime m l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
  have hr0 : (l * j) % m ≠ 0 := by
    intro h0
    have h1 : m ∣ l * j := Nat.dvd_of_mod_eq_zero h0
    have h2 : m ∣ j := hcop.dvd_of_dvd_mul_left h1
    have := Nat.le_of_dvd hj h2
    omega
  have hrm : (l * j) % m < m := Nat.mod_lt _ hm
  have hpow : q ^ (l * j) ≡ q ^ ((l * j) % m) [MOD q ^ m - 1] := by
    have hsplit : q ^ (l * j) = (q ^ m) ^ ((l * j) / m) * q ^ ((l * j) % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hsplit]
    have := (hone.pow ((l * j) / m)).mul_right (q ^ ((l * j) % m))
    simpa using this
  refine h _ (Nat.pos_of_ne_zero hr0) hrm ?_
  have e2 : k * q ^ ((l * j) % m) ≡ k * q ^ (l * j) [MOD q ^ m - 1] := (hpow.mul_left k).symm
  refine e2.trans ?_
  rw [pow_mul]
  exact e1

private theorem UpperTheory.Gal.InertialTypesAlt.deg_append (A B : List (ℕ × ℕ)) :
    GlobalTheory.Shin.deg (A ++ B) = GlobalTheory.Shin.deg A + GlobalTheory.Shin.deg B := by
  simp [GlobalTheory.Shin.deg]

private theorem UpperTheory.Gal.InertialTypesAlt.block_dvd (q l : ℕ) (p : ℕ × ℕ) (hd : l ∣ p.1) :
    GlobalTheory.Shin.deg (GlobalTheory.Shin.liftL q l [p]) = p.1 := by
  have h : ((List.range l).map fun i => (p.1 / l, p.2 * q ^ i)).map Prod.fst = List.replicate l (p.1 / l) := by
    rw [List.map_map]
    apply List.eq_replicate_iff.2
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
    rfl
  have h2 : GlobalTheory.Shin.deg (GlobalTheory.Shin.liftL q l [p]) = (List.replicate l (p.1 / l)).sum := by
    rw [← h]
    simp [GlobalTheory.Shin.deg, GlobalTheory.Shin.liftL]
  rw [h2, List.sum_replicate, smul_eq_mul]
  exact Nat.mul_div_cancel' hd

private theorem UpperTheory.Gal.InertialTypesAlt.liftAll_spec (q l : ℕ) (L : List (ℕ × ℕ)) (hq : 2 ≤ q) (hl : l.Prime)
    (h : ∀ p ∈ L, 0 < p.1 ∧ GlobalTheory.Shin.Reg q p.1 p.2) :
    GlobalTheory.Shin.deg (GlobalTheory.Shin.liftAll q l L) = GlobalTheory.Shin.deg L ∧
      ∀ p ∈ GlobalTheory.Shin.liftAll q l L, 0 < p.1 ∧ GlobalTheory.Shin.Reg (q ^ l) p.1 p.2 := by
  induction L with
  | nil => simp [GlobalTheory.Shin.liftAll, GlobalTheory.Shin.deg]
  | cons p L ih =>
    obtain ⟨ih1, ih2⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨hp0, hpR⟩ := h p List.mem_cons_self
    have hsplit : GlobalTheory.Shin.liftAll q l (p :: L) =
        (if l ∣ p.1 then GlobalTheory.Shin.liftL q l [p] else [(p.1, p.2 * ∑ i ∈ Finset.range l, q ^ (p.1 * i))]) ++
          GlobalTheory.Shin.liftAll q l L := by
      simp only [GlobalTheory.Shin.liftAll, List.flatMap_cons]
    have hdegp : GlobalTheory.Shin.deg (p :: L) = p.1 + GlobalTheory.Shin.deg L := by simp [GlobalTheory.Shin.deg]
    rw [hsplit, UpperTheory.Gal.InertialTypesAlt.deg_append, ih1, hdegp]
    by_cases hd : l ∣ p.1
    · rw [if_pos hd]
      refine ⟨by rw [UpperTheory.Gal.InertialTypesAlt.block_dvd q l p hd], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · simp only [GlobalTheory.Shin.liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
        exact ⟨Nat.div_pos (Nat.le_of_dvd hp0 hd) hl.pos, UpperTheory.Gal.InertialTypesAlt.reg_dvd i hq hl.pos hp0 hd hpR⟩
      · exact ih2 x hx
    · rw [if_neg hd]
      refine ⟨by simp [GlobalTheory.Shin.deg], ?_⟩
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hp0, UpperTheory.Gal.InertialTypesAlt.reg_ndvd hq hl hp0 hd hpR⟩
      · exact ih2 x hx

theorem UpperTheory.Gal.InertialTypesAlt.liftOk :
    LiftOk := by
  intro a l hl hok
  obtain ⟨hq, hD, hL⟩ := hok
  obtain ⟨h1, h2⟩ := UpperTheory.Gal.InertialTypesAlt.liftAll_spec a.q l a.L hq hl hL
  have hD' : GlobalTheory.Shin.deg (a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i)) = GlobalTheory.Shin.deg a.D := by
    simp [GlobalTheory.Shin.deg, List.map_map, Function.comp_def]
  refine ⟨⟨?_, ?_, h2⟩, ?_⟩
  · show 2 ≤ a.q ^ l
    calc 2 ≤ a.q := hq
      _ ≤ a.q ^ l := Nat.le_self_pow hl.ne_zero a.q
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
    exact hD r hr
  · show GlobalTheory.Shin.deg (a.D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range l, a.q ^ i)) + GlobalTheory.Shin.deg (GlobalTheory.Shin.liftAll a.q l a.L) =
      GlobalTheory.Shin.deg a.D + GlobalTheory.Shin.deg a.L
    rw [hD', h1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PSubqMap
namespace UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

section SlopeTestRemainingChoices

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori
open GlobalTheory.Parabolic (mem_fixed)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = N} {W V Z : Type} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
  {ρ : Representation ℂ (Levi k fun a => Fin (d a)) W}

private theorem isSmooth_sub (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    IsSmooth S.toRepresentation := fun y => by
  have : {g : GL (Fin N) k | S.toRepresentation g y = y} =
      {g : GL (Fin N) k | parInd (stdBlocks d hd) ρ g y.1 = y.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact isSmooth_parInd _ _ y.1

private theorem levelZeroMap_surjective {S : Subrepresentation (parInd (stdBlocks d hd) ρ)}
    {π : Representation ℂ (GL (Fin N) k) V} (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) : Function.Surjective (levelZeroMap f) := by
  intro v
  obtain ⟨u0, hu0⟩ := hf v.1
  obtain ⟨u, hu, e⟩ := IwahoriOnto.exists_fixed_map_eq (isSmooth_sub S) DepthZero.isCompact_KOne₁
    f.toLinearMap u0 fun h hh => by
      show f (S.toRepresentation h u0) = f u0
      rw [f.isIntertwining, hu0]
      exact mem_fixed.1 v.2 h hh
  exact ⟨⟨u, hu⟩, Subtype.ext (e.trans hu0)⟩

private def evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) :
    fixed S.toRepresentation (KOne k (Fin N)) →ₗ[ℂ] W where
  toFun u := (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem evalOne_redK (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (κ : KO k (Fin N)) (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S (levelZero S.toRepresentation (redK k (Fin N) κ) u) =
      (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 κ := by
  show ((levelZero S.toRepresentation (redK k (Fin N) κ) u).1.1 : IndSp (stdBlocks d hd) ρ).1.1 1 = _
  rw [levelZero_apply]
  show ((parInd (stdBlocks d hd) ρ (κ : GL (Fin N) k) u.1.1 : IndSp (stdBlocks d hd) ρ)).1.1 1 = _
  rw [parInd_apply, one_mul]

private theorem val_mul_of_mem (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) (x : GL (Fin N) k) {c : GL (Fin N) k}
    (hc : c ∈ KOne k (Fin N)) :
    (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 (x * c) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 x := by
  have h : S.toRepresentation c u.1 = u.1 := mem_fixed.1 u.2 c hc
  have h2 : parInd (stdBlocks d hd) ρ c u.1.1 = u.1.1 := congrArg Subtype.val h
  exact congrArg (fun F : IndSp (stdBlocks d hd) ρ => F.1.1 x) h2

private theorem leviKOne_le_leviK {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {s : ℕ} {d : Fin s → ℕ} :
    leviKOne k (fun a => Fin (d a)) ≤ leviK k (fun a => Fin (d a)) := by
  intro l hl
  unfold leviKOne at hl
  unfold leviK
  rw [Subgroup.mem_pi] at hl ⊢
  exact fun a ha => GlobalTheory.StepData.KOne_le_KO (hl a ha)

private theorem evalOne_mem_fixed (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    evalOne S u ∈ fixed ρ (leviKOne k fun a => Fin (d a)) := by
  rw [mem_fixed]
  intro l hl
  have hpar := leviEmb_mem_parab k (stdBlocks d hd) l
  have hlaw := parInd_law (stdBlocks d hd) ρ (u.1.1 : IndSp (stdBlocks d hd) ρ) ⟨_, hpar⟩ 1
  have hK : leviEmb k (stdBlocks d hd) l ∈ KOne k (Fin N) := jLevi_le_KOne _ ⟨l, hl, rfl⟩
  have h4 := val_mul_of_mem S u 1 hK
  rw [one_mul] at h4
  simp only [mul_one, leviProj_leviEmb, deltaHalf_of_mem_leviK (leviKOne_le_leviK hl)] at hlaw
  show ρ l ((u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1) = (u.1.1 : IndSp (stdBlocks d hd) ρ).1.1 1
  rw [h4] at hlaw
  simpa using hlaw.symm

private theorem val_of_redK_mem (hPF : ParaFactor) (F : IndSp (stdBlocks d hd) ρ)
    (hF : ∀ x, ∀ c ∈ KOne k (Fin N), F.1.1 (x * c) = F.1.1 x)
    (κ₀ : KO k (Fin N)) (hκ : redK k (Fin N) κ₀ ∈ parab 𝓀[k] (stdBlocks d hd)) :
    ∃ x : leviK k fun a => Fin (d a),
      redLevi k _ x = leviProj 𝓀[k] (stdBlocks d hd) ⟨redK k (Fin N) κ₀, hκ⟩ ∧
      F.1.1 κ₀ = ρ (x : Levi k fun a => Fin (d a)) (F.1.1 1) := by
  have hg : (κ₀ : GL (Fin N) k) ∈ parahoric k (stdBlocks d hd) := (coe_mem_levelPre κ₀).2 hκ
  obtain ⟨p, x, -, hpx, hred, c, hc, hgp⟩ := (hPF k (stdBlocks d hd)).1 ⟨κ₀, hg⟩
  have h3 := parInd_law (stdBlocks d hd) ρ F p 1
  rw [mul_one, hpx, deltaHalf_of_mem_leviK x.2, Units.val_one, one_smul] at h3
  have h4 : (κ₀ : GL (Fin N) k) = p * c := hgp
  refine ⟨x, hred, ?_⟩
  rw [h4, hF _ c hc]
  exact h3


set_option maxHeartbeats 1000000 in
private theorem evalOne_parab (hPF : ParaFactor)
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ)) (h : parab 𝓀[k] (stdBlocks d hd))
    (u : fixed S.toRepresentation (KOne k (Fin N))) :
    Φ (evalOne S (levelZero S.toRepresentation (h : GL (Fin N) 𝓀[k]) u)) =
      κ (leviProj 𝓀[k] (stdBlocks d hd) h) (Φ (evalOne S u)) := by
  rcases h with ⟨h, hmem⟩
  obtain ⟨κ₀, rfl⟩ := redK_surjective h
  obtain ⟨x, hx1, hx2⟩ := val_of_redK_mem hPF (u.1.1 : IndSp (stdBlocks d hd) ρ)
    (fun y c hc => val_mul_of_mem S u y hc) κ₀ hmem
  exact (congrArg Φ ((evalOne_redK S κ₀ u).trans hx2)).trans
    ((hΦ x _).trans (congrArg (fun g => κ g (Φ (evalOne S u))) hx1))

private theorem eq_zero_of_evalOne (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (u : fixed S.toRepresentation (KOne k (Fin N)))
    (hu : ∀ γ : GL (Fin N) 𝓀[k], evalOne S (levelZero S.toRepresentation γ u) = 0) : u = 0 := by
  have hF : (u.1.1 : IndSp (stdBlocks d hd) ρ) = 0 :=
    UpperTheory.TNZ.step_indDetK k s N d hd W ρ _ 0 fun κ hκ => by
      have := hu (redK k (Fin N) ⟨κ, hκ⟩)
      rw [evalOne_redK] at this
      exact this
  exact Subtype.ext (Subtype.ext hF)

private theorem main (hPF : ParaFactor) {π : Representation ℂ (GL (Fin N) k) V}
    {κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z} {Φ : W →ₗ[ℂ] Z}
    (hΦ : ∀ (x : leviK k fun a => Fin (d a)) (w : W),
      Φ (ρ (x : Levi k fun a => Fin (d a)) w) = κ (redLevi k _ x) (Φ w))
    (hinj : ∀ w ∈ fixed ρ (leviKOne k fun a => Fin (d a)), Φ w = 0 → w = 0)
    (S : Subrepresentation (parInd (stdBlocks d hd) ρ))
    (sec : fixed π (KOne k (Fin N)) →ₗ[ℂ] fixed S.toRepresentation (KOne k (Fin N)))
    (hs : ∀ g x, sec (levelZero π g x) = levelZero S.toRepresentation g (sec x))
    (hinv : Function.Injective sec)
    (hfix : fixed π (KOne k (Fin N)) ≠ ⊥) :
    ∃ ψ : fixed π (KOne k (Fin N)) →ₗ[ℂ] Z, ψ ≠ 0 ∧
      ∀ (p : parab 𝓀[k] (stdBlocks d hd)) (x : fixed π (KOne k (Fin N))),
        ψ (levelZero π p x) = κ (leviProj 𝓀[k] (stdBlocks d hd) p) (ψ x) := by
  obtain ⟨x0, hx0mem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  let y0 : fixed π (KOne k (Fin N)) := ⟨x0, hx0mem⟩
  have hsx : sec y0 ≠ 0 := by
    intro h0
    apply hx0
    have h1 := hinv (h0.trans (map_zero sec).symm)
    exact congrArg Subtype.val h1
  have hγ : ∃ γ, evalOne S (levelZero S.toRepresentation γ (sec y0)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hsx (eq_zero_of_evalOne S _ hc)
  obtain ⟨γ, hγ⟩ := hγ
  refine ⟨Φ ∘ₗ (evalOne S ∘ₗ sec), ?_, ?_⟩
  · intro h0
    apply hγ
    apply hinj _ (evalOne_mem_fixed S _)
    have h1 := LinearMap.congr_fun h0 (levelZero π γ y0)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hs] at h1
    exact h1
  · intro p x
    have h3 := evalOne_parab hPF hΦ S p (sec x)
    calc (Φ ∘ₗ (evalOne S ∘ₗ sec)) (levelZero π p x)
        = Φ (evalOne S (levelZero S.toRepresentation p (sec x))) :=
          congrArg (fun w => Φ (evalOne S w)) (hs _ _)
      _ = _ := h3

end SlopeTestRemainingChoices

end UpperTheory.Gal.InertialTypesAlt.SubquotientMaps

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.Gal.InertialTypesAlt.SubquotientMaps in
set_option synthInstance.maxHeartbeats 400000 in
theorem UpperTheory.Gal.InertialTypesAlt.subqMap :
    FinSec → UpperTheory.Gal.TypesAndIwahori.ParaFactor → SubqMap := by
  intro hSec hPF k _ _ _ _ N s d hd W V Z _ _ _ _ _ _ ρ π κ Φ hΦ hinj hsq hfix
  obtain ⟨S, f, hf⟩ := hsq
  have : Finite (GL (Fin N) 𝓀[k]) := inferInstance
  obtain ⟨sec, hs, hfs⟩ := hSec (GL (Fin N) 𝓀[k])
    (fixed S.toRepresentation (KOne k (Fin N))) (fixed π (KOne k (Fin N)))
    (levelZero S.toRepresentation) (levelZero π) (levelZeroMap f).toLinearMap
    (fun g x => Representation.IntertwiningMap.isIntertwining _ _ (levelZeroMap f) g x) (levelZeroMap_surjective f hf)
  exact main hPF hΦ hinj S sec hs (Function.LeftInverse.injective hfs) hfix
end
