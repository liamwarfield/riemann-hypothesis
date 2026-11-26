module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLift

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem row_induction {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (C : ∀ i, Set (Fn G (.grid i 0))) : ∀ (n : ℕ) (f : ∀ i : Fin n, Sch G (.right (i : ℕ) 0)),
    (∀ (i : Fin n) F, F ∈ C i → LiftConv W M (.right (i : ℕ) 0) (f i) F ∧
      liftA W M (.right (i : ℕ) 0) (f i) F ∈ C ((i : ℕ) + 1)) →
    ∀ F ∈ C 0, PathConv W M (rowPath T 0 n) (rowFam 0 n f) F ∧ liftP W M (rowPath T 0 n) (rowFam 0 n f) F ∈ C n
  | 0, _, _, _, hF => ⟨trivial, hF⟩
  | n + 1, f, h, F, hF => by
    have ih := row_induction W M C n (fun i => f i.castSucc) (fun i F hF => h i.castSucc F hF) F hF
    have := h (Fin.last n) _ ih.2
    exact ⟨⟨ih.1, this.1⟩, this.2⟩

theorem isAutFun_zero (V : HSp D) : IsAutFun V (0 : GA D V → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩

theorem isAutFun_add {V : HSp D} {f g : GA D V → ℂ} (hf : IsAutFun V f) (hg : IsAutFun V g) : IsAutFun V (f + g) := by
  obtain ⟨U, hU, h⟩ := hf.level
  obtain ⟨U', hU', h'⟩ := hg.level
  refine ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.left γ hγ x, hg.left γ hγ x], ⟨U ⊓ U', hU.inter hU', fun k hk hf x => ?_⟩,
    hf.cont.add hg.cont⟩
  simp only [Pi.add_apply, h k hk.1 hf x, h' k hk.2 hf x]

theorem isAutFun_smul {V : HSp D} {f : GA D V → ℂ} (hf : IsAutFun V f) (a : ℂ) : IsAutFun V (a • f) := by
  obtain ⟨U, hU, h⟩ := hf.level
  refine ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.left γ hγ x], ⟨U, hU, fun k hk hf x => ?_⟩, hf.cont.const_smul a⟩
  simp only [Pi.smul_apply, h k hk hf x]

theorem isAutFun_of_mem_cusp (N : GlobalTheory.Grid.Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) := by
  obtain ⟨U, hU, rfl⟩ := Submodule.mem_map.1 hΦ
  clear hΦ
  have hU' : ∀ w, IsAutFun N.V (U w) := by
    induction hU using Submodule.span_induction with
    | mem x hx => exact fun w => (hx.aut w).toIsAutFun
    | zero => exact fun w => isAutFun_zero _
    | add x y _ _ hx hy => exact fun w => isAutFun_add (hx w) (hy w)
    | smul c x _ hx => exact fun w => isAutFun_smul (hx w) c
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => simpa using isAutFun_smul (hU' f) r
  | add x y hx hy => simpa using isAutFun_add hx hy

theorem start_mem {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (u : R.HE.H) :
    PiTensorProduct.lift (R.HE.e u) ∈ (GlobalTheory.Grid.nodeY R 0).Cusp R.θ := by
  have h1 : R.HE.e u ∈ R.EEat R.triv := h.models.HE.2.1 ▸ LinearMap.mem_range_self _ u
  have h2 := Formalism.IndefR.Mult.goodPart_le R.θ (R.MY 0) _ _ _ h1
  exact GlobalTheory.Grid.Node.multT_le_cusp (GlobalTheory.Grid.nodeY R 0) R.θ _ _ (Submodule.mem_map_of_mem h2)

theorem rowBase_of_core {F : Face D A} (h : GlobalTheory.Hk3.Core R F) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R :=
  ⟨h.lev, h.models.inf, h.models.νY, h.models.νY', h.models.νX⟩

end GlobalTheory.RowLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.ProdLength

section General
variable {F G U V X : Type} [Field F] [Group G] [AddCommGroup U] [Module F U] [AddCommGroup V]
  [Module F V] [AddCommGroup X] [Module F X]

def comapSub {α : Representation F G U} {β : Representation F G V} (ι : α.IntertwiningMap β)
    (S : Subrepresentation β) : Subrepresentation α :=
  ⟨S.toSubmodule.comap ι.toLinearMap, fun g v hv => by
    show ι (α g v) ∈ S.toSubmodule
    rw [Representation.IntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv⟩

def mapSub {β : Representation F G V} {γ : Representation F G X} (p : β.IntertwiningMap γ)
    (S : Subrepresentation β) : Subrepresentation γ :=
  ⟨S.toSubmodule.map p.toLinearMap, by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨β g v, S.apply_mem_toSubmodule g hv, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _ p g v⟩

theorem hasFiniteLength_of_exact {α : Representation F G U} {β : Representation F G V}
    {γ : Representation F G X} (ι : α.IntertwiningMap β) (p : β.IntertwiningMap γ)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) (hα : HasFiniteLength α) (hγ : HasFiniteLength γ) :
    HasFiniteLength β := by
  obtain ⟨hα1, hα2⟩ := (hasFiniteLength_iff_wellFounded α).1 hα
  obtain ⟨hγ1, hγ2⟩ := (hasFiniteLength_iff_wellFounded γ).1 hγ
  let f : Subrepresentation β → Subrepresentation α × Subrepresentation γ :=
    fun S => (comapSub ι S, mapSub p S)
  have hmono : Monotone f := fun S T h =>
    ⟨fun v hv => h hv, Submodule.map_mono (f := p.toLinearMap) h⟩
  have hf : StrictMono f := by
    intro S T hST
    refine lt_of_le_of_ne (hmono hST.le) fun heq => hST.not_ge ?_
    have h1 : (comapSub ι S).toSubmodule = (comapSub ι T).toSubmodule := congrArg (fun x => x.1.toSubmodule) heq
    have h2 : (mapSub p S).toSubmodule = (mapSub p T).toSubmodule := congrArg (fun x => x.2.toSubmodule) heq
    intro x hx
    have hpx : p x ∈ (mapSub p T).toSubmodule := ⟨x, hx, rfl⟩
    rw [← h2] at hpx
    obtain ⟨y, hy, hyx⟩ := hpx
    have hyx' : p y = p x := hyx
    obtain ⟨u, hu⟩ := hex (x - y) (by rw [map_sub, hyx', sub_self])
    have huT : u ∈ (comapSub ι T).toSubmodule := by
      show ι u ∈ T.toSubmodule
      rw [hu]
      exact T.toSubmodule.sub_mem hx (hST.le hy)
    rw [← h1] at huT
    have huS : ι u ∈ S.toSubmodule := huT
    rw [hu] at huS
    have := S.toSubmodule.add_mem huS hy
    rwa [sub_add_cancel] at this
  exact (hasFiniteLength_iff_wellFounded β).2 ⟨hf.wellFoundedGT, hf.wellFoundedLT⟩

theorem hasFiniteLength_of_injective {α : Representation F G U} {β : Representation F G V}
    (ι : α.IntertwiningMap β) (hι : Function.Injective ι) (hβ : HasFiniteLength β) :
    HasFiniteLength α := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded β).1 hβ
  have hmono : Monotone (mapSub ι) := fun S T h => Submodule.map_mono (f := ι.toLinearMap) h
  have hf : StrictMono (mapSub ι) := by
    intro S T hST
    refine lt_of_le_of_ne (hmono hST.le) fun heq => hST.not_ge ?_
    have h3 : (mapSub ι S).toSubmodule = (mapSub ι T).toSubmodule := congrArg (·.toSubmodule) heq
    intro x hx
    have hx' : ι x ∈ (mapSub ι T).toSubmodule := ⟨x, hx, rfl⟩
    rw [← h3] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    rwa [← hι hyx]
  exact (hasFiniteLength_iff_wellFounded α).2 ⟨hf.wellFoundedGT, hf.wellFoundedLT⟩

theorem hasFiniteLength_of_subsingleton [Subsingleton V] (β : Representation F G V) :
    HasFiniteLength β := by
  haveI : Subsingleton (Subrepresentation β) := ⟨fun S T => by
    ext v
    rw [Subsingleton.elim v 0]
    exact ⟨fun _ => T.toSubmodule.zero_mem, fun _ => S.toSubmodule.zero_mem⟩⟩
  exact (hasFiniteLength_iff_wellFounded β).2 ⟨Finite.to_wellFoundedGT, Finite.to_wellFoundedLT⟩

end General

section Tensor
open GlobalTheory.ParIndExact
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasFiniteLength_extTensor_left (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hA : HasFiniteLength A)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ G Y), σ.IsIrreducible →
      IsSubquotient σ A → HasFiniteLength (extTensor σ B)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded A).1 hA
  have key : ∀ S T : Subrepresentation A, T ≤ S → HasFiniteLength (extTensor (subQuot S T) B) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor (subQuot S T) B)) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_left (F := ℂ)
        (V := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule) (W := W)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := A) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_left B ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot A
  obtain ⟨ι', hι'⟩ := extTensor_injective_left B ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

theorem hasFiniteLength_extTensor_right (A : Representation ℂ G V) (B : Representation ℂ H W)
    (hB : HasFiniteLength B)
    (hbase : ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H Y), τ.IsIrreducible →
      IsSubquotient τ B → HasFiniteLength (extTensor A τ)) :
    HasFiniteLength (extTensor A B) := by
  obtain ⟨h1, h2⟩ := (hasFiniteLength_iff_wellFounded B).1 hB
  have key : ∀ S T : Subrepresentation B, T ≤ S → HasFiniteLength (extTensor A (subQuot S T)) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (extTensor A (subQuot S T))) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt
    · subst hEq
      haveI := subsingleton_subQuot_self T
      haveI := tensor_subsingleton_right (F := ℂ) (V := V)
        (W := ↥T.toSubmodule ⧸ Submodule.comap T.toSubmodule.subtype T.toSubmodule)
      exact hasFiniteLength_of_subsingleton _
    by_cases hc : T ⋖ S
    · exact hbase _ _ (isIrreducible_subQuot hc) (isSubquotient_subQuot S T)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hc ⟨hlt, fun U h1 h2 => hno ⟨U, h1, h2⟩⟩
    obtain ⟨ι, p, hι, hp, hpι, hex⟩ := subQuot_exact (ρ := B) hTU.le hUS.le
    obtain ⟨ι', p', -, hex'⟩ := extTensor_exact_right A ι p hι hp hpι hex
    exact hasFiniteLength_of_exact ι' p' hex' (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  obtain ⟨ι, hι⟩ := subQuot_top_bot B
  obtain ⟨ι', hι'⟩ := extTensor_injective_right A ι hι
  exact hasFiniteLength_of_injective ι' hι' (key ⊤ ⊥ bot_le)

end Tensor
end GlobalTheory.ProdLength

theorem GlobalTheory.ProdLength.prod₂_hasFiniteLength : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ → HasFiniteLength (prod₂ π₁ π₂) := by
  intro hBZ k _ _ _ _ r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂
  obtain ⟨hAdm, -, hInd, -⟩ := hBZ k
  have schur : ∀ (n : ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (σ : Representation ℂ (GL (Fin n) k) Y),
      IsSmooth σ → σ.IsIrreducible → ∀ φ : Y →ₗ[ℂ] Y, (∀ g x, φ (σ g x) = σ g (φ x)) →
        ∃ c : ℂ, φ = c • LinearMap.id := fun n Y _ _ σ hs hi =>
    GlobalTheory.SchurAdm.schur_admissible _ (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO Y σ hi
      (hAdm (Fin n) Y σ hs hi)
  have hT : HasFiniteLength (extTensor π₁ π₂) :=
    GlobalTheory.ProdLength.hasFiniteLength_extTensor_left π₁ π₂ h₁ fun Y _ _ σ hσ hsq =>
      GlobalTheory.ProdLength.hasFiniteLength_extTensor_right σ π₂ h₂ fun Z _ _ τ hτ hsq' =>
        hasFiniteLength_of_isIrreducible (GlobalTheory.JacFactor.isIrreducible_extTensor σ τ hσ hτ
          (schur r Y σ (hsq.isSmooth s₁) hσ) (schur t Z τ (hsq'.isSmooth s₂) hτ))
  have hc : Continuous (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom :=
    (continuous_apply false).prodMk (continuous_apply true)
  exact hInd Bool (Fin (r + t)) (Two (Fin r) (Fin t)) (two (stdSum rfl)) _ _
    (isSmooth_comp (isSmooth_extTensor s₁ s₂) _ hc)
    ((hasFiniteLength_comp_iff _ _ (leviTwo k (Fin r) (Fin t)).symm.surjective).2 hT)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGLStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicProduct_hasFiniteLength_GL : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), HasFiniteLength π₁ → HasFiniteLength π₂ → IsSmooth π₁ → IsSmooth π₂ → HasFiniteLength (prod₂ π₁ π₂) := by
  first | exact @GlobalTheory.ProdLength.prod₂_hasFiniteLength | exact GlobalTheory.ProdLength.prod₂_hasFiniteLength | (intros; apply GlobalTheory.ProdLength.prod₂_hasFiniteLength <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBplus

open GlobalTheory.Per GlobalTheory.Per.Inhab
open scoped Pointwise

variable {D : D7}

theorem integrable_of_haar {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}
    {Q : GA D A → GA D B → ℂ} (hQ : IsRatInv ι e Q) (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hc : Continuous fun q : GA D A × NFlag B e => Q q.1 q.2) {μ : Measure (GA D A)} {𝓕 : Set (GA D A)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 μ) {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)}
    (hN : IsUnitN B e ν 𝓝) :
    (∀ g, IntegrableOn (fun n : NFlag B e => Q g n) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, Q g n ∂ν) 𝓕 μ := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  haveI := hμ
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ A) hK hcov μ h𝓕
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hc.continuousOn
  refine FJConv.iterated_integrableOn hfin.ne (by rw [hN.2.2]; exact ENNReal.one_ne_top) hc (M := M) fun g n => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hQ.norm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine le_trans (le_of_eq ?_) (hM (k, k') ⟨hk, hk'⟩)
  rw [e1, hQ.conj k _ (mul_mem γ'.2 k'.2) γ hγ _ ((hs _ _).2 rfl), hQ.left k _ k'.2 _ γ'.2 hγ']

theorem isAutFun_star {V : HSp D} {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (star φ) := by
  obtain ⟨U, hU, hUφ⟩ := h.level
  exact ⟨fun γ hγ g => by simp only [Pi.star_apply, h.left γ hγ g],
    ⟨U, hU, fun k hk hkf g => by simp only [Pi.star_apply, hUφ k hk hkf g]⟩, h.cont.star⟩

section Col

open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols levPlus mem_cols)

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D)

theorem coefPlus_fin {h : GA D (G.V (.top 0))} (hh : h ∈ GfC (G.V (.top 0))) : (coefPlus G θ).ρ h = 1 := by
  have e : GlobalTheory.CoefModel.realGL θ (Xp G) h = 1 := funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom (Xp G) h) = 1
    rw [show infHom (Xp G) h = 1 from hh, map_one]
  show GlobalTheory.CoefModel.rhoH _ _ (invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h)) = 1
  rw [e, map_one, map_one]

theorem coefPlus_cont (hθ : IsInfFam θ) (x : (coefPlus G θ).W) : Continuous fun h => (coefPlus G θ).ρ h x := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  refine GlobalTheory.CoefModel.continuous_rhoH _ _ (fun h => invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h)) (fun τ => ?_) x
  refine (((GlobalTheory.CoefModel.realGL_laws hθ (Xp G)).1 τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
  show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹ τ : Matrix (Fin (Xp G).rank) (Fin (Xp G).rank) ℂ) = _
  rw [map_inv]
  rfl

theorem rho_cancel (ξ : Module.Dual ℂ (coefPlus G θ).W) (x : (coefPlus G θ).W) (γ g : GA D (G.V (.top 0))) :
    ξ ((coefPlus G θ).ρ (γ * g)⁻¹ ((coefPlus G θ).ρ γ x)) = ξ ((coefPlus G θ).ρ g⁻¹ x) := by
  have key : (coefPlus G θ).ρ (γ * g)⁻¹ * (coefPlus G θ).ρ γ = (coefPlus G θ).ρ g⁻¹ := by
    rw [← MonoidHom.map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [← Module.End.mul_apply, key]

theorem rho_right (ξ : Module.Dual ℂ (coefPlus G θ).W) (x : (coefPlus G θ).W) (k g : GA D (G.V (.top 0)))
    (hk : (coefPlus G θ).ρ k⁻¹ = 1) :
    ξ ((coefPlus G θ).ρ (g * k)⁻¹ x) = ξ ((coefPlus G θ).ρ g⁻¹ x) := by
  rw [mul_inv_rev, MonoidHom.map_mul (coefPlus G θ).ρ k⁻¹ g⁻¹, Module.End.mul_apply, hk, Module.End.one_apply]

theorem col_right {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) (g : GA D (G.V (.top 0)))
    {k : GA D (G.V (.top 0))} (hk : k ∈ (G.Kplus).comap (Lev.finE (G.V (.top 0)))) :
    Ψ ((finHom (G.V (.top 0))).rangeRestrict (g * k)) = Ψ ((finHom (G.V (.top 0))).rangeRestrict g) := by
  have hk2 : (finHom (G.V (.top 0))).rangeRestrict k ∈ levPlus G := by
    rw [Subgroup.mem_comap] at hk
    rw [levPlus, Subgroup.mem_comap, Lev.toAfE, Subgroup.mem_comap]
    exact hk
  have h1 := (mem_cols G θ Ψ).1 hΨ 1 ((finHom (G.V (.top 0))).rangeRestrict g) ⟨_, hk2⟩
  simp only [map_one, one_mul, OneMemClass.coe_one, Module.End.one_apply] at h1
  rw [map_mul]; exact h1

theorem pairVec_left (ξ : Module.Dual ℂ (coefPlus G θ).W) {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W}
    (hΨ : Ψ ∈ Cols G θ) {γ : GA D (G.V (.top 0))} (hγ : γ ∈ GQ (G.V (.top 0))) (g : GA D (G.V (.top 0))) :
    pairVec (coefPlus G θ) ξ Ψ (γ * g) = pairVec (coefPlus G θ) ξ Ψ g := by
  rw [pairVec_apply, pairVec_apply]
  have h1 := (mem_cols G θ Ψ).1 hΨ ⟨γ, hγ⟩ ((finHom (G.V (.top 0))).rangeRestrict g) 1
  simp only [OneMemClass.coe_one, mul_one] at h1
  have e1 : (finHom (G.V (.top 0))).rangeRestrict (γ * g) =
      Bridge.ratF (G.V (.top 0)) ⟨γ, hγ⟩ * (finHom (G.V (.top 0))).rangeRestrict g := map_mul _ _ _
  rw [e1, h1]
  exact rho_cancel G θ ξ _ γ g

theorem pairVec_right (ξ : Module.Dual ℂ (coefPlus G θ).W) {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W}
    (hΨ : Ψ ∈ Cols G θ) {k : GA D (G.V (.top 0))} (hk : k ∈ (G.Kplus).comap (Lev.finE (G.V (.top 0))))
    (hkf : k ∈ GfC (G.V (.top 0))) (g : GA D (G.V (.top 0))) :
    pairVec (coefPlus G θ) ξ Ψ (g * k) = pairVec (coefPlus G θ) ξ Ψ g := by
  rw [pairVec_apply, pairVec_apply, col_right G θ hΨ g hk]
  exact rho_right G θ ξ _ k g (coefPlus_fin G θ (inv_mem hkf))

theorem pairVec_cont (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (coefPlus G θ).W)
    {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) :
    Continuous (pairVec (coefPlus G θ) ξ Ψ) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hU := (congLev_open_compact (G.V (.top 0)) (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd) (G.pl.modul_ne_bot sc)).1
  refine continuous_iff_continuousAt.2 fun h0 => ?_
  have hn : h0 • (((G.Kplus).comap (Lev.finE (G.V (.top 0))) : Subgroup _) : Set (GA D (G.V (.top 0)))) ∈ nhds h0 :=
    (hU.leftCoset h0).mem_nhds ⟨1, one_mem _, mul_one h0⟩
  have hev : (fun h => pairVec (coefPlus G θ) ξ Ψ h) =ᶠ[nhds h0]
      fun h => ξ ((coefPlus G θ).ρ h⁻¹ (Ψ ((finHom (G.V (.top 0))).rangeRestrict h0))) := by
    filter_upwards [hn] with h hh
    obtain ⟨k, hk, rfl⟩ := hh
    rw [pairVec_apply]
    simp only [smul_eq_mul]
    rw [col_right G θ hΨ h0 hk]
  refine ContinuousAt.congr ?_ hev.symm
  exact ((LinearMap.continuous_of_finiteDimensional ξ).comp ((coefPlus_cont G θ hθ _).comp continuous_inv)).continuousAt

theorem pairVec_isAutFun (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (coefPlus G θ).W)
    {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) :
    IsAutFun (G.V (.top 0)) (pairVec (coefPlus G θ) ξ Ψ) := by
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  exact ⟨fun γ hγ g => pairVec_left G θ ξ hΨ hγ g,
    ⟨_, (congLev_open_compact (G.V (.top 0)) (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hV.sd) (G.pl.modul_ne_bot sc)).1,
      fun k hk hkf g => pairVec_right G θ ξ hΨ hk hkf g⟩, pairVec_cont G θ hθ ξ hΨ⟩

end Col

theorem bplusConv_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (_hM : M.IsRow) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W)
    (Ψ : Bridge.Gf (G.V (.top 0)) → (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W) (_hΨ : Ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.Cols G W.θ)
    (F : GA D (G.V (.grid D.R.m 0)) → ℂ) (_hF : IsAutFun (G.V (.grid D.R.m 0)) F),
    BplusConv W M (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ) ξ Ψ) F := by
  intro D T L sc G W M hM ξ Ψ hΨ F hF
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
    rw [hV.sig τ, hV.rank]; simp [Node.neg]
  have hφ := isAutFun_star (pairVec_isAutFun G W.θ W.θ_is ξ hΨ)
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hs : ∀ h, EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h :=
    fun h => (embRel_iff _ h _).2 rfl
  have hQ : IsRatInv (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι G.besTop.e
      (fun h n => star (star (pairVec _ ξ Ψ) h) * F (n * embTop G h * (G.besTop.y : GA D _)) *
        star (besChar W.ψ G.besTop n)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro δ γ h n hn
      exact (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ h n hn).1
    · intro g n hn γ hγ hq
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop γ n hγ hn,
        GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop γ hγ hq, one_mul,
        mul_assoc γ, mul_assoc γ, hF.left γ hq]
    · intro g n hn γ hγ δ hδ
      obtain ⟨s₀, -, hrel, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _ hι
      have he : embTop G = s₀ := funext fun h => (hrel h _).1 (hs h)
      have hc : F (δ * n * δ⁻¹ * embTop G (γ * g) * G.besTop.y) =
          F (n * embTop G g * G.besTop.y) := by
        rw [he, (hrel _ _).1 hδ, ← hF.left _ (hq γ hγ) (n * s₀ g * G.besTop.y)]
        simp only [map_mul, mul_assoc, inv_mul_cancel_left]
      rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ hδ n hn).2, hc, hφ.left γ hγ]
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  have H := integrable_of_haar hQ G.besTop.e_iso hι hA
    (((hφ.cont.comp continuous_fst).star.mul (hF.cont.comp (((continuous_subtype_val.comp continuous_snd).mul
      ((emb_continuous hι hs).comp continuous_fst)).mul continuous_const))).mul
      ((GlobalTheory.BesselChar.besChar_continuous W.ψ W.ψ_std.1 G.besTop).comp continuous_snd).star) hμ h𝓕 hM.unip
  unfold BplusConv
  rw [besInt_eq]
  exact H

end GlobalTheory.RowBplus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumnStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorank_converges_column : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (_hM : M.IsRow) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W)
    (Ψ : Bridge.Gf (G.V (.top 0)) → (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W) (_hΨ : Ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.Cols G W.θ)
    (F : GA D (G.V (.grid D.R.m 0)) → ℂ) (_hF : IsAutFun (G.V (.grid D.R.m 0)) F),
    BplusConv W M (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ) ξ Ψ) F := by
  first | exact @GlobalTheory.RowBplus.bplusConv_col | exact GlobalTheory.RowBplus.bplusConv_col | (intros; apply GlobalTheory.RowBplus.bplusConv_col <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem evI_eq (a : AF F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = evIHom F a := rfl

def embI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (evIHom F).comp (algebraMap F (AF F))

theorem countable_F : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

def infAd (m : mixedEmbedding.mixedSpace F) : AF F :=
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem evIHom_infAd (m : mixedEmbedding.mixedSpace F) : evIHom F (infAd m) = m := by
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) = m
  exact RingEquiv.apply_symm_apply _ m

theorem mul_infAd {u : AF F} (hu : evIHom F u = 0) (m : mixedEmbedding.mixedSpace F) : u * infAd m = 0 := by
  have h1 : u.1 = 0 := by
    have : (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  show (u.1 * _, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
  rw [h1, zero_mul, mul_zero]

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

def bI (F : Type) [Field F] [NumberField F] :
    Module.Basis (Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F))) ℝ (mixedEmbedding.mixedSpace F) :=
  Module.finBasis ℝ (mixedEmbedding.mixedSpace F)

def pI {κ : Type} (ξ : κ → F) : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ :=
  fun ij => Algebra.trace ℝ _ (embI F (ξ ij.1) * bI F ij.2)

def mI {κ : Type} (t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) (i : κ) :
    mixedEmbedding.mixedSpace F :=
  (-(1 / (2 * Real.pi))) • ∑ j, t (i, j) • bI F j

theorem psi_dot {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {κ : Type} [Fintype κ]
    (t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) (ξ : κ → F) :
    ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) =
      Complex.exp (((∑ ij, pI ξ ij * t ij : ℝ) : ℂ) * Complex.I) := by
  set a := (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i) with ha
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) a := by
    intro u hu
    rw [evI_eq] at hu
    show u * a = 0
    simp only [ha, dotProduct, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_left_comm, mul_infAd hu, mul_zero]
  rw [hψ.2.2 a hAt, evI_eq]
  have hev : evIHom F a = ∑ i, embI F (ξ i) * mI t i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ha, dotProduct, map_sum, map_mul, evIHom_infAd, embI, RingHom.comp_apply]
  have htr : Algebra.trace ℝ _ (evIHom F a) = -(1 / (2 * Real.pi)) * ∑ ij, pI ξ ij * t ij := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hev, map_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [mI, mul_smul_comm, Finset.mul_sum, map_smul, map_sum, smul_eq_mul, pI]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [htr]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

theorem pI_eq_zero {κ : Type} {ξ : κ → F} (h : pI ξ = 0) : ξ = 0 := by
  funext i
  by_contra hne
  have hz : ∀ z, Algebra.trace ℝ _ (embI F (ξ i) * z) = 0 := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (bI F).sum_repr z, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, show Algebra.trace ℝ _ (embI F (ξ i) * bI F j) = 0 from congrFun h (i, j),
      smul_zero]
  have h1 := hz (embI F (ξ i)⁻¹)
  rw [← map_mul, mul_inv_cancel₀ hne, map_one, ← map_one (algebraMap ℝ (mixedEmbedding.mixedSpace F)),
    Algebra.trace_algebraMap, mixedEmbedding.finrank, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h1
  exact (Module.finrank_pos (R := ℚ) (M := F)).ne' h1

theorem pI_zero {κ : Type} : pI (0 : κ → F) = 0 := by
  funext ij
  simp [pI]

theorem coeff_zero {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (c : (κ → F) → ℂ) (hc : Summable fun ξ => ‖c ξ‖)
    (h : ∀ t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ,
      ∑' ξ : κ → F, ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) * c ξ = 0) :
    c 0 = 0 := by
  classical
  letI : MeasurableSpace (κ → F) := ⊤
  haveI : MeasurableSingletonClass (κ → F) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  haveI : Countable F := countable_F
  have hint : Integrable c Measure.count := integrable_count_iff.mpr hc
  have hp : Measurable (pI (F := F) (κ := κ)) := fun _ _ => MeasurableSpace.measurableSet_top
  have key := GlobalTheory.FourierPush.setIntegral_preimage_eq_zero (κ → F) Measure.count c hint
    (κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) pI hp ?_ {0} (measurableSet_singleton 0)
  · have hpre : pI ⁻¹' {0} = ({0} : Set (κ → F)) := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨pI_eq_zero, fun h => h ▸ pI_zero⟩
    rw [hpre, integral_singleton] at key
    simpa using key
  · intro l
    have hI : Integrable (fun ξ => Complex.exp ((l (pI ξ) : ℂ) * Complex.I) * c ξ) Measure.count := by
      refine integrable_count_iff.mpr (hc.congr fun ξ => ?_)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [integral_countable hI]
    have hl : ∀ ξ : κ → F, l (pI ξ) = ∑ ij, pI ξ ij * l (fun k => if ij = k then 1 else 0) := by
      intro ξ
      rw [show l (pI ξ) = l.toLinearMap (pI ξ) from rfl, LinearMap.pi_apply_eq_sum_univ]
      simp [smul_eq_mul]
    have := h (fun ij => l (fun k => if ij = k then 1 else 0))
    rw [← this]
    refine tsum_congr fun ξ => ?_
    rw [psi_dot hψ, ← hl]
    simp

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj

theorem theta_inj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), ∀ (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ),
    IsDatum M ψ crd Φ₁ f → IsDatum M ψ crd Φ₂ f → Φ₁ = Φ₂ := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd Φ₁ Φ₂ f h₁ h₂
  funext x
  have hs : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) →
      Summable fun ξ : Fin n × Fin d → F => ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ := by
    intro Φ hΦ
    have := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    exact this
  have hsum : Summable fun ξ : Fin n × Fin d → F =>
      ‖Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ := by
    refine ((hs Φ₁ h₁.1).add (hs Φ₂ h₂.1)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
  have key := coeff_zero hψ
    (fun ξ => Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x))
    hsum ?_
  · have h0 : (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)) + x = x := by
      funext i; simp
    simp only [h0, sub_eq_zero] at key
    exact key
  · intro t
    have hn : ∀ ξ : Fin n × Fin d → F,
        ‖ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i))‖ = 1 := fun ξ => by
      rw [psi_dot hψ]; exact Complex.norm_exp_ofReal_mul_I _
    have hS : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) → Summable fun ξ : Fin n × Fin d → F =>
        ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) *
          Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) := fun Φ hΦ =>
      Summable.of_norm ((hs Φ hΦ).congr fun ξ => by rw [norm_mul, hn, one_mul])
    have hT : ∀ Φ, IsDatum M ψ crd Φ f →
        ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) * ∑' ξ : Fin n × Fin d → F,
          ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) *
            Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) =
          f (crd (M.co.e.symm (x, fun i => infAd (mI t i)))) := by
      intro Φ hΦ
      rw [← hΦ.2 (M.co.e.symm (x, fun i => infAd (mI t i))), ← tsum_mul_left]
      simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, LinearEquiv.apply_symm_apply,
        AddChar.map_add_eq_mul]
      refine tsum_congr fun ξ => ?_
      ring
    have hne : ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) ≠ 0 := by
      intro h0
      have := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i)))
        (-(⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))))
      rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
      exact one_ne_zero this
    have e2 := mul_left_cancel₀ hne ((hT Φ₁ h₁).trans (hT Φ₂ h₂).symm)
    simp only [mul_sub]
    rw [(hS Φ₁ h₁.1).tsum_sub (hS Φ₂ h₂.1), e2, sub_self]

end GlobalTheory.ThetaInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzDatum_eq_of_thetaFunction_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), ∀ (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ), IsDatum M ψ crd Φ₁ f → IsDatum M ψ crd Φ₂ f → Φ₁ = Φ₂ := by
  first | exact @GlobalTheory.ThetaInj.theta_inj | exact GlobalTheory.ThetaInj.theta_inj | (intros; apply GlobalTheory.ThetaInj.theta_inj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.BrRat

open MvPolynomial _root_.Formalism.L2.Col Formalism.L2.Ker

section General

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem projVV_of_mem {K : Type} [Field K] [CharZero K] (sg : ι → DomWeight n) (x : VV K sg) :
    Br.projVV sg x.1 = x := by
  have h := GlobalTheory.Proof.TensorMapDescent.eq_zero_of_fockB sg (Br.projVV sg x.1 - x) fun i => by
    rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply,
      GlobalTheory.Proof.TensorMapDescent.fockB_projVV_basis, sub_self]
  exact sub_eq_zero.mp h

theorem exists_map_eq {K : Type} [Field K] (φ : K →+* ℂ) {σ : Type} (P : MvPolynomial σ ℂ)
    (h : ∀ m, AddMonoidAlgebra.coeff P m ∈ Set.range φ) : ∃ P₀ : MvPolynomial σ K, map φ P₀ = P := by
  classical
  choose c hc using h
  refine ⟨∑ m ∈ P.support, monomial m (c m), ?_⟩
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_monomial, hc]

theorem descend {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (sg : ι → DomWeight n) (x : VV ℂ sg)
    (h : ∀ m, AddMonoidAlgebra.coeff x.1 m ∈ Set.range φ) : ∃ y : VV K sg, map φ y.1 = x.1 := by
  obtain ⟨P₀, hP⟩ := exists_map_eq φ x.1 h
  refine ⟨Br.projVV sg P₀, ?_⟩
  rw [← GlobalTheory.Proof.TensorMapDescent.projVV_map φ sg P₀, hP, projVV_of_mem]

theorem map_frDet {K : Type} [Field K] (φ : K →+* ℂ) (τ : ι) : map φ (frDet K n τ) = frDet ℂ n τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext a s
  simp

theorem map_dualSubst {K : Type} [Field K] (φ : K →+* ℂ) (P : Pol K ι n) :
    map φ (dualSubst K ι n P) = dualSubst ℂ ι n (map φ P) := by
  have e : (map φ : Pol K ι n →+* Pol ℂ ι n).comp (dualSubst K ι n).toRingHom =
      (dualSubst ℂ ι n).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [dualSubst]
    · intro v
      have hm : (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol ℂ ι n)) =
          (map φ : Pol K ι n →+* Pol ℂ ι n).mapMatrix (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol K ι n)) := by
        ext a s
        simp
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, dualSubst, aeval_X, map_X]
      rw [hm, ← RingHom.map_adjugate]
      rfl
  exact DFunLike.congr_fun e P

theorem isFunForm_map {K : Type} [Field K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {F : VV K σ}
    {f : VV K fun τ => (σ τ).dual} (h : IsFunForm σ F f) :
    IsFunForm σ ⟨map φ F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ F.2⟩
      ⟨map φ f.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ _ _ f.2⟩ := by
  unfold IsFunForm at h ⊢
  have h1 := congrArg (map φ) h
  simp only [map_mul, map_prod, map_pow, map_frDet, map_dualSubst] at h1
  exact h1

theorem covOf_eq (σ : ι → DomWeight n) (f : VV ℂ fun τ => (σ τ).dual) : covOf σ f = (funEquiv σ).symm f := by
  have hex : ∃ φ : (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] VV ℂ σ, ∀ f, IsFunForm σ (φ f) f :=
    ⟨(funEquiv σ).symm.toLinearMap, fun f => (isFunForm_iff_eq σ _ f).2 (by simp)⟩
  have e : covOf σ f = hex.choose f := by rw [covOf, dite_eq_left hex]
  rw [e]
  apply (funEquiv σ).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((isFunForm_iff_eq σ _ f).1 (hex.choose_spec f)).symm

theorem covOf_desc {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n)
    (f : VV ℂ fun τ => (σ τ).dual) (hf : ∀ m, AddMonoidAlgebra.coeff f.1 m ∈ Set.range φ) :
    ∃ F₀ : VV K σ, map φ F₀.1 = (covOf σ f).1 := by
  obtain ⟨f₀, hf₀⟩ := descend φ _ f hf
  refine ⟨(funEquiv σ).symm f₀, ?_⟩
  have h1 : IsFunForm σ ((funEquiv σ).symm f₀) f₀ := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm f₀)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := isFunForm_map φ σ h1
  have h4 : f = funEquiv σ ⟨map φ ((funEquiv σ).symm f₀).1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ ((funEquiv σ).symm f₀).2⟩ := by
    rw [← (isFunForm_iff_eq σ _ _).1 h2]
    exact Subtype.ext hf₀.symm
  rw [covOf_eq, h4, LinearEquiv.symm_apply_apply]

theorem brPair_mem_range {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (U : VV ℂ Λ) (V : VV ℂ fun τ => (σ τ).dual)
    (hU : ∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range φ) (hV : ∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range φ) :
    brPair σ hN Λ U V ∈ Set.range φ := by
  obtain ⟨U₀, hU₀⟩ := exists_map_eq φ U.1 hU
  obtain ⟨F₀, hF₀⟩ := covOf_desc φ σ V hV
  refine ⟨(extNormB K σ)⁻¹ * fockB (Br.brStdP hN Λ σ U₀ : Pol K ι n) F₀.1, ?_⟩
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, ← hF₀, Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, ← hU₀, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]

end General

end GlobalTheory.BrRat

namespace GlobalTheory.RowClaim

theorem brPair_mem_coefField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range D.what₂.embLL) → (∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ _ t Φ _ U V hU hV
  haveI : CharZero D.what₂.LL := (RingHom.charZero_iff D.what₂.embLL.injective).mpr inferInstance
  exact GlobalTheory.BrRat.brPair_mem_range D.what₂.embLL _ _ _ U V hU hV

end GlobalTheory.RowClaim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingPairing_mem_coefficientField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, AddMonoidAlgebra.coeff U.1 m ∈ Set.range D.what₂.embLL) → (∀ m, AddMonoidAlgebra.coeff V.1 m ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowClaim.brPair_mem_coefField | exact GlobalTheory.RowClaim.brPair_mem_coefField | (intros; apply GlobalTheory.RowClaim.brPair_mem_coefField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchOfPolMatch
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.PolMatchConst

def finProd {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ) :
    (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)

theorem match_of_polMatch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → Φ' ∈ G.M'.So B.ψ B.τ₁ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Match B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hT Φ Φ' hP hSo
  have hP0 := hP
  obtain ⟨T, hXT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', _⟩ := hP
  have hstd : ∀ (κ : Type) (ψ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) (vac : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ),
      (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      (∀ v ∉ T, ψ v = vac v) →
      ∀ᶠ v in Filter.cofinite, ψ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    intro κ ψ vac hvac hψ
    filter_upwards [hvac, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    rw [hψ v hvT, hv]
  have hg : ∀ i, finProd (φ i) ∈ GlobalTheory.WeilM.SB _ := fun i =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ i) (hf i).2.1 (hstd _ _ _ hT.geo.hM.std (hf i).2.2)⟩
  have hg' : ∀ j, finProd (φ' j) ∈ GlobalTheory.WeilM.SB _ := fun j =>
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2),
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (φ' j) (hf' j).2.1 (hstd _ _ _ hT.geo.hM'.std (hf' j).2.2)⟩
  have e : Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (finProd (φ i)) := hΦ
  have e' : Φ' = ∑ j, GlobalTheory.WeilM.pureA F (f' j) (finProd (φ' j)) := hΦ'
  refine ⟨hSo, m, m', fun i => finProd (φ i), f, fun _ => f, fun j => finProd (φ' j), f', fun _ => f',
    fun i => ⟨hg i, tendsto_const_nhds⟩, fun j => ⟨hg' j, tendsto_const_nhds⟩, e, e', fun _ => ?_⟩
  rw [← e, ← e']
  exact ⟨hSo, hP0⟩

end GlobalTheory.SquareAgree.PolMatchConst
end
end
