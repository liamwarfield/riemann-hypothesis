module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomFiniteVectorEqFiniteHeisenbergComb
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenCompactLevelThetaKernelBottomTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingVacuumTranslateSource
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingVacuumTranslateSource
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.VacTranslateLeft

theorem exists_open_fix_translate_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ U : Subgroup (GA D S), IsOpen (U : Set (GA D S)) ∧ ∀ κ ∈ U, κ ∈ GfC S →
      heisO ψ S T (actO S T κ 1 u) f₀ = heisO ψ S T u f₀ := by
  intro D ψ θ S T sS sT ΛS ΛT hS hT f₀ hvac u hu
  obtain ⟨M, hM, hMu⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO'
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) u hu
  have hN : 0 < 2 * (2 * 2) * M * M := by positivity
  have hev := GlobalTheory.LatNhds.eventually_move S T ΛS ΛT hS hT u hu (2 * (2 * 2) * M * M) hN
  have hc : Filter.Tendsto (fun κ : GA D S => (κ, (1 : GA D T))) (𝓝 1) (𝓝 1) := by
    have := (continuous_id.prodMk (continuous_const (y := (1 : GA D T)))).tendsto (1 : GA D S)
    simpa only [Prod.mk_one_one, id] using this
  have hev' := hc.eventually hev
  have key : ∃ n : ℕ, ∀ κ ∈ GfC S, GlobalTheory.Member.FinCong S n.factorial κ →
      ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T κ 1 u = u + (2 * (2 * 2) * M * M) • l := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := k) hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    obtain ⟨l, hl, e⟩ := hn
    exact hkne n l hl e
  obtain ⟨n, hn⟩ := key
  refine ⟨GlobalTheory.VacFixTarget.congGroup S n.factorial, GlobalTheory.VacFixTarget.isOpen_congGroup S n.factorial_pos,
    fun κ hκc hκ => ?_⟩
  obtain ⟨l, hl, e⟩ := hn κ hκ hκc
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have e2 : (2 * (2 * 2) * M * M) • l = 2 • ((2 * 2) • (M • (M • l))) := by
    simp only [smul_smul]
    congr 1
    ring
  have hu' : (2 * 2) • (M • (M • l)) ∈
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
    AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hl M) M) _
  have hs : ψ (symplOH S T u (2 • ((2 * 2) • (M • (M • l))))) = 1 := by
    rw [two_nsmul, GlobalTheory.SplitScalar.symplOH_add_right, GlobalTheory.SplitScalar.symplOH_add_self, ← GlobalTheory.Mem.CoefInv.symplO_nsmul,
      ← GlobalTheory.Mem.CoefInv.symplO_nsmul, smul_comm M (2 * 2) u]
    exact GlobalTheory.VacTranslate.psi_four_eq_one hvac.2.lat.1 hw₀ hMu (AddSubgroup.nsmul_mem _ hl M)
  have h := GlobalTheory.SplitScalar.heisO_heisO ψ S T u (2 • ((2 * 2) • (M • (M • l)))) f₀
  rw [hvac.2.lat.1 _ hu', hs, one_smul] at h
  rw [e, e2, h]

end GlobalTheory.VacTranslateLeft

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingVacuumTranslateSourceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_fixing_vacuum_translate_source : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f₀ : WO S T → ℂ,
    IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ →
    ∀ u : WO S T, u.map (infPart D) = 0 →
    ∃ U : Subgroup (GA D S), IsOpen (U : Set (GA D S)) ∧ ∀ κ ∈ U, κ ∈ GfC S →
      heisO ψ S T (actO S T κ 1 u) f₀ = heisO ψ S T u f₀ := by
  first | exact @GlobalTheory.VacTranslateLeft.exists_open_fix_translate_source | exact GlobalTheory.VacTranslateLeft.exists_open_fix_translate_source | (intros; apply GlobalTheory.VacTranslateLeft.exists_open_fix_translate_source <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomFiniteVectorEqFiniteHeisenbergCombStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_finiteVector_eq_finite_heisenbergComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO A' WW), (∀ k, (x k).map (infPart D) = 0) ∧
      X.f' t = ∑ k, c k • heisO W.ψ A' WW (x k) X.vac' := by
  first | exact @GlobalTheory.BottomFinComb.finVec_isFinComb | exact GlobalTheory.BottomFinComb.finVec_isFinComb | (intros; apply GlobalTheory.BottomFinComb.finVec_isFinComb <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenCompactLevelThetaKernelBottomTriple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotKerLevel

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem fixTranslate (hX : IsBottomTri W i j X) (t : T) (u : WO A' WW) (hu : u.map (infPart D) = 0) :
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' →
      X.ω' t (κ, 1) (heisO W.ψ A' WW u X.vac') = heisO W.ψ A' WW u X.vac' := by
  obtain ⟨U₁, hU₁, h₁⟩ := GlobalTheory.T.exists_open_subgroup_fixes_vacuum_definiteBottom hX t
  obtain ⟨U₂, hU₂, h₂⟩ := GlobalTheory.T.exists_open_fixing_vacuum_translate_source D W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.Λ X.rW.Λ hX.is.rigA'.1 hX.is.rigW.1 X.vac'
    hX.is.isVac' u hu
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  refine ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun κ hκ hf => ?_⟩
  rw [hW.om_heis κ 1 u X.vac' hX.is.isVac'.2.theta, h₁ κ hκ.1 hf, h₂ κ hκ.2 hf]

theorem exists_open_fix (hX : IsBottomTri W i j X) (t : T) :
    ∃ U : Subgroup (GA D A'), IsOpen (U : Set (GA D A')) ∧ ∀ κ ∈ U, κ ∈ GfC A' → X.ω' t (κ, 1) (X.f' t) = X.f' t := by
  obtain ⟨n, c, x, hx, e⟩ := GlobalTheory.T.definiteBottom_finiteVector_eq_finite_heisenbergComb hX t
  choose U hU hfix using fun k => fixTranslate hX t (x k) (hx k)
  refine ⟨⨅ k, U k, ?_, fun κ hκ hf => ?_⟩
  · have e2 : (((⨅ k, U k) : Subgroup (GA D A')) : Set (GA D A')) = ⋂ k, (U k : Set (GA D A')) := by
      ext y; simp [Subgroup.mem_iInf]
    rw [e2]
    exact isOpen_iInter_of_finite hU
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [e, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, hfix k κ (Subgroup.mem_iInf.1 hκ k) hf]

theorem continuous_finPart (V : HSp D) : Continuous (GlobalTheory.DefiniteClassAvg.finPart V) := by
  have e : GlobalTheory.DefiniteClassAvg.finPart V = fun y => (GlobalTheory.DefiniteClassAvg.realPart V y)⁻¹ * y := by
    funext y
    exact eq_inv_mul_of_mul_eq (GlobalTheory.DefiniteClassAvg.realPart_mul_finPart V y)
  rw [e]
  exact ((GlobalTheory.DefiniteClassAvg.continuous_realPart V).inv).mul continuous_id

theorem finPart_one (V : HSp D) : GlobalTheory.DefiniteClassAvg.finPart V 1 = 1 := by
  have h1 := GlobalTheory.DefiniteClassAvg.finPart_mul_realPart V 1
  have h2 : GlobalTheory.DefiniteClassAvg.finPart V 1 ∈ GinfC V ⊓ GfC V := by
    refine ⟨?_, GlobalTheory.DefiniteClassAvg.finPart_mem V 1⟩
    have : GlobalTheory.DefiniteClassAvg.finPart V 1 = (GlobalTheory.DefiniteClassAvg.realPart V 1)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (GinfC V).inv_mem (GlobalTheory.DefiniteClassAvg.realPart_mem V 1)
  rw [Formalism.IndefR.TopMult.inf_GinfC_GfC', Subgroup.mem_bot] at h2
  exact h2

theorem eq_of_finE_eq (V : HSp D) {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GfC V) (h : Lev.finE V a = Lev.finE V b) :
    a = b := by
  have h1 : finHom V a = finHom V b := by
    have inj : Function.Injective (Formalism.UG.bc (n := Fin V.rank) (Lev.swapAE D)) := by
      intro x y hxy
      apply Units.ext
      ext p q
      have := congrArg (fun z : GL (Fin V.rank) (Lev.EAf D) => z.1 p q) hxy
      simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at this
      exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective this
    exact inj h
  have h2 : a⁻¹ * b ∈ GinfC V ⊓ GfC V := by
    refine ⟨?_, (GfC V).mul_mem ((GfC V).inv_mem ha) hb⟩
    show finHom V (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  rw [Formalism.IndefR.TopMult.inf_GinfC_GfC', Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.1 h2)

theorem exists_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U, hUo, hfix⟩ := exists_open_fix hX t
  have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hX.is.weil' t
  have hθ : IsInfFam W.θ := hX.is.isVac'.2.inf
  have hf' : IsThetaFunO W.ψ A' WW (X.f' t) := (GlobalTheory.ConstRatio.theta_f hX.is t).2
  let K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)) := St X.rA'.β ⊓ (U ⊓ GfC A').map (Lev.finE A')
  have hKo : IsOpen ((K.comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    have hU1 : GlobalTheory.DefiniteClassAvg.finPart A' ⁻¹' (U : Set (GA D A')) ∈ nhds (1 : GA D A') :=
      (continuous_finPart A').continuousAt.preimage_mem_nhds (by rw [finPart_one]; exact hUo.mem_nhds U.one_mem)
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A' X.rA'.β ∅, hU1] with κ h1 h2
    exact ⟨h1.2.1, ⟨GlobalTheory.DefiniteClassAvg.finPart A' κ, ⟨h2, GlobalTheory.DefiniteClassAvg.finPart_mem A' κ⟩,
      GlobalTheory.DefiniteClassAvg.finE_finPart A' κ⟩⟩
  have hKc : IsCompact ((Lev.levA A' K : Subgroup (GA D A')) : Set (GA D A')) := by
    obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A' X.rA'.β
    refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC A').inter
      (Subgroup.isClosed_of_isOpen _ hKo)) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact hCm k hk1 hk2.1
  refine ⟨K, ⟨hKo, hKc⟩, fun P h k hk g => ?_⟩
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  obtain ⟨u, ⟨huU, huf⟩, hue⟩ := hk2.2
  have hku : k = u := (eq_of_finE_eq A' huf hk1 hue).symm
  have hk3 : X.ω' t (k, 1) (X.f' t) = X.f' t := hku ▸ hfix u huU huf
  show X.ω' t (g * k, h) _ 0 = X.ω' t (g, h) _ 0
  have e : ((g * k, h) : GA D A' × GA D WW) = (g, h) * (k, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ _ hW W.θ hθ k hk1 1 (GfC WW).one_mem
    _ _ _ _ _ P hf', hk3]

end GlobalTheory.BotKerLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenCompactLevelThetaKernelBottomTripleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompactLevel_thetaKernel_bottomTriple : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  first | exact @GlobalTheory.BotKerLevel.exists_level | exact GlobalTheory.BotKerLevel.exists_level | (intros; apply GlobalTheory.BotKerLevel.exists_level <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder

open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal

namespace GlobalTheory.RowTest.BottomClassSum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem weil' (hX : IsBottomTri W i j X) (t : T) :
    IsWeilDatumO W.ψ A' WW (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))
      ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.ω' t) :=
  hX.is.weil' t

theorem theta' (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) :
    IsThetaFunO W.ψ A' WW (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO hX.is.isVac'.1 hX.is.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
    (GlobalTheory.ConstRatio.theta_f hX.is t).2 P

theorem ker'_left (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) :
    ∀ γ ∈ GQ A', ∀ g, X.ker' W.ψ W.θ t P h (γ * g) = X.ker' W.ψ W.θ t P h g := by
  intro γ hγ g
  have hW := weil' hX t
  have hF := theta' hX t P
  show X.ω' t (γ * g, h) _ 0 = X.ω' t (g, h) _ 0
  have e : ((γ * g, h) : GA D A' × GA D WW) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hF)

theorem ker'_cont (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW) (x : GA D A') :
    Continuous fun k : GinfC A' => X.ker' W.ψ W.θ t P h (x * k) := by
  have hW := weil' hX t
  have hF := theta' hX t P
  exact (hW.om_cont _ hF 0).comp ((continuous_const.mul continuous_subtype_val).prodMk continuous_const)

theorem level_all [Finite T] (t₀ : T) (hX : IsBottomTri W i j X) :
    ∃ K : Subgroup (GL (Fin A'.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A' K ∧
      ∀ (t : T) (P : PolF D WW.rank A'.rank) (h : GA D WW), ∀ k ∈ Lev.levA A' K, ∀ g,
        X.ker' W.ψ W.θ t P h (g * k) = X.ker' W.ψ W.θ t P h g := by
  choose K hK hinv using GlobalTheory.T.exists_openCompactLevel_thetaKernel_bottomTriple hX
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A'
  have hG := hT.2.2.2.2.1
  refine ⟨⨅ t, K t, ⟨?_, ?_⟩, fun t P h k hk g => hinv t P h k ?_ g⟩
  · have e : (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) =
        ⋂ t, (((K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
      ext x; simp [Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hK t).1
  · have hcl : IsClosed ((((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A'))) := by
      have e : (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) =
          ⋂ t, (((K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
        ext x; simp [Subgroup.mem_iInf]
      rw [e]
      exact isClosed_iInter fun t => Subgroup.isClosed_of_isOpen _ (hK t).1
    have e2 : ((Lev.levA A' (⨅ t, K t) : Subgroup (GA D A')) : Set (GA D A')) =
        (Lev.levA A' (K t₀) : Set (GA D A')) ∩ (((⨅ t, K t).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Lev.mem_levA, Subgroup.mem_comap]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, (Subgroup.mem_iInf.1 h2) t₀⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [e2]
    exact (hK t₀).2.inter_right hcl
  · obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨hk1, (Subgroup.mem_iInf.1 hk2) t⟩

end GlobalTheory.RowTest.BottomClassSum
