module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.Frob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

def evalMap {π : Representation ℂ (GL (Fin (a + b)) k) V} {σ : Representation ℂ (GL (Fin a) k) W}
    {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    V →ₗ[ℂ] TensorProduct ℂ W W' :=
  φ.toLinearMap ∘ₗ (twKer π (unipRad k (two (stdSum (rfl : a + b = a + b)))) 1).mkQ

theorem evalMap_law {π : Representation ℂ (GL (Fin (a + b)) k) V}
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ))
    (q : parab k (two (stdSum (rfl : a + b = a + b)))) (w : V) :
    evalMap φ (π q w) =
      (deltaHalf k (Two (Fin a) (Fin b)) (leviProj k _ q) : ℂ) •
        extTensor σ ρ ((leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q)) (evalMap φ w) := by
  set xy := (leviTwo k (Fin a) (Fin b)).symm (leviProj k _ q) with hxy
  have hL : leviProj k (two (stdSum (rfl : a + b = a + b))) q = leviTwo k _ _ xy :=
    (MulEquiv.apply_symm_apply _ _).symm
  obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip k (two (stdSum (rfl : a + b = a + b))) q
  rw [hL] at hpu ⊢
  have hpu' : (q : GL (Fin (a + b)) k) =
      leviEmb k (two (stdSum (rfl : a + b = a + b))) (leviTwo k _ _ xy) * u := hpu
  have hmk : (Submodule.Quotient.mk (π u w) :
      Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) = Submodule.Quotient.mk w := by
    rw [Submodule.Quotient.eq]
    refine Submodule.subset_span ⟨⟨u, hu⟩, w, ?_⟩
    simp
  have key : ∀ (M : Levi k (Two (Fin a) (Fin b))) (x : V),
      (Submodule.Quotient.mk (π (leviEmb k (two (stdSum (rfl : a + b = a + b))) M) x) :
        Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b))))) =
        (deltaHalf k (Two (Fin a) (Fin b)) M : ℂ) •
          GlobalTheory.SmGL.jac (two (stdSum (rfl : a + b = a + b))) π M (Submodule.Quotient.mk x) := by
    intro M x
    rw [jac_mk, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  have hint := Representation.IntertwiningMap.isIntertwining _ _ φ xy
    (Submodule.Quotient.mk w : Jacquet π (unipRad k (two (stdSum (rfl : a + b = a + b)))))
  simp only [evalMap, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [hpu', map_mul, Module.End.mul_apply, key, hmk, map_smul]
  change _ • φ (jac₂ (stdSum (rfl : a + b = a + b)) π xy (Submodule.Quotient.mk w)) = _
  rw [hint]
  rfl

def frobMap {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) :
    π.IntertwiningMap (prod₂ σ ρ) :=
  { toFun := fun v => ⟨⟨fun x => evalMap φ (π x v), fun q x => by
        show evalMap φ (π (q * x) v) = _
        rw [map_mul, Module.End.mul_apply]
        exact evalMap_law φ q (π x v)⟩,
      mem_smoothPart_of_nhds (Filter.mem_of_superset ((hs v).mem_nhds (by simp)) fun h hh => by
        have hh' : π h v = v := hh
        refine Subtype.ext (funext fun x => ?_)
        show evalMap φ (π (x * h) v) = evalMap φ (π x v)
        rw [map_mul, Module.End.mul_apply, hh'])⟩
    map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (v + w)) = evalMap φ (π x v) + evalMap φ (π x w)
      rw [map_add (f := _), map_add (f := _)]))
    map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (c • v)) = c • evalMap φ (π x v)
      rw [map_smul, map_smul]))
    isIntertwining' := fun h => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
      show evalMap φ (π x (π h v)) = evalMap φ (π (x * h) v)
      rw [map_mul, Module.End.mul_apply])) }

theorem frobMap_one {π : Representation ℂ (GL (Fin (a + b)) k) V} (hs : IsSmooth π)
    {σ : Representation ℂ (GL (Fin a) k) W} {ρ : Representation ℂ (GL (Fin b) k) W'}
    (φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ)) (v : V) :
    (frobMap hs φ v).1.1 1 = φ (Submodule.Quotient.mk v) := by
  show evalMap φ (π 1 v) = _
  rw [map_one]
  rfl

theorem exists_injective_of_jac₂ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (V W W' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (σ : Representation ℂ (GL (Fin a) k) W)
    (ρ : Representation ℂ (GL (Fin b) k) W'), IsSmooth π → π.IsIrreducible →
    ∀ φ : (jac₂ (stdSum (rfl : a + b = a + b)) π).IntertwiningMap (extTensor σ ρ), φ ≠ 0 →
      ∃ ψ : π.IntertwiningMap (prod₂ σ ρ), Function.Injective ψ := by
  intro k _ _ _ _ a b V W W' _ _ _ _ _ _ π σ ρ hs hπ φ hφ
  refine ⟨frobMap hs φ, ?_⟩
  haveI := hπ
  refine (Representation.IsIrreducible.injective_or_eq_zero (frobMap hs φ)).resolve_right fun h0 => hφ ?_
  ext v
  show φ (Submodule.Quotient.mk v) = 0
  rw [← frobMap_one hs φ v, h0]
  rfl

end GlobalTheory.CompanionTheory.Frob
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegativeSchwartzBump
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegativeSchwartzBump
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicBump

open NumberField IsDedekindDomain Topology
open scoped Classical

theorem exists_compact_open_nhds (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {w₀ : κ → FiniteAdeleRing (𝓞 F) F} {B : Set (κ → FiniteAdeleRing (𝓞 F) F)} (hB : B ∈ 𝓝 w₀) :
    ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsOpen C ∧ IsCompact C ∧ IsClosed C ∧ w₀ ∈ C ∧ C ⊆ B := by
  rw [nhds_pi, Filter.mem_pi] at hB
  obtain ⟨I, -, t, ht, hsub⟩ := hB
  have hO : (⋂ i, (fun a => w₀ i + a) ⁻¹' t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) :=
    Filter.iInter_mem.mpr fun i =>
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using ht i)
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  have hNF : ((N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, mul_inv_cancel₀ hNF, map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : FiniteAdeleRing (𝓞 F) F ≃ₜ FiniteAdeleRing (𝓞 F) F :=
    { toFun := fun u => c * u
      invFun := fun u => (N : FiniteAdeleRing (𝓞 F) F) * u
      left_inv := fun u => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u) = u
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u) = u
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  let D : κ → Set (FiniteAdeleRing (𝓞 F) F) := fun i =>
    (Homeomorph.subRight (w₀ i)) ⁻¹' (h ⁻¹' (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)))
  have hDc : ∀ i, IsCompact (D i) := fun i =>
    (Homeomorph.subRight (w₀ i)).isCompact_preimage.2 (h.isCompact_preimage.2 hint_c)
  have hDo : ∀ i, IsOpen (D i) := fun i =>
    (hint_o.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  have hint_l : IsClosed (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
    (Formalism.UG.intAd F).toAddSubgroup.isClosed_of_isOpen hint_o
  have hDl : ∀ i, IsClosed (D i) := fun i =>
    (hint_l.preimage h.continuous).preimage (Homeomorph.subRight (w₀ i)).continuous
  refine ⟨Set.univ.pi D, isOpen_set_pi Set.finite_univ fun i _ => hDo i, isCompact_univ_pi hDc,
    isClosed_set_pi fun i _ => hDl i, fun i _ => ?_, fun u hu => hsub fun i _ => ?_⟩
  · show c * (w₀ i - w₀ i) ∈ (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F))
    rw [sub_self, mul_zero]
    exact zero_mem (Formalism.UG.intAd F)
  · have hi : c * (u i - w₀ i) ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have h1 := Set.mem_iInter.mp (hNO _ hi) i
    rw [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at h1
    simpa using h1

theorem exists_bump : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : Set (κ → AF F)), IsOpen N → ∀ z₀ ∈ N, ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N → Φ z = 0) ∧ 0 < (Φ z₀).re := by
  intro F _ _ κ _ N hN z₀ hz₀
  let P : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have hP : Continuous P := continuous_pi fun i =>
    Continuous.prodMk ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst))
      ((continuous_apply i).comp continuous_snd)
  let y₀ : κ → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1
  let w₀ : κ → FiniteAdeleRing (𝓞 F) F := fun i => (z₀ i).2
  have hPz : ∀ z : κ → AdeleRing (𝓞 F) F,
      P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) = z := fun z =>
    funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  have hmem : P ⁻¹' N ∈ 𝓝 (y₀, w₀) :=
    (hN.preimage hP).mem_nhds (by show P (y₀, w₀) ∈ N; rw [hPz z₀]; exact hz₀)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨φ, hφs, hφc, hφd, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (E := κ → mixedEmbedding.mixedSpace F) (n := ⊤) hA
  obtain ⟨C, hCo, hCc, hCcl, hwC, hCB⟩ := exists_compact_open_nhds F hB
  have hc : HasCompactSupport fun y => ((φ y : ℝ) : ℂ) :=
    hφc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    hc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hφd)
  have hf : ∀ y, f y = ((φ y : ℝ) : ℂ) := fun y => rfl
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := Set.indicator C fun _ => 1
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, HasCompactSupport.intro hCc fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ C
    · exact ⟨C, hCo, hx, fun x' hx' => by simp only [g, Set.indicator_of_mem hx, Set.indicator_of_mem hx']⟩
    · exact ⟨Cᶜ, hCcl.isOpen_compl, hx, fun x' hx' => by
        simp only [g, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']⟩
  have hval : ∀ z, GlobalTheory.WeilM.pureA F f g z = ((φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) : ℝ) : ℂ) *
      g (fun i => (z i).2) := fun z => rfl
  have hgval : ∀ w, g w = ((Set.indicator C (fun _ => (1 : ℝ)) w : ℝ) : ℂ) := fun w => by
    by_cases hw : w ∈ C <;> simp [g, hw]
  have hnn : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  refine ⟨GlobalTheory.WeilM.pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, fun z => ?_, fun z hz => ?_, ?_⟩
  · rw [hval, hgval, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨mul_nonneg (hnn _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _), rfl⟩
  · rw [hval]
    by_contra hne
    have h1 := left_ne_zero_of_mul hne
    have h2 := right_ne_zero_of_mul hne
    have h1' : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) ≠ 0 := fun h => h1 (by rw [h]; simp)
    have h2' : (fun i => (z i).2) ∈ C := by
      by_contra h
      exact h2 (Set.indicator_of_notMem h _)
    have h3 := hAB (Set.mk_mem_prod (hφs (subset_tsupport _ h1')) (hCB h2'))
    apply hz
    have h4 : P (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2) ∈ N := h3
    rwa [hPz z] at h4
  · rw [hval]
    have e1 : g (fun i => (z₀ i).2) = 1 := Set.indicator_of_mem (show w₀ ∈ C from hwC) _
    have e2 : φ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z₀ i).1) = 1 := hφ1
    rw [e1, e2]
    simp

end GlobalTheory.CompanionTheory.AdelicBump

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNonnegativeSchwartzBumpStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonnegative_schwartz_bump : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : Set (κ → AF F)), IsOpen N → ∀ z₀ ∈ N, ∃ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N → Φ z = 0) ∧ 0 < (Φ z₀).re := by
  first | exact @GlobalTheory.CompanionTheory.AdelicBump.exists_bump | exact GlobalTheory.CompanionTheory.AdelicBump.exists_bump | (intros; apply GlobalTheory.CompanionTheory.AdelicBump.exists_bump <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensor
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProductTheta

variable {D : D7} {r s p : ℕ}

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.castAdd s i))

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.natAdd r i))

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [rowT, rowB, rowJ]

theorem continuous_rowJ :
    Continuous fun z : Mx D r p × Mx D s p => rowJ z.1 z.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply a).comp continuous_fst)
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply b).comp continuous_snd)

def rowHomeo : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := by simp [rowT_rowJ, rowB_rowJ]
  right_inv y := rowJ_rowT_rowB y
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem rowT_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowT (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowT y) a : Mx D r p) := rfl

theorem rowB_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowB (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowB y) a : Mx D s p) := rfl

theorem pr_split {b : HermE D (r + s)} {br : HermE D r} {bs : HermE D s} (h : IsBlockSL2Embedding b br bs)
    (x y : Mx D (r + s) p) :
    pr b x y = pr br (rowT x) (rowT y) + pr bs (rowB x) (rowB y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext i j
  simp only [pr, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Fin.sum_univ_add, h1, h2, h3, h4,
    map_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rfl

theorem halfTr_add (u v : AE D) : halfTr (u + v) = halfTr u + halfTr v := by
  simp only [halfTr, trA, map_add (f := _), mul_add]

theorem npow_half_mul (x : ℝ≥0) (hx : x ≠ 0) :
    npow x ((r : ℂ) / 2) * npow x ((s : ℂ) / 2) = npow x (((r + s : ℕ) : ℂ) / 2) := by
  have hx' : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  simp only [npow]
  rw [← Complex.cpow_add _ _ hx']
  congr 1
  push_cast
  ring

theorem absA_ne_zero (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h
  have := map_mul (absA D) u u⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

theorem prodTh_of_schwTensor : SchwTensor → ProdTh := by
  intro hT D r s p μr 𝓕r μs 𝓕s hμr hμs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hr hs
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  refine ⟨fun h => hT D θ hθ r s p _ (hr.mem h) _ (hs.mem h), ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowT u.2) : G D p × Mx D r p) :=
      continuous_fst.prodMk (continuous_rowT.comp continuous_snd)
    have c2 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowB u.2) : G D p × Mx D s p) :=
      continuous_fst.prodMk (continuous_rowB.comp continuous_snd)
    exact (hr.cont.comp c1).mul (hs.cont.comp c2)
  · intro C hC
    obtain ⟨Mr, hMr, h1⟩ := hr.maj C hC
    obtain ⟨Ms, hMs, h2⟩ := hs.maj C hC
    refine ⟨_, hT D θ hθ r s p _ hMr _ hMs, fun h hh y => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (h1 h hh _) (h2 h hh _) (norm_nonneg _) (norm_nonneg _)
  · intro g a hg h y
    have e := npow_half_mul (r := r) (s := s) (absA D (Matrix.GeneralLinearGroup.det a)) (absA_ne_zero _)
    rw [hr.levi g a hg h, hs.levi g a hg h, rowT_mul, rowB_mul, ← e]
    simp only [MonoidHom.mul_apply, Circle.coe_mul]
    ring
  · intro g c hg h y
    rw [hr.unip g c hg h, hs.unip g c hg h, pr_split hb, mul_add, Matrix.trace_add, halfTr_add,
      AddChar.map_add_eq_mul]
    ring
  · intro g hg h x
    haveI := hμr.1
    haveI := hμs.1
    haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
    haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
    have hemb : MeasurableEmbedding (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) :=
      (rowHomeo (D := D) (r := r) (s := s) (p := p)).measurableEmbedding
    rw [hemb.integral_map, hr.weyl g hg h, hs.weyl g hg h, ← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [rowT_rowJ, rowB_rowJ, pr_split hb, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]
    ring

end GlobalTheory.CompanionTheory.ThTot.ProductTheta

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensorStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_theta_of_schwartz_tensor : SchwTensor → ProdTh := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | exact GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedFormula
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree.FibMass

theorem sig_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

theorem gram_mem {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
    [Algebra F R] (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a c
  have hi : ∀ y : E, sigR R σ (inclR R y) = inclR R (σ y) := fun y => by simp [sigR, inclR]
  change sigR R σ (hR R σ J (X c) (X a)) = hR R σ J (X a) (X c)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R σ hs, hi, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.AvgFree.FibMass

theorem GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ Tt : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact Tt → IsOpen Tt → Tt ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} → (∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (Tt ∩ gramIn (Fv F v) σ J Y) = ∫⁻ y in Y, mv y Tt ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)) ∧ Continuous (fun y => (mv y Tt).toReal) ∧ (∀ y, mv y Tt ≠ ⊤) ∧ ∃ C : ℝ≥0, ∀ y, mv y Tt ≤ C := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv Tt hTc hTo hTf
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI hBH : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := hmv
  have hinv : ∀ e, σ (σ e) = e := GlobalTheory.CompanionTheory.AvgFree.FibMass.sig_inv hσ
  have hgc : Continuous (gramR (Fv F v) σ J : (Fin n → Fin M → Fv F v ⊗[F] E) → _) := a10 n M J

  let q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n := fun X =>
    ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.AvgFree.FibMass.gram_mem (Fv F v) hinv hJ.1 X⟩
  have hqc : Continuous q := hgc.subtype_mk _
  have hTm : MeasurableSet Tt := hTo.measurableSet

  have hae : ∀ y, ∀ᵐ x ∂(mv y), q x = y := fun y => by
    refine measure_mono_null ?_ (h1 y)
    intro x hx hx'
    exact hx (Subtype.ext hx'.1)

  let φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ := Tt.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hTo.frontier_eq, hTc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hTc fun x hx => Set.indicator_of_notMem hx _
  have hφt : tsupport φ ⊆ {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
    refine subset_trans (closure_minimal ?_ hTc.isClosed) hTf
    intro x hx
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h3 φ hφc hφs hφt
  have hint : ∀ y, ∫ X, φ X ∂(mv y) = (mv y Tt).toReal := fun y => by
    simp [φ, integral_indicator hTm, Measure.real]
  have hfin : ∀ y, mv y Tt ≠ ⊤ := fun y => by
    have h := hI y (Set.mem_univ y)
    rw [integrable_indicator_iff hTm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : Continuous fun y => (mv y Tt).toReal := by
    have h := continuousOn_univ.1 hC
    simpa only [hint] using h
  refine ⟨fun Y hY => ?_, hcont, hfin, ?_⟩
  · have hG : gramIn (Fv F v) σ J Y = q ⁻¹' Y := by
      ext X
      constructor
      · rintro ⟨y, hy, e⟩
        have : q X = y := Subtype.ext e
        show q X ∈ Y
        rwa [this]
      · intro hX
        exact ⟨q X, hX, rfl⟩
    rw [hG]
    have hqY : MeasurableSet (q ⁻¹' Y) := hqc.measurable hY
    have hT : MeasurableSet (Tt ∩ q ⁻¹' Y) := hTm.inter hqY
    have e := h2 ((Tt ∩ q ⁻¹' Y).indicator 1) (measurable_one.indicator hT)
    rw [lintegral_indicator_one hT, Measure.restrict_apply hT,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hTf)] at e
    rw [e, ← lintegral_indicator hY]
    refine lintegral_congr fun y => ?_
    rw [lintegral_indicator_one hT]
    by_cases hy : y ∈ Y
    · rw [Set.indicator_of_mem hy]
      refine measure_congr ?_
      filter_upwards [hae y] with x hx
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      show q x ∈ Y
      rwa [hx]
    · rw [Set.indicator_of_notMem hy]
      refine measure_mono_null (t := {x | ¬ q x = y}) ?_ (hae y)
      intro x hx hxy
      apply hy
      rw [← hxy]
      exact hx.2
  · obtain ⟨C, hC'⟩ := (hTc.image hqc).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨Real.toNNReal C, fun y => ?_⟩
    by_cases hy : y ∈ q '' Tt
    · have h := hC' y hy
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at h
      show mv y Tt ≤ ENNReal.ofReal C
      exact (ENNReal.le_ofReal_iff_toReal_le (hfin y) (ENNReal.toReal_nonneg.trans h)).2 h
    · have h0 : mv y Tt = 0 := by
        refine measure_mono_null ?_ (h1 y)
        intro x hx hx'
        exact hy ⟨x, hx, Subtype.ext hx'.1⟩
      rw [h0]
      exact bot_le
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedFormulaStatement
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fibre_measure_unramified_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ Tt : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact Tt → IsOpen Tt → Tt ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} → (∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (Tt ∩ gramIn (Fv F v) σ J Y) = ∫⁻ y in Y, mv y Tt ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)) ∧ Continuous (fun y => (mv y Tt).toReal) ∧ (∀ y, mv y Tt ≠ ⊤) ∧ ∃ C : ℝ≥0, ∀ y, mv y Tt ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses | exact GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses | (intros; apply GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatement
noncomputable section

open MeasureTheory Measure Set
open scoped Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.CompanionTheory.ThTot

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProdMeasPf

section Abstract

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem isAddFundamentalDomain_join (J : X × Y ≃ᵐ Z) (hJ : ∀ a b, J (a + b) = J a + J b)
    (Γ : AddSubgroup X) (Δ : AddSubgroup Y) (Λ : AddSubgroup Z)
    (hΛ : ∀ z, z ∈ Λ ↔ (J.symm z).1 ∈ Γ ∧ (J.symm z).2 ∈ Δ)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (F : Set X) (G : Set Y)
    (hF : IsAddFundamentalDomain Γ F μ) (hG : IsAddFundamentalDomain Δ G ν) :
    IsAddFundamentalDomain Λ (J '' (F ×ˢ G)) ((μ.prod ν).map J) := by
  have hm : ∀ R : Set (X × Y), (μ.prod ν).map J (J '' R) = μ.prod ν R := fun R => by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective]
  have htr : ∀ (l : Z) (w : X × Y), l + J w = J (J.symm l + w) := fun l w => by
    rw [hJ, J.apply_symm_apply]
  have himg : ∀ l : Λ, (l +ᵥ (J '' (F ×ˢ G)) : Set Z) =
      J '' ((((⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) +ᵥ F : Set X)) ×ˢ
        (((⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) +ᵥ G : Set Y))) := by
    intro l
    ext z
    constructor
    · rintro ⟨_, ⟨w, ⟨h1, h2⟩, rfl⟩, rfl⟩
      refine ⟨J.symm l.1 + w, ⟨⟨w.1, h1, rfl⟩, ⟨w.2, h2, rfl⟩⟩, ?_⟩
      exact (htr l.1 w).symm
    · rintro ⟨w, ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩, rfl⟩
      refine ⟨J (a, b), ⟨(a, b), ⟨ha, hb⟩, rfl⟩, ?_⟩
      have : J.symm l.1 + (a, b) = w := Prod.ext h1 h2
      change l.1 + J (a, b) = J w
      rw [htr, this]
  refine ⟨?_, ?_, ?_⟩
  · have hq : QuasiMeasurePreserving J.symm ((μ.prod ν).map J) (μ.prod ν) := by
      refine ⟨J.symm.measurable.aemeasurable, ?_⟩
      rw [Measure.map_map J.symm.measurable J.measurable]
      simp only [MeasurableEquiv.symm_comp_self, Measure.map_id]
      exact Measure.AbsolutelyContinuous.rfl
    rw [J.image_eq_preimage_symm]
    exact (hF.nullMeasurableSet.prod hG.nullMeasurableSet).preimage hq
  · rw [J.measurableEmbedding.ae_map_iff]
    have h1 := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hF.ae_covers
    have h2 := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hG.ae_covers
    filter_upwards [h1, h2] with w hw1 hw2
    obtain ⟨g, hg⟩ := hw1
    obtain ⟨d, hd⟩ := hw2
    refine ⟨⟨J (g.1, d.1), (hΛ _).2 (by simp)⟩, (g.1 + w.1, d.1 + w.2), ⟨hg, hd⟩, ?_⟩
    change J (g.1 + w.1, d.1 + w.2) = J (g.1, d.1) + J w
    rw [← hJ]
    rfl
  · intro l l' hll
    change (μ.prod ν).map J ((l +ᵥ (J '' (F ×ˢ G)) : Set Z) ∩ (l' +ᵥ (J '' (F ×ˢ G)) : Set Z)) = 0
    rw [himg, himg, ← Set.image_inter J.injective, hm, Set.prod_inter_prod, Measure.prod_prod]
    have hne : (⟨(J.symm l.1).1, ((hΛ _).1 l.2).1⟩ : Γ) ≠ ⟨(J.symm l'.1).1, ((hΛ _).1 l'.2).1⟩ ∨
        (⟨(J.symm l.1).2, ((hΛ _).1 l.2).2⟩ : Δ) ≠ ⟨(J.symm l'.1).2, ((hΛ _).1 l'.2).2⟩ := by
      by_contra hcon
      push_neg at hcon
      apply hll
      apply Subtype.ext
      apply J.symm.injective
      exact Prod.ext (congrArg Subtype.val hcon.1) (congrArg Subtype.val hcon.2)
    rcases hne with h | h
    · have := hF.aedisjoint h
      rw [show μ _ = 0 from this, zero_mul]
    · have := hG.aedisjoint h
      rw [show ν _ = 0 from this, mul_zero]

end Abstract

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j; simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j; simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem rowJ_add (x x' : Mx D r p) (z z' : Mx D s p) : rowJ (x + x') (z + z') = rowJ x z + rowJ x' z' := by
  funext i j
  induction i using Fin.addCases with
  | left a => simp [rowJ]
  | right b => simp [rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simpa [rowJ] using (continuous_fst.matrix_elem a j)
  | right b =>
    simpa [rowJ] using (continuous_snd.matrix_elem b j)

def rowH : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := Prod.ext (rowT_rowJ _ _) (rowB_rowJ _ _)
  right_inv := rowJ_rowT_rowB
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem mem_ratMx_iff (y : Mx D (r + s) p) :
    y ∈ ratMx D (r + s) p ↔ rowT y ∈ ratMx D r p ∧ rowB y ∈ ratMx D s p := by
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨⟨fun i j => γ (Fin.castAdd s i) j, rfl⟩, ⟨fun i j => γ (Fin.natAdd r i) j, rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    replace ha : rat a = rowT y := ha
    replace hb : rat b = rowB y := hb
    refine ⟨fun i j => Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) i, ?_⟩
    change rat _ = y
    funext i j
    induction i using Fin.addCases with
    | left u =>
      refine Eq.trans ?_ (congrFun (congrFun ha u) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.castAdd s u)) =
        incA D (a u j)
      rw [Fin.addCases_left]
    | right v =>
      refine Eq.trans ?_ (congrFun (congrFun hb v) j)
      change incA D (Fin.addCases (motive := fun _ => D.host.E) (fun u => a u j) (fun v => b v j) (Fin.natAdd r v)) =
        incA D (b v j)
      rw [Fin.addCases_right]

theorem prodMeas : ProdMeas := by
  intro D r s p μr 𝓕r μs 𝓕s μ 𝓕 hr hs h
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D r p
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D s p
  obtain ⟨c1, c2, c3, c4, -⟩ := lattice_Mx D (r + s) p
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  let J : Mx D r p × Mx D s p ≃ᵐ Mx D (r + s) p := (rowH (D := D) (r := r) (s := s) (p := p)).toMeasurableEquiv
  have hJ : ∀ a b, J (a + b) = J a + J b := fun a b => rowJ_add a.1 b.1 a.2 b.2
  have hJf : (J : Mx D r p × Mx D s p → Mx D (r + s) p) = fun z => rowJ z.1 z.2 := rfl
  let e : Mx D r p × Mx D s p ≃+ Mx D (r + s) p :=
    { (rowH (D := D) (r := r) (s := s) (p := p)).toEquiv with map_add' := hJ }
  have hH : ((μr.prod μs).map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map (μr.prod μs) e continuous_rowJ (continuous_rowT.prodMk continuous_rowB)
  have hF : IsAddFundamentalDomain (ratMx D (r + s) p) (J '' (𝓕r ×ˢ 𝓕s)) ((μr.prod μs).map J) :=
    isAddFundamentalDomain_join J hJ (ratMx D r p) (ratMx D s p) (ratMx D (r + s) p)
      (fun z => mem_ratMx_iff z) μr μs 𝓕r 𝓕s hr.2.1 hs.2.1
  have h1 : (μr.prod μs).map J (J '' (𝓕r ×ˢ 𝓕s)) = 1 := by
    rw [J.map_apply, Set.preimage_image_eq _ J.injective, Measure.prod_prod, hr.2.2, hs.2.2, one_mul]
  have hcov : IsCovolOne (ratMx D (r + s) p) ((μr.prod μs).map J) (J '' (𝓕r ×ˢ 𝓕s)) := ⟨hH, hF, h1⟩
  exact covolOne_measure_eq hcov h

end GlobalTheory.CompanionTheory.ThTot.ProdMeasPf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatementStatement
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_measure_statement : ProdMeas := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | exact GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenUnitSubgroupKer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenUnitSubgroupKer
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.HeckeSmooth

theorem exists_open_unit_subgroup_ker : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (w : HeightOneSpectrum (𝓞 E)),
    ∃ U : Subgroup (w.adicCompletion E)ˣ, IsOpen (U : Set (w.adicCompletion E)ˣ) ∧
      (∀ x ∈ U, IsUnitAt w x) ∧ ∀ x ∈ U, χ.1 (localIdele E w x) = 1 := by
  intro E _ _ χ w
  have hker : IsOpen ((χ.loc w).ker : Set (w.adicCompletion E)ˣ) := GlobalTheory.HeckeComp.smooth_loc χ w
  let V : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {x | Valued.v (x : w.adicCompletion E) = 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, one_mul]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hV : IsOpen (V : Set (w.adicCompletion E)ˣ) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx1 : Valued.v (x : w.adicCompletion E) = 1 := hx
    have hx0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by rw [hx1]; exact one_ne_zero
    have h2 : (fun y : (w.adicCompletion E)ˣ => (y : w.adicCompletion E)) ⁻¹'
        {y | Valued.v y = Valued.v (x : w.adicCompletion E)} ∈ nhds x :=
      Units.continuous_val.continuousAt (Valued.locally_const hx0)
    refine Filter.mem_of_superset h2 ?_
    intro y hy
    have hy' : Valued.v (y : w.adicCompletion E) = Valued.v (x : w.adicCompletion E) := hy
    show Valued.v (y : w.adicCompletion E) = 1
    rw [hy', hx1]
  refine ⟨(χ.loc w).ker ⊓ V, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    exact hker.inter hV
  · intro x hx
    exact (Subgroup.mem_inf.mp hx).2
  · intro x hx
    exact MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hx).1

end GlobalTheory.CompanionTheory.HeckeSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenUnitSubgroupKerStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_heckeChar_eq_one : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)),
    ∃ U : Subgroup (w.adicCompletion E)ˣ, IsOpen (U : Set (w.adicCompletion E)ˣ) ∧ (∀ x ∈ U, IsUnitAt w x) ∧
      ∀ x ∈ U, χ.1 (localIdele E w x) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker | exact GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker | (intros; apply GlobalTheory.CompanionTheory.HeckeSmooth.exists_open_unit_subgroup_ker <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisjointTranslatesVolumeBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisjointTranslatesVolumeBound
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Count

theorem card_mul_measure_le_of_disjoint_translates :
    ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G)
    [μ.IsAddLeftInvariant] (L : AddSubgroup G) (S : Set G), MeasurableSet S → S ⊆ L →
    ∀ (ι : Type) [Fintype ι] (f : ι → G), (∀ i, f i ∈ L) →
    (∀ i j u v, u ∈ S → v ∈ S → f i + u = f j + v → i = j) →
    (Fintype.card ι : ℝ≥0∞) * μ S ≤ μ (L : Set G) := by
  intro G _ _ _ μ _ L S hS hSL ι _ f hf hdis
  let T : ι → Set G := fun i => (fun x => -f i + x) ⁻¹' S
  have hT : ∀ i, MeasurableSet (T i) := fun i => (measurable_const_add (-f i)) hS
  have hμ : ∀ i, μ (T i) = μ S := fun i => measure_preimage_add μ (-f i) S
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) T := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr ?_
    intro x hi hj
    refine hij (hdis i j (-f i + x) (-f j + x) hi hj ?_)
    simp
  have hsub : (⋃ i ∈ (Finset.univ : Finset ι), T i) ⊆ (L : Set G) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, _, hi⟩ := hx
    have h1 : -f i + x ∈ L := hSL hi
    have h2 : f i + (-f i + x) ∈ L := L.add_mem (hf i) h1
    simpa using h2
  calc (Fintype.card ι : ℝ≥0∞) * μ S = ∑ i ∈ (Finset.univ : Finset ι), μ (T i) := by
        simp [hμ, Finset.card_univ]
    _ = μ (⋃ i ∈ (Finset.univ : Finset ι), T i) :=
        (measure_biUnion_finset hd (fun i _ => hT i)).symm
    _ ≤ μ (L : Set G) := measure_mono hsub

end GlobalTheory.CompanionTheory.SiegelND.Integ.Count
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisjointTranslatesVolumeBoundStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disjoint_translates_volume_bound : ∀ (G : Type) [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : Measure G)
    [μ.IsAddLeftInvariant] (L : AddSubgroup G) (S : Set G), MeasurableSet S → S ⊆ L →
    ∀ (ι : Type) [Fintype ι] (f : ι → G), (∀ i, f i ∈ L) →
    (∀ i j u v, u ∈ S → v ∈ S → f i + u = f j + v → i = j) →
    (Fintype.card ι : ℝ≥0∞) * μ S ≤ μ (L : Set G) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Count.card_mul_measure_le_of_disjoint_translates | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Count.card_mul_measure_le_of_disjoint_translates | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Count.card_mul_measure_le_of_disjoint_translates <;> assumption)
end
end
