module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianPairingOntoInverseIdealAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeForward
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalRelation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLev

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

def relax (J : QJ a t) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  (J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (GlobalTheory.PenBridge.plF J)) ⊓ GfC _ ⊓
    (Subgroup.pi Set.univ fun i =>
      KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0)).comap (GlobalTheory.PenBridge.rd J j hj)

def U0 (a : GeoAll W u) (j : ℕ) (hj : j + 1 = B.R.m) : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :=
  if h : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) then
    relax h.choose_spec.choose j hj h.choose_spec.choose_spec.2.some
  else ⊥

end GlobalTheory.PenLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilSchrodingerRealParameter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValueZeroParabolic
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelLaw

theorem value_zero_parabolic : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n), ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g : G D n, (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  intro D n V ψ χ θ μ ω hω Φ p hp a ha g
  obtain ⟨m, v, b, e, hm, hv⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (p * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D V.rank n) * a.1 : Mx D V.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have hs : s0 V n + (n : ℂ) / 2 = (V.rank : ℂ) / 2 := by rw [s0]; ring
  rw [e', hω.levi m _ hm, z1, hω.unip v b hv, z2, hs]
  simp [halfTr]

end GlobalTheory.StdUnn.SiegelLaw
end

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelSection

theorem fock_mem_degenerate : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 → ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → IsSection χ (s0 V n) (fun g : G D n => (ω g Φ).1 0) := by
  intro D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
  refine ⟨?_, ?_, ?_⟩
  · intro p hp a ha g
    exact GlobalTheory.StdUnn.SiegelLaw.value_zero_parabolic D n V ψ χ θ μ ω hω Φ p hp a ha g
  · exact GlobalTheory.T.continuous_weilSchrodinger_standardUnn_eval_zero D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω Φ
  · have hfin := GlobalTheory.T.fockVector_schrodingerModel_isKFinite D n V ψ hψ χ hχ hres θ hθ μ 𝓕 hμ ω hω l hl s hs Φ hΦ
    let L : schwartzA θ V.rank n →ₗ[ℂ] (G D n → ℂ) :=
      { toFun := fun Ψ g => (ω g Ψ).1 0
        map_add' := fun Ψ₁ Ψ₂ => by funext g; simp
        map_smul' := fun c Ψ => by funext g; simp }
    rw [isKFinite_iff]
    refine ⟨(Submodule.span ℂ {Ψ : schwartzA θ V.rank n | ∃ k ∈ K D n, Ψ = ω k Φ}).map L, inferInstance, ?_⟩
    intro k hk
    have e : (fun g : G D n => (ω (g * k) Φ).1 0) = L (ω k Φ) := by
      funext g; simp [L, map_mul]
    rw [e]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, hk, rfl⟩)

end GlobalTheory.StdUnn.SiegelSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.TwistPlaces

theorem sel_under {X : Formalism.L2.Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    (hsel : Formalism.L2.Col.IsSel X sel) {ξ : Formalism.L2.DIV.Chr X.F X.E X.K} {P : HeightOneSpectrum (𝓞 X.E)}
    (h : P ∈ Formalism.L2.Col.QE sel ξ) : sel (P.under (𝓞 X.F)) = P := by
  unfold Formalism.L2.Col.QE at h
  split_ifs at h with hf
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 h
    have e : (sel v).under (𝓞 X.F) = v := HeightOneSpectrum.ext (hsel v)
    rw [e]
  · exact absurd h (Finset.notMem_empty _)

end GlobalTheory.TopVol.TwistPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeClosed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.LevProd.SamePlace

open GlobalTheory.FinPl (Lat latV Moves SplitPt)
open GlobalTheory.IwaPlace (hermAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) {L : Lat V}

theorem half_mem (hL : IntIn q V F L) {g : GA D V} (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y)
    {y : Fin V.rank → Formalism.L2.Theta.AE D} (hy : y ∈ latV V L (· = q.v)) :
    q.e • (Formalism.L2.Theta.mt V g *ᵥ y) ∈ latV V L (· = q.v) := by
  have he : finPart D q.e ∈ intAE D := by
    rw [← GlobalTheory.FinPl.LatIndHalf.sec_one]; exact (q.int_iff 1).1 (one_mem _)
  have h2 : (Formalism.L2.Theta.mt V g).map q.pr = F.β * (GlobalTheory.LevIdx.locHom q V F g).val * F.γ :=
    (GlobalTheory.LevIdx.eq_locHom_iff q V F g _).2 rfl
  have e : q.e • (Formalism.L2.Theta.mt V g *ᵥ y) =
      fun i => q.sec ((F.β *ᵥ ((GlobalTheory.LevIdx.locHom q V F g).val *ᵥ (F.γ *ᵥ fun j => q.pr (y j)))) i) := by
    funext i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← h2, Pi.smul_apply, smul_eq_mul, ← q.sec_pr]
    exact congrArg q.sec (RingHom.map_mulVec q.pr _ y i)
  rw [e]
  refine (hL _).1 (GlobalTheory.LocGl.mulVec_int ((GlobalTheory.LocGl.mem_KO_iff _).1 hg).1 ((hL _).2 ?_))
  rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
  simpa only [q.sec_pr] using GlobalTheory.FinPl.LatIndHalf.mul_mem_latV he hy

theorem act_mem (hsd : IsSelfDualC V L) (hL : IntIn q V F L) {g : GA D V} (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y)
    {y : Fin V.rank → Formalism.L2.Theta.AE D} (hy : y ∈ latV V L (· = q.v)) :
    Formalism.L2.Theta.mt V g *ᵥ y ∈ latV V L (· = q.v) := by
  obtain ⟨s1, -, s2⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L q.v hsd
  have hs := GlobalTheory.IwaPlace.mulVec_mem_idAt (Formalism.L2.Theta.mt V g) (s1 y hy)
  have e : Formalism.L2.Theta.mt V g *ᵥ y =
      q.e • (Formalism.L2.Theta.mt V g *ᵥ y) + cA D q.e • (Formalism.L2.Theta.mt V g *ᵥ y) := by
    rw [← add_smul, GlobalTheory.LocGl.idem_eq]
    exact funext fun i => ((GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (hs i)).symm
  have hg' : GlobalTheory.LevIdx.locHom q V F g⁻¹ ∈ KO k Y := by rw [map_inv]; exact inv_mem hg
  rw [e]
  refine add_mem (half_mem q F hL hg hy) ((s2 _ fun i => Ideal.mul_mem_left _ _ (hs i)).2 fun x hx => ?_)
  have e2 : q.e • x = Formalism.L2.Theta.mt V g *ᵥ (q.e • (Formalism.L2.Theta.mt V g⁻¹ *ᵥ x)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, mul_inv_cancel,
      GlobalTheory.MixModel.mt_one, Matrix.one_mulVec]
  change hermAt V (cA D q.e • (Formalism.L2.Theta.mt V g *ᵥ y)) x ∈ _
  rw [GlobalTheory.LocGl.hermAt_smul, e2, GlobalTheory.LocGl.hermAt_unitary]
  exact (s2 y (s1 y hy)).1 hy _ (half_mem q F hL hg' hx)

theorem moves_of_mem_KO (hsd : IsSelfDualC V L) (hL : IntIn q V F L) {g : GA D V}
    (hg : GlobalTheory.LevIdx.locHom q V F g ∈ KO k Y) : Moves V g L L (· = q.v) := by
  refine fun y _ => ⟨act_mem q F hsd hL hg, fun hy => ?_⟩
  have := act_mem q F hsd hL (g := g⁻¹) (by rw [map_inv]; exact inv_mem hg) hy
  rwa [Matrix.mulVec_mulVec, ← GlobalTheory.MixModel.mt_mul, inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mulVec] at this


end GlobalTheory.LevProd.SamePlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

noncomputable section

namespace GlobalTheory.LevelUnif

open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil GlobalTheory.SymChain
open GlobalTheory.FinPl (SplitPt)
open _root_.Formalism.L2.NTheta (IsIdemAt)

section Elem

variable {κ : Type} [CommRing κ] {r : ℕ}

def elem {i j : Fin r} (h : i ≠ j) (u : κ) : GL (Fin r) κ :=
  ⟨transvection i j u, transvection i j (-u), by rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero],
    by rw [transvection_mul_transvection_same i j h, neg_add_cancel, transvection_zero]⟩

theorem elem_apply {i j : Fin r} (h : i ≠ j) (u : κ) (a b : Fin r) :
    (elem h u).val a b = (1 : Matrix (Fin r) (Fin r) κ) a b + if i = a ∧ j = b then u else 0 := rfl

theorem edgeSum_one (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) :
    edgeSum Ed (1 : GL (Fin r) κ) = 0 := by
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · exact one_apply_ne fun e => hE a (by rwa [← e] at h)
  · rfl

theorem edgeSum_elem (Ed : Fin r → Fin r → Prop) [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) {i j : Fin r} (h : i ≠ j) (hij : Ed i j)
    (u : κ) : edgeSum Ed (elem h u) = u := by
  have h1 : ∀ a b, (if Ed a b then (elem h u).val a b else 0) = if i = a then (if j = b then u else 0) else 0 := fun a b => by
    rw [elem_apply]
    by_cases h2 : Ed a b
    · rw [if_pos h2, one_apply_ne fun e => hE a (by rwa [← e] at h2), zero_add, ite_and]
    · rw [if_neg h2, ← ite_and, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h2 hij
  unfold edgeSum
  simp only [h1]
  simp

theorem elem_mem_unipCol {i j : Fin r} (h : i ≠ j) (hij : i.val < j.val) (u : κ) (a c : ℕ) (hc : j.val ≠ c) :
    elem h u ∈ unipCol κ r a c := by
  refine ⟨⟨fun x y hxy => ?_, fun x => ?_⟩, fun x y h1 h2 h3 => ?_⟩
  · have hxy' : y.val < x.val := hxy
    rw [elem_apply, one_apply_ne (fun e => by rw [e] at hxy'; omega), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    omega
  · rw [elem_apply, one_apply_eq, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact h rfl
  · rw [elem_apply, one_apply_ne (fun e => by rw [e] at h2; omega), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    omega

end Elem

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)
  {PP : Pl D.host.E} (h : IsIdemAt q.e PP) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
include hψ in
theorem chr_near {t : kˣ} (ht : IsUnif t) {y y' : k} (hy : valuation k (y - y') < 1) :
    ψ (((t⁻¹ : kˣ) : k) * y) = ψ (((t⁻¹ : kˣ) : k) * y') := by
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  have triv : ψ (((t⁻¹ : kˣ) : k) * (y - y')) = 1 := (hψ 1).2 (by simp) _ (by
    rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, map_one, inv_mul_le_one₀ tp]
    exact (ht _).1 hy)
  rw [show ((t⁻¹ : kˣ) : k) * y = ((t⁻¹ : kˣ) : k) * (y - y') + ((t⁻¹ : kˣ) : k) * y' by ring, AddChar.map_add_eq_mul, triv, one_mul]


include h hψ in
theorem exists_res {t : kˣ} (ht : IsUnif t) : ∃ α : AddChar (kP PP) ℂ,
    ∀ z, (ψ (((t⁻¹ : kˣ) : k) * prO q z) : ℂ) = α (Ideal.Quotient.mk _ z) := by
  have wd : ∀ z z' : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = Ideal.Quotient.mk PP.asIdeal z' →
      ψ (((t⁻¹ : kˣ) : k) * prO q z) = ψ (((t⁻¹ : kˣ) : k) * prO q z') := fun z z' e =>
    chr_near hψ ht (by rw [← map_sub, ← prO_lt q h]; exact Ideal.Quotient.eq.1 e)
  choose l hl using Ideal.Quotient.mk_surjective (I := PP.asIdeal)
  refine ⟨{ toFun := fun u => ψ (((t⁻¹ : kˣ) : k) * prO q (l u))
            map_zero_eq_one' := by rw [wd _ 0 (by rw [hl, map_zero])]; simp
            map_add_eq_mul' := fun a b => by
              rw [wd _ (l a + l b) (by rw [map_add (f := _), hl, hl, hl]), map_add (f := _), mul_add, AddChar.map_add_eq_mul, Circle.coe_mul] },
    fun z => congrArg (fun c : Circle => (c : ℂ)) (wd _ z (hl _)).symm⟩


include h in
theorem exists_near {y : k} (hy : valuation k y ≤ 1) : ∃ z, valuation k (y - prO q z) < 1 := by
  obtain ⟨-, hi, hd⟩ := place_facts q h
  have h2 : {x : k | valuation k (x - y) < 1} ∈ nhds y := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha⟩ := hd.mem_nhds h2
  have ha' : valuation k ((ofSplit q).pr a - y) < 1 := ha
  have ha1 : valuation k ((ofSplit q).pr a) ≤ 1 := by
    simpa using Valuation.map_add_le (valuation k) ha'.le hy
  obtain ⟨r, s, hs, e⟩ := (hi a).1 ((Valuation.mem_integer_iff _ _).2 ha1)
  have e' : prO q s * (ofSplit q).pr a = prO q r :=
    ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
  obtain ⟨t, p, hp, htp⟩ := PP.isMaximal.exists_inv hs
  refine ⟨t * r, ?_⟩
  have e2 : prO q t * prO q s + prO q p = 1 := by rw [← map_mul, ← map_add (f := _), htp, map_one]
  have e3 : y - prO q (t * r) = (ofSplit q).pr a * prO q p - ((ofSplit q).pr a - y) := by
    rw [map_mul, ← e']
    linear_combination (-(ofSplit q).pr a) * e2
  rw [e3]
  refine Valuation.map_sub_lt _ ?_ ha'
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ha1) ((prO_lt q h p).1 hp)


include h hψ in
theorem near_of_res {t t' : kˣ} (ht : IsUnif t) (ht' : IsUnif t')
    (he : ∀ z, ψ (((t⁻¹ : kˣ) : k) * prO q z) = ψ (((t'⁻¹ : kˣ) : k) * prO q z)) :
    valuation k ((t : k) - t') < valuation k (t : k) := by
  have h1 : ∀ y, valuation k y ≤ 1 → ψ (((t⁻¹ : kˣ) : k) * y) = ψ (((t'⁻¹ : kˣ) : k) * y) := fun y hy => by
    obtain ⟨z, hz⟩ := exists_near q h hy
    rw [chr_near hψ ht hz, chr_near hψ ht' hz, he]
  set c : k := ((t⁻¹ : kˣ) : k) - ((t'⁻¹ : kˣ) : k) with hc
  have h2 : valuation k c ≤ 1 := by
    by_cases c0 : c = 0
    · rw [c0, map_zero]; exact zero_le
    have cp : 0 < valuation k c := zero_lt_iff.2 ((map_ne_zero _).2 c0)
    have := (hψ c).1 fun y hy => by
      have h3 := h1 (c⁻¹ * y) (by rw [map_mul, map_inv₀, inv_mul_le_one₀ cp]; exact hy)
      rw [← mul_inv_eq_one, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, ← hc,
        mul_inv_cancel_left₀ c0] at h3
      exact h3
    simpa using this
  have e : (t : k) - t' = (t : k) * (-c * t') := by
    rw [hc, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    field_simp
    ring
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  rw [e, map_mul]
  refine mul_lt_of_lt_one_right tp ?_
  rw [map_mul, Valuation.map_neg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h2) ((ht' _).2 le_rfl)

theorem psiAt_eq {Ψ : AddChar (AF D.host.F) ℂ} (hc : (ofSplit q).IsChar Ψ ψ) (y : D.host.E) :
    Formalism.IndefR.Mi.psiAt Ψ q.e y = ψ ((ofSplit q).pr y) := by
  rw [hc]
  change _ = Ψ (Algebra.trace _ _ (incA D D.host.xi0 * q.sec (q.pr (incA D y))))
  rw [q.sec_pr, Formalism.IndefR.Mi.psiAt, map_mul (incA D), mul_left_comm]

end Local

theorem norm_notMem_sq {D : D7} {PP : Pl D.host.E} (h : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by
  have hspl : ∀ k, Formalism.MainNotions.S.SplitsCompl D.host.E (D.host.g k) := by
    intro k
    have hp := D.host.g_prime k
    have := Formalism.MainNotions.BridgeLemma.span_isMaximal hp
    apply Formalism.MainNotions.S.splitsCompl_of_ncard _ _ hp
    rw [← IsDedekindDomain.coe_primesOverFinset (Formalism.MainNotions.BridgeLemma.span_ne_bot hp) (𝓞 D.host.E), ← Formalism.MainNotions.BridgeLemma.image_plOver _ hp,
      (Formalism.MainNotions.BridgeLemma.injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k
  rw [Nat.cast_mul] at h
  obtain ⟨k, hk⟩ : ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal :=
    (PP.isPrime.mem_or_mem h).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
  obtain ⟨h1, h2⟩ := hspl k _ PP.isMaximal hk
  unfold Formalism.L2.Col.qOf
  rw [h1]
  exact h2

section Levels

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ}

theorem chi_of_eq {P P' : LevelP Pg r ℂ} (e : P = P') (x : G0 Pg r) (h : x ∈ P'.H) :
    ∃ h' : x ∈ P.H, P.chi ⟨x, h'⟩ = P'.chi ⟨x, h⟩ := by
  subst e
  exact ⟨h, rfl⟩

theorem prod_single {ι : Type} [Fintype ι] (pl : ι ≃ Pg) (α : ∀ i, AddChar (kP (pl i).1) ℂ) (Ed : Fin r → Fin r → Prop)
    [DecidableRel Ed] (hE : ∀ a, ¬ Ed a a) {i j : Fin r} (h : i ≠ j) (hij : Ed i j) (n : ι) (u : kP (pl n).1) :
    ∏ m, α m (edgeSum Ed ((Pi.mulSingle (pl n) (elem h u) : G0 Pg r) (pl m))) = α n u := by
  rw [Finset.prod_eq_single n, Pi.mulSingle_eq_same, edgeSum_elem Ed hE h hij]
  · intro m _ hm
    rw [Pi.mulSingle_eq_of_ne (pl.injective.ne hm), edgeSum_one Ed hE, AddChar.map_zero_eq_one]
  · intro hn
    exact absurd (Finset.mem_univ n) hn

theorem single_mem (H : ∀ PP : Pg, Subgroup (GL (Fin r) (kP PP.1))) (n : Pg) {x : GL (Fin r) (kP n.1)} (hx : x ∈ H n) :
    (Pi.mulSingle n x : G0 Pg r) ∈ Subgroup.pi Set.univ H := fun PP _ => by
  by_cases e : PP = n
  · subst e
    rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne e]
    exact (H PP).one_mem

end Levels

theorem edgeSum_eq_supSum {κ : Type} [CommRing κ] {r : ℕ} (g : GL (Fin r) κ) :
    edgeSum supEdge g = Formalism.IndefR.Mi.supSum (g : Matrix (Fin r) (Fin r) κ) := by
  unfold edgeSum Formalism.IndefR.Mi.supSum
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.1 + 1, h⟩]
    · exact if_pos (show supEdge i ⟨i.1 + 1, h⟩ from rfl)
    · intro j _ hj
      exact if_neg (fun hj' => hj (Fin.ext hj'))
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · refine Finset.sum_eq_zero fun j _ => ?_
    refine if_neg (fun hj => ?_)
    have := j.2
    unfold supEdge at hj
    omega

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

end Gen

end GlobalTheory.LevelUnif

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaAtMoveLat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacMove
variable {D : D7}

theorem mt_mul₀ (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one₀ (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul₀, mul_inv_cancel, mt_one₀, Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : Lat S} {P : Pl D → Prop} (h : Moves S g L M P) :
    Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv] at e
  exact e.symm

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : Lat S} {P : Pl D → Prop} (h : Moves S g L M P)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : mt S g *ᵥ z ∈ latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact GlobalTheory.FinPl.MovedVac.smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_eq (S T : HSp D) (g : GA D S) (h : GA D T) (u : WO S T) :
    actO S T g h u = HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹) := rfl

theorem actO_mem_latO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [actO_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem mem_latO_iff_actO {S T : HSp D} {Λ M : Lat S} {Λ' M' : Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M)
    (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : Pl D → Prop} {g : GA D S} {h : GA D T}
    (hg : Moves S g Λ M P) (hh : Moves T h Λ' M' P) (u : WO S T) :
    u ∈ latO S T (Λ : Set _) (Λ' : Set _) P ↔ actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  refine ⟨actO_mem_latO hΛ hM hΛ' hM' hg hh, fun hu => ?_⟩
  have := actO_mem_latO hM hΛ hM' hΛ' (moves_inv hg) (moves_inv hh) hu
  rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this

end GlobalTheory.VacMove

namespace GlobalTheory.VacMove

theorem isThetaAt_moveLat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Λ M : Lat S) (Λ' M' : Lat T), IsSelfDualC S Λ → IsSelfDualC S M → IsSelfDualC T Λ' → IsSelfDualC T M' → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, Moves S b Λ M (fun _ => True) → Moves T b' Λ' M' (fun _ => True) → ∀ e Φ f₀ f, e * e = e → infPart D e = 0 → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀) (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  intro D ψ S T χS χT om hW Λ M Λ' M' hΛ hM hΛ' hM' b _ b' _ hb hb' e Φ f₀ f hee hinf hf₀ _ hf
  have key := mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := mem_latO_iff_actO hM hΛ hM' hΛ' (moves_inv hb) (moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

end GlobalTheory.VacMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeFinal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.LevProd.OffTwist

theorem entry_mem_of_stab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (hT : (T : 𝓞 F) ∉ v.asIdeal) (L : Submodule (𝓞 E) (Fin n → E))
    (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 E, x j = (r : E)) (h2 : ∀ s, (Pi.single s (T : E) : Fin n → E) ∈ L)
    {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} (g : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hg : g ∈ Formalism.UG.levelVL σ J v L) (r s : Fin n) :
    g.val r s ∈ intV E v := by
  replace hg : g ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L) := hg.2
  have hle : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L, ∀ j, y j ∈ intV E v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      intro j
      obtain ⟨c, hc⟩ := h1 x hx j
      refine Subring.subset_closure (Or.inl ⟨⟨x j, c, hc.symm⟩, rfl⟩)
    | zero => intro j; exact zero_mem _
    | add x y _ _ hx hy => intro j; exact add_mem (hx j) (hy j)
    | smul c x _ hx => intro j; exact mul_mem c.2 (hx j)
  have hv : Valued.v ((T : ℕ) : v.adicCompletion F) = 1 := by
    have e : ((T : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (T : 𝓞 F)) := by
      simp
    rw [e]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hT
  have hne : ((T : ℕ) : v.adicCompletion F) ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact zero_ne_one hv
  have hinv : ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have hc : (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹ ∈ intV E v :=
    Subring.subset_closure (Or.inr ⟨⟨_, hinv⟩, rfl⟩)
  have hmem : (fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s (T : E) : Fin n → E) i)) ∈
      Formalism.UG.latS (F := F) (v.adicCompletion F) (intV E v) L := Submodule.subset_span ⟨_, h2 s, rfl⟩
  have h3 := hle _ ((hg _).1 hmem) r
  have e3 : (g.val *ᵥ fun i => Formalism.UG.inclE (F := F) (v.adicCompletion F) ((Pi.single s (T : E) : Fin n → E) i)) r =
      g.val r s * (T : ℕ) := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [e3] at h3
  have e4 : ((T : ℕ) : E ⊗[F] v.adicCompletion F) * ((1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F)⁻¹) = 1 := by
    have : ((T : ℕ) : E ⊗[F] v.adicCompletion F) = (1 : E) ⊗ₜ[F] ((T : ℕ) : v.adicCompletion F) :=
      (map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := v.adicCompletion F)) T).symm
    rw [this, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hne]
    rfl
  have h4 := mul_mem h3 hc
  rwa [mul_assoc, e4, mul_one] at h4

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prV_toEAf (v : GlobalTheory.FinPl.Pl D) (x : AE D) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D x) =
      Algebra.TensorProduct.comm D.host.F _ _ (GlobalTheory.FinPl.compAt D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero, map_zero]
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, map_add (f := _)]

theorem pr_eq_zero (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (hx : Formalism.UG.prV (E := D.host.E) q.v (toEAf D x) = 0) : q.pr x = 0 := by
  rw [prV_toEAf, map_eq_zero_iff _ (AlgEquiv.injective _)] at hx
  have h1 : GlobalTheory.FinPlLoc.idem D (· = q.v) * x = 0 := by
    rw [← GlobalTheory.FinPlLoc.mem_idOff_iff]
    refine (Submodule.mem_iInf _).2 ?_
    rintro ⟨w, rfl⟩
    exact RingHom.mem_ker.2 hx
  have he := (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.e_mem_idAt q)
  have h2 : q.sec (q.pr x) = 0 := by
    rw [q.sec_pr, ← he, mul_comm (GlobalTheory.FinPlLoc.idem D _), mul_assoc, h1, mul_zero]
  rw [← q.pr_sec (q.pr x), h2, map_zero]


set_option maxHeartbeats 1600000 in
theorem exists_int_lift (v : GlobalTheory.FinPl.Pl D) (y : D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) (hy : y ∈ intV D.host.E v) :
    ∃ x : AE D, finPart D x ∈ intAE D ∧ Formalism.UG.prV (E := D.host.E) v (toEAf D x) = y := by
  have hone : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  induction hy using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨c, rfl⟩
    · refine ⟨(1 : AF D.host.F) ⊗ₜ (c : D.host.E), AddSubgroup.subset_closure ⟨1, hone, c, rfl⟩, rfl⟩
    · let α : Af D.host.F := RestrictedProduct.mk (Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F)
        (Filter.Eventually.of_forall fun w => by
          by_cases h : w = v
          · subst h; rw [Pi.single_eq_same]; exact c.2
          · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
      have hα : α ∈ intAf D.host.F := fun w => by
        show (Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F) w ∈ _
        by_cases h : w = v
        · subst h; rw [Pi.single_eq_same]; exact c.2
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      refine ⟨pairA D.host.F 0 α ⊗ₜ (1 : D.host.E), ?_, ?_⟩
      · rw [GlobalTheory.FinPlLoc.finPart_pair]
        exact AddSubgroup.subset_closure ⟨α, hα, 1, by simp⟩
      · rw [prV_toEAf, GlobalTheory.FinPlLoc.compAt_pair, Algebra.TensorProduct.comm_tmul]
        show (1 : D.host.E) ⊗ₜ[D.host.F] ((Pi.single v c.1 : ∀ w : GlobalTheory.FinPl.Pl D, w.adicCompletion D.host.F) v) = _
        rw [Pi.single_eq_same]
  | zero => exact ⟨0, by rw [RingHom.map_zero]; exact zero_mem _, by rw [RingHom.map_zero, RingHom.map_zero]⟩
  | one =>
    refine ⟨1, ?_, by rw [RingHom.map_one, RingHom.map_one]⟩
    rw [RingHom.map_one, Algebra.TensorProduct.one_def]
    exact AddSubgroup.subset_closure ⟨1, hone, 1, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, by rw [RingHom.map_add (f := _)]; exact add_mem hx hy, by rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]⟩
  | neg a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨-x, by rw [RingHom.map_neg]; exact neg_mem hx, by rw [RingHom.map_neg, RingHom.map_neg]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x * y, by rw [RingHom.map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE hx hy, by rw [RingHom.map_mul, RingHom.map_mul]⟩

theorem pr_mem_int (q : GlobalTheory.FinPl.SplitPt D k) (x : AE D) (hx : Formalism.UG.prV (E := D.host.E) q.v (toEAf D x) ∈ intV D.host.E q.v) :
    q.pr x ∈ 𝒪[k] := by
  obtain ⟨x', h1, h2⟩ := exists_int_lift q.v _ hx
  have h3 : q.pr (x - x') = 0 := pr_eq_zero q _ (by rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self])
  rw [RingHom.map_sub, sub_eq_zero] at h3
  rw [h3, q.int_iff, q.sec_pr, RingHom.map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE ?_ h1
  have := (q.int_iff 1).1 (one_mem _)
  rwa [← map_one q.pr, q.sec_pr, mul_one] at this

theorem conj_int {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] {pos : Y → ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (hF : IsStdFr pos F)
    (M : Matrix (Fin N) (Fin N) k) (hM : ∀ r s, M r s ∈ 𝒪[k]) (a b : Y) : (F.γ * M * F.β) a b ∈ 𝒪[k] := by
  obtain ⟨e, -, he⟩ := hF
  have hγ : F.γ = (1 : Matrix (Fin N) (Fin N) k).submatrix e id := by
    have h1 : (1 : Matrix (Fin N) (Fin N) k).submatrix e id * F.β = 1 := by
      rw [he, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one, Matrix.submatrix_one_equiv]
    rw [← Matrix.one_mul F.γ, ← h1, Matrix.mul_assoc, F.βγ, Matrix.mul_one]
  have h : F.γ * M * F.β = M.submatrix e e := by
    rw [hγ, he]
    conv_lhs => rw [← Matrix.submatrix_id_id M]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.one_mul, Matrix.mul_one]
  rw [h]
  exact hM _ _

theorem locHom_mem_KO (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) {n : ℕ} (hn : S.rank = n) {Y : Type} [Fintype Y] [DecidableEq Y]
    {pos : Y → ℕ} (F : GlobalTheory.LocMod.Frame k S.rank Y) (hF : IsStdFr pos F) (T : ℕ) (hT : (T : 𝓞 D.host.F) ∉ q.v.asIdeal)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (h1 : ∀ x ∈ L, ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (h2 : ∀ s, (Pi.single s (T : D.host.E) : Fin n → D.host.E) ∈ L) {σ : D.host.E →ₐ[D.host.F] D.host.E}
    {J : Matrix (Fin n) (Fin n) D.host.E} (U : Subgroup (GA D S))
    (hU : ∀ g ∈ U, ∃ κ : GL (Fin n) (EF D), κ.val = finM S hn g ∧ Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) q.v) κ ∈
      Formalism.UG.levelVL σ J q.v L) :
    ∀ g ∈ U, GlobalTheory.LevIdx.locHom q S F g ∈ KO k Y := by
  subst hn
  have key : ∀ g ∈ U, ∀ a b, (GlobalTheory.LevIdx.locHom q S F g).val a b ∈ 𝒪[k] := by
    intro g hg
    obtain ⟨κ, hκ, hs⟩ := hU g hg
    refine conj_int F hF _ fun r s => ?_
    have h := entry_mem_of_stab q.v T hT L h1 h2 _ hs r s
    have e : (Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) q.v) κ).val r s =
        Formalism.UG.prV (E := D.host.E) q.v (toEAf D (mt S g r s)) := by
      show Formalism.UG.prV (E := D.host.E) q.v (κ.val r s) = _
      rw [hκ]; rfl
    rw [e] at h
    exact pr_mem_int q _ h
  intro g hg
  rw [GlobalTheory.SplitFlip.mem_KO_iff, ← map_inv]
  exact ⟨key g hg, key _ (inv_mem hg)⟩

end GlobalTheory.LevProd.OffTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMemLatOIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.LastPrim
variable {D : D7}

theorem latV_entry_mem' {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) (i : Fin S.rank) : y i ∈ idAt D P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, -, hβ, c, -, x, -, rfl⟩ := hz
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hβ _
  | zero => exact zero_mem _
  | add z z' _ _ hz hz' => exact add_mem hz hz'
  | neg z _ hz => exact neg_mem hz

theorem incAdj_yZero_mulVec : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (hρ : 0 < ρ) (a : AE D) (y : Fin B.V₀.rank → AE D),
    Matrix.mulVec (show Matrix (Fin J.W.rank) (Fin B.V₀.rank) (AE D) from J.d.incAdj B.V₀ (a • yZero B.V₀ ρ (vecB B.o B.ζ))) y =
      colMul J.d.jY ⟨ρ - 1, by omega⟩ (incA D D.host.xi0⁻¹ * cA D a * (∑ l, (∑ m, cA D (ratV (vecB B.o B.ζ) m) * gA B.V₀ m l) * y l)) := by
  intro D ρ B J hρ a y
  funext k
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | omega | simp
  simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, adj_smul, adj_neg, colMul, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell]
  rw [Finset.sum_congr rfl fun l _ => by
    rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]]
  simp only [ite_true, mul_one, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem cA_mem_idAt'' {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem smul_colMul {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (s t : AE D) :
    s • colMul d.jY i t = colMul d.jY i (s * t) := by
  funext k
  simp only [colMul, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem colMul_jY_mem_latA_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (𝔟 : FI D) (v : Pl D) (i : Fin ρ), 𝔟 ≠ 0 →
      (∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV 𝔟⁻¹ v) →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latA S L (· = v) ↔ cA D t ∈ idV ((D.host.AAbar : FI D) * 𝔟⁻¹) v := by
  intro D ψ hψ S S₀ ρ d L 𝔟 v i h𝔟 hL t ht
  obtain ⟨-, h2, -, h4, -, -, h7⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hAAb : (D.host.AAbar : FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hct := cA_mem_idAt'' ht
  have hconj : ∀ s, s ∈ idV (D.host.AA : FI D)⁻¹ v ↔ cA D s ∈ idV (D.host.AAbar : FI D)⁻¹ v := by
    intro s
    have := h4 (-1) s
    rwa [_root_.zpow_neg_one, _root_.zpow_neg_one] at this
  rw [h7, ← inv_inv (D.host.AAbar : FI D), mul_comm, ← h2 _ _ (inv_ne_zero hAAb) (inv_ne_zero h𝔟) _ hct]
  constructor
  · rintro ⟨-, h⟩ a ha
    have hs : cA D a ∈ idV (D.host.AA : FI D)⁻¹ v := by rw [hconj, cA_cA]; exact ha
    have h1 := h _ hs
    rw [smul_colMul, hL _ (Ideal.mul_mem_left _ _ ht), map_mul, cA_cA] at h1
    rw [mul_comm]; exact h1
  · intro h
    refine ⟨fun k => Ideal.mul_mem_right _ _ ht, fun s hs => ?_⟩
    rw [smul_colMul, hL _ (Ideal.mul_mem_left _ _ ht), map_mul, mul_comm]
    exact h _ ((hconj s).1 hs)

end GlobalTheory.SeeSaw.LastPrim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam.FinData

theorem isFinComb_smul {D : D7} {S T : HSp D} (r : ℂ) (c : WO S T →₀ ℂ) (h : GlobalTheory.SeeSaw.IsFinComb c) :
    GlobalTheory.SeeSaw.IsFinComb (r • c) := fun u hu => h u (Finsupp.support_smul hu)

end GlobalTheory.Fam.FinData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.FamTraceChiCol


open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain in
theorem conj_embX_toBlocks₂₂ {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((typeFrame ϖ ord).bas⁻¹ * embX c g * (typeFrame ϖ ord).bas).val.toBlocks₂₂ = 1 := by
  have e1 : (typeFrame ϖ ord).bas.val = fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val := rfl
  have e2 : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val := by
    change (embA n _)⁻¹.val = _
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, show (embX c g).val = fromBlocks g.val 0 0 1 from rfl,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₂, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
    Units.inv_mul]

end GlobalTheory.FamTraceChiCol

noncomputable section
namespace GlobalTheory.FamTraceChiCol


end GlobalTheory.FamTraceChiCol
end
end
