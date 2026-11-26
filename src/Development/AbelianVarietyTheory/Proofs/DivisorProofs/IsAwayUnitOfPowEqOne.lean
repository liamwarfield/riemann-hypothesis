module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValuationNonnegIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionSumJetNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationSectionBasisPullbackAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
noncomputable section

open Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ChiGrid
open GlobalTheory.SqTop (twPl Qn)
open GlobalTheory.Square (IsAwayUnit)
open GlobalTheory.RowTest (LocIn NumbersIn)

namespace GlobalTheory.KappaArith

theorem isAwayUnit_of_pow_eq_one {K : Type} [Field K] (m : ℕ) {z : K} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    IsAwayUnit m z := by
  have hint : IsIntegral ℤ z :=
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [hz]⟩
  let a : 𝓞 K := ⟨z, hint⟩
  have ha : (a : K) = z := rfl
  refine ⟨a, 0, 0, ⟨a ^ (n - 1), ?_⟩, by simp [ha]⟩
  rw [pow_zero]
  apply RingOfIntegers.ext
  have e1 : ((a * a ^ (n - 1) : 𝓞 K) : K) = z * z ^ (n - 1) := by rw [← ha]; norm_cast
  rw [e1, ← pow_succ', Nat.sub_add_cancel hn, hz]
  rfl

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)

def AwayIm (D : D7) (m : ℕ) (z : ℂ) : Prop := ∃ ζ : D.what₂.LL, IsAwayUnit m ζ ∧ D.what₂.embLL ζ = z

theorem awayIm_one (m : ℕ) : AwayIm D m 1 := ⟨1, IsAwayUnit.one m, map_one _⟩

theorem AwayIm.mul {m : ℕ} {z z' : ℂ} (h : AwayIm D m z) (h' : AwayIm D m z') : AwayIm D m (z * z') := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨b, hb, rfl⟩ := h'
  exact ⟨a * b, ha.mul hb, map_mul _ _ _⟩

theorem AwayIm.prod {m : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, AwayIm D m (f i)) :
    AwayIm D m (∏ i ∈ s, f i) :=
  Finset.prod_induction f (AwayIm D m) (fun _ _ => AwayIm.mul) (awayIm_one m) h

theorem awayIm_val {μ₀ : T} (hL : Lc.Is μ₀) {t : T} (hx : LocIn D.what₂.embLL (Lc.xiH t)) (m : ℕ)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (x : (w.adicCompletion D.host.E)ˣ) :
    AwayIm D m ((Lc.xiH t).loc w x : ℂ) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  obtain ⟨ζ, hζ⟩ := hx w x
  have h1 : ((Lc.xiH t).loc w x) ^ n = 1 := by
    have : ((Lc.xiH t) ^ n).loc w x = 1 := by rw [show (Lc.xiH t) ^ n = 1 from ho]; rfl
    exact this
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.KappaArith

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantExponentsMatchingWeightBarGap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantExponentsMatchingWeightBarGap
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.WtMatchArithBar

theorem exists_shift {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (f : Fin (p + q) → ℤ) (hf : Antitone f)
    (hg0 : 1 ≤ GlobalTheory.CompHS.gap f (p - 1))
    (N M k : ℕ) (hN : 0 < N) (hk : 2 * M + N ≤ k + 1) :
    ∃ w : ℤ, (∀ i : Fin (p + q), (i : ℕ) < p → 0 ≤ ((k : ℤ) + 1) * f i + N * w - M) ∧
      (∀ i : Fin (p + q), p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * f i) - N * w - M) := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  set X : ℤ := ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ - M with hX
  refine ⟨-(X / N), fun i hi => ?_, fun i hi => ?_⟩
  · have h1 : f i ≥ f ⟨p - 1, by omega⟩ := hf (by simp [Fin.le_def]; omega)
    have h2 : ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ ≤ ((k : ℤ) + 1) * f i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 := Int.emod_nonneg X (by omega : (N : ℤ) ≠ 0)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    linarith
  · have h1 : f i ≤ f ⟨p, by omega⟩ := hf (by simp [Fin.le_def]; omega)
    have hg := hg0
    unfold GlobalTheory.CompHS.gap at hg
    rw [dite_eq_left (by omega)] at hg
    have e : (⟨p - 1 + 1, by omega⟩ : Fin (p + q)) = ⟨p, by omega⟩ := Fin.ext (by simp; omega)
    rw [e] at hg
    have h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * (f ⟨p - 1, by omega⟩ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 := Int.emod_lt_of_pos X (by omega : (0 : ℤ) < N)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    have hk' : (2 * M + N : ℤ) ≤ k + 1 := by exact_mod_cast hk
    nlinarith


open GlobalTheory.AllWt in
theorem exists_dom_exponents_bar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), 1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  intro E _ _ _ H Dw la hp hq hanti hgap N M k hN hk
  have key : ∀ σ : Psi H, ∃ w : ℤ,
      (∀ i : Fin (Dw.p + Dw.q), (i : ℕ) < Dw.p → 0 ≤ ((k : ℤ) + 1) * la σ i + N * w - M) ∧
      (∀ i : Fin (Dw.p + Dw.q), Dw.p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * la σ i) - N * w - M) :=
    fun σ => exists_shift hp hq (la σ) (hanti σ) (hgap σ) N M k hN hk
  choose w hwb hws using key
  have hantiσ : ∀ (σ : Psi H) (i j : Fin (Dw.p + Dw.q)), i ≤ j → la σ j ≤ la σ i :=
    fun σ _ _ h => hanti σ h
  set val : (E →+* ℂ) × ℕ → ℤ := fun x => ((k : ℤ) + 1) * (wtOf Dw la 0).1 x +
    (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 x with hval
  have vbig : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.p),
      val (σ.1, i) = ((k : ℤ) + 1) * la σ ⟨i, by omega⟩ + (N * w σ - M) := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_big _ _ σ i hi, wtOf_big _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
  have vsmall : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.q),
      val (conjEmb σ.1, i) = -(((k : ℤ) + 1) * la σ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩) - N * w σ - M := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_small _ _ σ i hi, wtOf_small _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
    ring
  have split : ∀ τ : E →+* ℂ, (∃ σ : Psi H, σ.1 = τ ∧ Dw.mult τ = Dw.p) ∨
      (∃ σ : Psi H, conjEmb σ.1 = τ ∧ Dw.mult τ = Dw.q) := by
    intro τ
    by_cases h : τ (H.rt : E) = H.rt0
    · exact Or.inl ⟨⟨τ, h⟩, rfl, by simp [Datum.mult, h]⟩
    · exact Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, AllWt.conjEmb_conjEmb τ, by simp [Datum.mult, h]⟩
  have nonneg : ∀ (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → 0 ≤ val (τ, i) := by
    intro τ i hi
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hi; rw [vbig σ i hi]; have := hwb σ ⟨i, by omega⟩ hi; linarith
    · rw [hm] at hi; rw [vsmall σ i hi]; exact hws σ _ (by simp)
  have mono : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → val (τ, j) ≤ val (τ, i) := by
    intro τ i j hij hj
    have hk0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hj
      rw [vbig σ i (by omega), vbig σ j hj]
      have := hantiσ σ ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.le_def]; omega)
      nlinarith
    · rw [hm] at hj
      rw [vsmall σ i (by omega), vsmall σ j hj]
      have := hantiσ σ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
        (by simp [Fin.le_def]; omega)
      nlinarith
  refine ⟨w, fun x => if x.2 < Dw.mult x.1 then (val x).toNat else 0, ⟨fun τ => ?_, even_two_mul M⟩, ?_⟩
  · intro i j hij
    simp only
    split_ifs with hj hi hi
    · exact Int.toNat_le_toNat (mono τ i j hij hj)
    · omega
    · exact Nat.zero_le _
    · exact le_refl _
  · funext x
    rcases x with _ | ⟨τ, i⟩
    · simp [ex, exOf, exZ, wtOf]
    · have hi : (i : ℕ) < Dw.mult τ := i.2
      show (((if (i : ℕ) < Dw.mult τ then (val (τ, (i : ℕ))).toNat else 0 : ℕ)) : ℤ) = _
      rw [if_pos hi, Int.toNat_of_nonneg (nonneg τ i hi)]
      rw [Pi.add_apply, Pi.smul_apply]
      show _ = (k + 1) • (wtOf Dw la 0).1 (τ, (i : ℕ)) +
        (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 (τ, (i : ℕ))
      rw [nsmul_eq_mul]
      simp only [hval]
      push_cast
      ring

end GlobalTheory.WtMatchArithBar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantExponentsMatchingWeightBarGapStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_exponents_matching_weight_bar_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), 1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  first | exact @GlobalTheory.WtMatchArithBar.exists_dom_exponents_bar | exact GlobalTheory.WtMatchArithBar.exists_dom_exponents_bar | (intros; apply GlobalTheory.WtMatchArithBar.exists_dom_exponents_bar <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.WtMatchBar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_mem_secZ {ex : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (n : ℕ) :
    f ^ n ∈ GlobalTheory.AllWt.secZ Xo c (n • ex) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ n ih => rw [pow_succ, succ_nsmul]; exact GlobalTheory.AllWt.mul_mem_secZ ih hf

theorem nsmul_exOf_zero_one (m : ℕ) : m • GlobalTheory.AllWt.exOf Dw 0 1 = GlobalTheory.AllWt.exOf Dw 0 m := by
  induction m with
  | zero => rw [zero_smul]; funext i; rw [Nat.cast_zero, GlobalTheory.AllWt.exOf, GlobalTheory.AllWt.wtOf_zero]; cases i <;> rfl
  | succ m ih =>
    rw [succ_nsmul, ih, ← GlobalTheory.AllWt.exOf_add, add_zero]; push_cast; rfl

theorem val_pow_succ_nonneg {la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : IsVal la v) {f : Rul Xo c} (hf : 0 ≤ v f) (n : ℕ) : 0 ≤ v (f ^ (n + 1)) := by
  induction n with
  | zero => rw [pow_one]; exact hf
  | succ n ih => rw [pow_succ, hv.mul]; exact add_nonneg ih hf


end GlobalTheory.WtMatchBar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripleWeilTransfer

variable {D : D7}

theorem isThetaFunO_of_mem_algF {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (ε : Bool) {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) {Φ : WO M X → ℂ}
    (hΦ : Φ ∈ algF ψ θ ε A B) : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, P, hf, rfl⟩ := hx
    exact GlobalTheory.GalLift.Vec.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
  | zero => exact GlobalTheory.OrientedHeis.theta_zero
  | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
  | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx

theorem eq_on_theta {ψ : AddChar (AF D.host.F) ℂ} (ε : Bool) {M X : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    {ω ω' : GlobalTheory.Grid.WRep M X} (h : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω) (h' : GlobalTheory.Grid.IsWeil ψ ε M X χ χ' ω')
    (p : GA D M × GA D X) (f : WO M X → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.Grid.sgn ε M) X f) : ω p f = ω' p f := by
  have e := GlobalTheory.WeilUniq.weilDatum_unique D ψ h.std _ X χ χ' _ _ h h' ((GlobalTheory.Grid.ofSgn ε M).symm p.1, p.2) f hf
  simpa [GlobalTheory.Grid.WRep.toSgn] using e

theorem isCoinvMap_congr {θ : InfFam D} {M X : HSp D} {ω ω' : GlobalTheory.Grid.WRep M X} {S : Submodule ℂ (WO M X → ℂ)}
    {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
    {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO M X → ℂ) →ₗ[ℂ] Pi}
    (he : ∀ q, ∀ Φ ∈ S, ω q Φ = ω' q Φ) (h : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω S Pi rf rl p) : GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsCoinvMap θ ω' S Pi rf rl p := by
  obtain ⟨⟨sM1, sM2⟩, ⟨sX1, sX2⟩, onto, invf, invl, eqf, eql⟩ := h
  refine ⟨⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩, onto,
    fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_, fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ Φ' hΦ' hd => ?_⟩
  · rw [← he _ Φ hΦ]; exact sM1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sM2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact sX1 g hg Φ hΦ
  · obtain ⟨Φ', h1, h2⟩ := sX2 τ Y hY Φ hΦ
    refine ⟨Φ', h1, fun z => ?_⟩
    simpa only [he _ Φ hΦ] using h2 z
  · rw [← he _ Φ hΦ]; exact invf g hg Φ hΦ
  · exact invl τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)
  · rw [← he _ Φ hΦ]; exact eqf g hg Φ hΦ
  · exact eql τ Y hY Φ hΦ Φ' hΦ' (fun z => by simpa only [he _ Φ hΦ] using hd z)

end GlobalTheory.TripleWeilTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentredPointPhiPositiveWeights
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem vV_algebraMap_unit (T : CDVR) (u : T.Vˣ) : vV T.V (algebraMap T.V T.Fr (u : T.V)) = 0 := by
  have h1 : valV T.V (algebraMap T.V T.Fr (u : T.V)) = 1 := by
    unfold valV
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    refine (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 ?_
    show (u : T.V) ∉ IsLocalRing.maximalIdeal T.V
    exact fun h => h u.isUnit
  simp [vV, h1]

theorem log_ofAdd_neg (m : ℤ) :
    WithZero.log ((Multiplicative.ofAdd (-m) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = -m := by
  first | rfl | simp [WithZero.log] | exact WithZero.log_coe _

theorem isLocalHom_of_centred {Y : Scheme.{0}} {y : Y} {ν : Valuation (Y.presheaf.stalk y) (WithZero (Multiplicative ℤ))}
    (hν : Centred y ν) (T : CDVR) (g : Y.presheaf.stalk y →+* T.V) (ρ : ℝ) (hρ : 0 < ρ)
    (hval : ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (vV T.V (algebraMap T.V T.Fr (g a)) : ℝ)) :
    IsLocalHom g := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ IsLocalRing.maximalIdeal _ := hna
  have h0 : ν a ≠ 0 := by
    intro h
    rw [hν.2.2 a h, map_zero] at ha
    exact not_isUnit_zero ha
  have hlt := hν.2.1 a hm
  have hlog : WithZero.log (ν a) < 0 := by
    have := (WithZero.log_lt_log h0 one_ne_zero).2 hlt
    simpa using this
  have hv := hval a h0
  obtain ⟨u, hu⟩ := ha
  rw [← hu, vV_algebraMap_unit] at hv
  have : (0 : ℝ) < -((WithZero.log (ν a) : ℤ) : ℝ) := by
    have : ((WithZero.log (ν a) : ℤ) : ℝ) < 0 := by exact_mod_cast hlog
    linarith
  rw [hv] at this
  simp at this


end GlobalTheory.HSApp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyAnyRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyAnyRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

def semiToLin {S R : Type} [CommRing S] [CommRing R] [Algebra S R] {M N : Type} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N] (f : M →ₛₗ[algebraMap S R] N) :
    M →ₗ[S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' s m := by simp [f.map_smulₛₗ, algebraMap_smul]

theorem fp_of_tensor_equiv {S R M N : Type} [CommRing S] [CommRing R] [Algebra S R] [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module R N] {g : ℕ} (e : R ⊗[S] M ≃ₗ[R] N) (h : FP S M g) : FP R N g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, fun p => ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_baseChange, h3]

theorem wedge_of_isBaseChange {S R M N M₂ N₂ : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N]
    [AddCommGroup M₂] [Module S M₂] [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower S R N₂]
    {φ : M →ₗ[S] N} {ψ : M₂ →ₗ[S] N₂} (hφ : IsBaseChange R φ) (hψ : IsBaseChange R ψ)
    (cM : M →ₗ[S] M →ₗ[S] M₂) (cN : N →ₗ[R] N →ₗ[R] N₂) (hc : ∀ m m', ψ (cM m m') = cN (φ m) (φ m'))
    (eM : ⋀[S]^2 M ≃ₗ[S] M₂) (heM : ∀ a b, eM (exteriorPower.ιMulti S 2 ![a, b]) = cM a b) :
    ∃ e : ⋀[R]^2 N ≃ₗ[R] N₂, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cN a b := by
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hφ 2
  let e : ⋀[R]^2 N ≃ₗ[R] N₂ := hE.equiv.symm ≪≫ₗ eM.baseChange S R _ _ ≪≫ₗ hψ.equiv
  refine ⟨e, ?_⟩
  have key : ∀ m m', e (exteriorPower.ιMulti R 2 ![φ m, φ m']) = cN (φ m) (φ m') := by
    intro m m'
    have h1 : exteriorPower.ιMulti R 2 ![φ m, φ m'] =
        GlobalTheory.exteriorPowerMapOver R 2 φ (exteriorPower.ιMulti S 2 ![m, m']) := by
      rw [GlobalTheory.exteriorPowerMapOver_ιMulti]
      congr 1
      funext k
      fin_cases k <;> rfl
    have h2 : hE.equiv.symm (GlobalTheory.exteriorPowerMapOver R 2 φ (exteriorPower.ιMulti S 2 ![m, m'])) =
        1 ⊗ₜ exteriorPower.ιMulti S 2 ![m, m'] := by
      rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
    rw [h1]
    change hψ.equiv (eM.baseChange S R _ _ (hE.equiv.symm _)) = _
    rw [h2, LinearEquiv.baseChange_tmul, IsBaseChange.equiv_tmul, one_smul, heM, hc]
  let iw := exteriorPower.ιMulti R 2 (M := N)
  have u0 : ∀ a b x : N, (![x, b] : Fin 2 → N) = Function.update ![a, b] 0 x := by
    intro a b x; funext k; fin_cases k <;> simp
  have u1 : ∀ a b x : N, (![a, x] : Fin 2 → N) = Function.update ![a, b] 1 x := by
    intro a b x; funext k; fin_cases k <;> simp
  have add0 : ∀ a a' b : N, iw ![a + a', b] = iw ![a, b] + iw ![a', b] := by
    intro a a' b
    have := iw.map_update_add ![a, b] 0 a a'
    rwa [← u0 a b (a + a'), ← u0 a b a, ← u0 a b a'] at this
  have add1 : ∀ a b b' : N, iw ![a, b + b'] = iw ![a, b] + iw ![a, b'] := by
    intro a b b'
    have := iw.map_update_add ![a, b] 1 b b'
    rwa [← u1 a b (b + b'), ← u1 a b b, ← u1 a b b'] at this
  have smul0 : ∀ (r : R) (a b : N), iw ![r • a, b] = r • iw ![a, b] := by
    intro r a b
    have := iw.map_update_smul ![a, b] 0 r a
    rwa [← u0 a b (r • a), ← u0 a b a] at this
  have smul1 : ∀ (r : R) (a b : N), iw ![a, r • b] = r • iw ![a, b] := by
    intro r a b
    have := iw.map_update_smul ![a, b] 1 r b
    rwa [← u1 a b (r • b), ← u1 a b b] at this
  have zero0 : ∀ b : N, iw ![0, b] = 0 := fun b => by
    simpa using smul0 0 0 b
  have zero1 : ∀ a : N, iw ![a, 0] = 0 := fun a => by
    simpa using smul1 0 a 0
  intro a b
  induction a using hφ.inductionOn with
  | add x y hx hy => simp only [iw] at add0; rw [add0, map_add (f := _), hx, hy, map_add (f := _), LinearMap.add_apply]
  | smul r x hx => simp only [iw] at smul0; rw [smul0, map_smul, hx, map_smul, LinearMap.smul_apply]
  | tmul m =>
    induction b using hφ.inductionOn with
    | add x y hx hy => simp only [iw] at add1; rw [add1, map_add (f := _), hx, hy, map_add (f := _)]
    | smul r x hx => simp only [iw] at smul1; rw [smul1, map_smul, hx, map_smul]
    | tmul m' => exact key m m'

theorem tensor_equiv_of_tower {S R R' M N P : Type} [CommRing S] [CommRing R] [CommRing R'] [Algebra S R]
    [Algebra R R'] [Algebra S R'] [IsScalarTower S R R'] [AddCommGroup M] [Module S M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R' P]
    (φ : M →ₛₗ[algebraMap S R] N) (χ : N →ₛₗ[algebraMap R R'] P) (θ : M →ₛₗ[algebraMap S R'] P)
    (hθ : ∀ m, χ (φ m) = θ m) (e1 : R ⊗[S] M ≃ₗ[R] N) (he1 : ∀ m, e1 (1 ⊗ₜ m) = φ m)
    (e2 : R' ⊗[S] M ≃ₗ[R'] P) (he2 : ∀ m, e2 (1 ⊗ₜ m) = θ m) :
    ∃ e : R' ⊗[R] N ≃ₗ[R'] P, ∀ c, e (1 ⊗ₜ c) = χ c := by
  refine ⟨(e1.symm.baseChange R R' _ _) ≪≫ₗ AlgebraTensorModule.cancelBaseChange S R R' R' M ≪≫ₗ e2,
    fun c => ?_⟩
  obtain ⟨x, rfl⟩ := e1.surjective c
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    have h1 : e1 (r ⊗ₜ m) = r • φ m := by
      rw [← he1, ← e1.map_smul, smul_tmul', smul_eq_mul, _root_.mul_one]
    have h2 : (algebraMap R R' r) ⊗ₜ[S] m = (algebraMap R R' r) • ((1 : R') ⊗ₜ[S] m) := by
      rw [smul_tmul', smul_eq_mul, _root_.mul_one]
    simp only [LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul, LinearEquiv.symm_apply_apply,
      AlgebraTensorModule.cancelBaseChange_tmul]
    rw [Algebra.smul_def, _root_.mul_one, h2, e2.map_smul, he2, h1, χ.map_smulₛₗ, hθ]
  | add x y hx hy => simp only [tmul_add, map_add (f := _), hx, hy]

theorem oStr_of_noetherian : OStr := by
  intro R _ A _ g hA hg
  obtain ⟨S, B, _, φ, -, hfg, hB, hBg, hpb⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g A ∅ hA hg
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  obtain ⟨hFP, hW, hBC1, hBC2⟩ := GlobalTheory.T.abelianScheme_structureSheafCohomology_noetherian S B g hB hBg
  have hAB : IsPullback φ A.hom B.hom (spMap (algebraMap S R)) := hpb.1
  obtain ⟨e1, he1⟩ := hBC1 R A.left A.hom φ hAB
  obtain ⟨e2, he2⟩ := hBC2 R A.left A.hom φ hAB
  have hp1 : IsBaseChange R (semiToLin (pullHO1 hAB.w)) := IsBaseChange.of_equiv e1 he1
  have hp2 : IsBaseChange R (semiToLin (pullHO2 hAB.w)) := IsBaseChange.of_equiv e2 he2
  have hcomp := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  refine ⟨fp_of_tensor_equiv e1 hFP, ?_, ?_, ?_⟩
  · obtain ⟨eM, heM⟩ := hW
    exact wedge_of_isBaseChange hp1 hp2 (cup _) (cup _)
      ((hcomp.2.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w).1) eM heM
  · intro R' _ _ X' s' ψ h
    letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
    haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have es : spMap (algebraMap R R') ≫ spMap (algebraMap S R) = spMap (algebraMap S R') := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have hc : IsPullback (ψ ≫ φ) s' B.hom (spMap (algebraMap S R')) := es ▸ h.paste_horiz hAB
    obtain ⟨e3, he3⟩ := hBC1 R' X' s' (ψ ≫ φ) hc
    exact tensor_equiv_of_tower (pullHO1 hAB.w) (pullHO1 h.w) (pullHO1 hc.w)
      ((hcomp.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w R' X' s' (algebraMap R R') ψ h.w
        (algebraMap S R') (ψ ≫ φ) hc.w rfl (fun _ => rfl)).1) e1 he1 e3 he3
  · intro R' _ _ X' s' ψ h
    letI : Algebra S R' := ((algebraMap R R').comp (algebraMap S R)).toAlgebra
    haveI : IsScalarTower S R R' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have es : spMap (algebraMap R R') ≫ spMap (algebraMap S R) = spMap (algebraMap S R') := by
      simp only [spMap, ← Spec.map_comp]; rfl
    have hc : IsPullback (ψ ≫ φ) s' B.hom (spMap (algebraMap S R')) := es ▸ h.paste_horiz hAB
    obtain ⟨e3, he3⟩ := hBC2 R' X' s' (ψ ≫ φ) hc
    exact tensor_equiv_of_tower (pullHO2 hAB.w) (pullHO2 h.w) (pullHO2 hc.w)
      ((hcomp.1 S R B.left A.left B.hom A.hom (algebraMap S R) φ hAB.w R' X' s' (algebraMap R R') ψ h.w
        (algebraMap S R') (ψ ≫ φ) hc.w rfl (fun _ => rfl)).2.1) e2 he2 e3 he3

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeStructureSheafCohomologyAnyRingStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_structureSheafCohomology_anyRing : GlobalTheory.AbCoh.OStr := by
  first | exact @GlobalTheory.AbCoh.oStr_of_noetherian | exact GlobalTheory.AbCoh.oStr_of_noetherian | (intros; apply GlobalTheory.AbCoh.oStr_of_noetherian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AbCoh.oStr : GlobalTheory.AbCoh.OStr := GlobalTheory.T.abelianScheme_structureSheafCohomology_anyRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_structure_cohomology_statement : GlobalTheory.AbCoh.OStr := by
  first | exact @GlobalTheory.AbCoh.oStr | exact GlobalTheory.AbCoh.oStr | (intros; apply GlobalTheory.AbCoh.oStr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_free_hodge_baseChange : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧
      GlobalTheory.Published.AbelianDeRham.BaseChange := by
  intro hH
  obtain ⟨hF, hBC, -⟩ := GlobalTheory.abelianDeRham_free_baseChange_rigid hH
  exact ⟨hF, GlobalTheory.AbelianHodge.abelianDeRham_hodge
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH, hBC⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChangeStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSchemeDeRham_free_hodgeSequence_baseChange : GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧ GlobalTheory.Published.AbelianDeRham.BaseChange := by
  first | exact @GlobalTheory.abelianDeRham_free_hodge_baseChange | exact GlobalTheory.abelianDeRham_free_hodge_baseChange | (intros; apply GlobalTheory.abelianDeRham_free_hodge_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSignatureOfGramEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotDict

open GlobalTheory.ChainFr GlobalTheory.SquareComm

variable {D : D7}

theorem gramAt_eq_one {V : HSp D} (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

def stdFr (V : HSp D) (h : V.gram = 1) : Fr V where
  ε _ _ := true
  fr _ := 1
  fr_unit _ := isUnit_one
  fr_gram τ := by
    rw [gramAt_eq_one h τ]
    simp [Formalism.REAL.Jm]

theorem cart_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (stdFr V h).cart τ = 1 := by
  simp [Fr.cart, stdFr, Formalism.REAL.Jm]

theorem onb_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (stdFr V h).onb τ = 1 := by
  simp [Fr.onb, stdFr]

theorem cart_frSgn_true_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (frSgn true (stdFr V h)).cart τ = -1 := by
  simp only [Fr.cart, frSgn, stdFr, Formalism.REAL.Jm]
  ext a b
  by_cases hab : a = b
  · subst hab; simp
  · simp [Matrix.one_apply, hab]

theorem cart_frSgn_false_stdFr (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : (frSgn false (stdFr V h)).cart τ = 1 := by
  simp [Fr.cart, frSgn, stdFr, Formalism.REAL.Jm]

theorem hasSignature_of_gram_eq_one {V : HSp D} (h : V.gram = 1) (τ : D.what₂.Tau) :
    Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := by
  refine ⟨(Equiv.sumEmpty (Fin V.rank) (Fin 0)).symm, 1, ?_⟩
  rw [gramAt_eq_one h τ]
  ext (a | a) (b | b)
  · simp [Formalism.UG.Jpq, Formalism.UG.cT, Matrix.one_apply]
  · exact b.elim0
  · exact a.elim0
  · exact a.elim0

end GlobalTheory.BotDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepSquarePairCharactersAlphaQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepSquarePairCharactersAlphaQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem resEtaPow_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} {n m : ℕ}
    (h : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n)
    (h' : GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ' m) :
    GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (χ / χ') (m + n) := by
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

theorem isHecke_div {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ χ' : (AF F ⊗[F] E)ˣ →* Circle} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem squareWeil₁ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (alpha G t i j) (alpha G t i j / beta G i j) om := by
  intro D T L sc G μ₀ hL t i j _hst B hB X Y r s r' s' hX hY Mo hMo
  have hα : GlobalTheory.LFun.IsHecke D.host.F D.host.E (alpha G t i j) := by
    have hm := (hL.mu0 j).1
    have hx := (hL.xi t).1
    have he := hL.eta.1
    refine ⟨(hm.1.mul hx.1).mul (he.1.pow _), fun x => ?_⟩
    have e1 := hm.2 x
    have e2 := hx.2 x
    have e3 := he.2 x
    show L.mu0 ((j : ℕ) + 1) _ * L.xi t _ * (L.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply]
    rw [e1, e2, e3]
    simp
  have hβ : GlobalTheory.LFun.IsHecke D.host.F D.host.E (beta G i j) := by
    have hc := (G.ch.chi_eq (D.R.m - (i : ℕ)) (by omega) (by omega)).1
    have he := hL.eta.1
    refine ⟨hc.1.mul (he.1.pow _), fun x => ?_⟩
    have e1 := hc.2 x
    have e3 := he.2 x
    show G.ch.chi (D.R.m - (i : ℕ)) _ * (L.eta ^ _) _ = 1
    rw [MonoidHom.pow_apply, e1, e3]
    simp
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  obtain ⟨rα, rβ⟩ := GlobalTheory.T.thetaGrid_alpha_beta_restrict_quadratic_pow_rank hL t i j
  have pα := GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rα
  have pβ := GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ rβ
  exact GlobalTheory.T.exists_adelicWeilRep_unitaryPair_schroedingerModel D B hB _ _ X Y r s r' s' hX hY Mo hMo _ _ hα (isHecke_div hα hβ) pα (resEtaPow_div pα pβ)

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepSquarePairCharactersAlphaQuotientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRep_squarePair_characters_alpha_quotient : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → ∀ (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (X : Spc D.host.F D.host.E (spW₁ G i j).rank) (Y : Spc D.host.F D.host.E ((spW G i j).rank + (spW₁ G i j).rank))
      (r s r' s' : ℕ), X.IsHerm D.sp.cm.sig B r s → Y.IsSkew D.sp.cm.sig B r' s' →
      ∀ Mo : Model D.sp.cm.sig X Y, Mo.IsGood B.ψ →
      ∃ om, Mo.IsWeil B.ψ (alpha G t i j) (alpha G t i j / beta G i j) om := by
  exact @GlobalTheory.FunObj.squareWeil₁
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)

namespace GlobalTheory.AVTower

theorem finrank_torsion {k : Type} [Field k] (A : AbVar k) {N : ℕ} (hN : N ≠ 0)
    {S : Type} [CommRing S] [Algebra k S] [Module.Finite k S] (y : SpAlg k S ⟶ A.X)
    (h : IsPullback y.left (spMap (algebraMap k S)) (mulN A.X N).left η[A.X].left) :
    Module.finrank k S = N ^ (2 * A.dim) := by
  obtain ⟨hi, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny k A (N : ℤ) (by exact_mod_cast hN)
  obtain ⟨-, hfl, -, hrk⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank k A A _ hi
  have hf : IsFinite ((N : ℤ) • 𝟙 A).hom.left := hi.1
  have e : ((N : ℤ) • 𝟙 A).hom = mulN A.X N := by
    rw [zsmul_hom, id_hom, GrpTangent.mulN_eq_pow, zpow_natCast]
  rw [e] at hf hfl hrk
  have h2 := Scheme.Hom.finrank_of_isPullback _ _ _ _ h (⊥ : PrimeSpectrum k)
  rw [hrk, hd, Int.natAbs_natCast] at h2
  rw [← h2, spMap, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem exists_tower (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] (A : AbVar k) :
    ∃ G : PDivGroup p k, G.height = 2 * A.dim ∧ Nonempty (G.TorsionTower A.X) := by
  have := A.ab.comm
  have hN : ∀ n : ℕ, 1 ≤ p ^ n := fun n => Nat.one_le_pow _ _ hp.out.pos
  choose R _ _ y h1 h2 H using fun n : ℕ => AbelianPDiv.exists_isPullback (A := A.X) A.ab (hN n)
  have h : ∀ n, AbelianPDiv.IsUnivTorsion (p ^ n) (y n) :=
    fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  have hr : ∀ n (q : PrimeSpectrum k), Module.rankAtStalk (R n) q = (p ^ n) ^ (2 * A.dim) := fun n q => by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact finrank_torsion A (pow_ne_zero _ hp.out.ne_zero) (y n) (H n)
  have hex : ∀ n : ℕ, letI := (h n).hopfAlgebra
      letI := (h (n + 1)).hopfAlgebra
      haveI := (h (n + 1)).isCocomm
      ∃ r : R (n + 1) →ₐc[k] R n, Function.Surjective r ∧
        RingHom.ker r = torsionIdeal (R := k) (A := R (n + 1)) (p ^ n) ∧
        DeRham.spOver (r : R (n + 1) →ₐ[k] R n) ≫ y (n + 1) = y n := fun n => by
    let O := k
    let S := R (n + 1)
    let R₀ := R n
    let x := y (n + 1)
    let y₀ := y n
    let N := p ^ n
    have h₀ : AbelianPDiv.IsUnivTorsion N y₀ := h n
    have h' : AbelianPDiv.IsUnivTorsion (p ^ (n + 1)) x := h (n + 1)
    have hy : y₀ ^ (p ^ (n + 1)) = 1 := by rw [pow_succ, pow_mul, h₀.1, one_pow]
    let _ := h₀.hopfAlgebra
    let _ := h'.hopfAlgebra
    have := h'.isCocomm
    let r := h'.lift y₀ hy
    have hr : DeRham.spOver r ≫ x = y₀ := h'.lift_y _ _
    have hc : ∀ {C : Type} [CommRing C] [Algebra O C] (f : R₀ →ₐ[O] C), DeRham.spOver (f.comp r) ≫ x = DeRham.spOver f ≫ y₀ :=
      fun f => h'.comp_lift_y f _ _
    have ht : ∀ {C : Type} [CommRing C] [Algebra O C] (f : S →ₐ[O] C),
        torsionIdeal (R := O) (A := S) N ≤ RingHom.ker f ↔ (DeRham.spOver f ≫ x) ^ N = 1 := fun {C} _ _ f => by
      rw [torsionIdeal_le_ker_iff, ← WithConv.ofConv_toConv f, ← h'.pow_y, WithConv.ofConv_toConv,
        ← h'.counitMap_y (Algebra.ofId O C)]
      exact ⟨fun e => by rw [e]; rfl, fun e => WithConv.ofConv_injective (h'.inj e)⟩
    let π := Ideal.Quotient.mkₐ O (torsionIdeal (R := O) (A := S) N)
    have hπ := (ht π).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    let s := h₀.lift _ hπ
    have hs : s.comp r = π := h'.inj ((hc s).trans (h₀.lift_y _ _))
    have hk : torsionIdeal (R := O) (A := S) N ≤ RingHom.ker r := (ht r).2 (by rw [hr, h₀.1])
    let r' : (S ⧸ torsionIdeal (R := O) (A := S) N) →ₐ[O] R₀ := Ideal.Quotient.liftₐ _ r hk
    have hr' : r'.comp π = r := Ideal.Quotient.liftₐ_comp _ _ _
    have hs' : r'.comp s = AlgHom.id O R₀ := h₀.inj (by
      rw [h₀.comp_lift_y, ← Category.assoc, DeRham.spOver_comp, hr', hr, PDiv.spOver_id, Category.id_comp])
    refine ⟨.ofAlgHom r (h'.inj ?_) (h'.inj ?_), fun b => ?_, le_antisymm (fun a ha => ?_) hk, hr⟩
    · exact (hc _).trans ((h₀.counitMap_y (AlgHom.id O O)).trans (h'.counitMap_y (AlgHom.id O O)).symm)
    · refine (h'.comulMap_y' _ (Algebra.TensorProduct.includeLeft.comp r)
        (Algebra.TensorProduct.includeRight.comp r) (fun a => by simp) (fun a => by simp)).trans ?_
      rw [hc, hc, hc]
      exact (h₀.comulMap_y (AlgHom.id O _)).symm
    · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s b)
      refine ⟨a, (DFunLike.congr_fun hr' a).symm.trans ?_⟩
      exact (congrArg r' ha).trans (DFunLike.congr_fun hs' b)
    · have ha' : r a = 0 := ha
      have : π a = 0 := by rw [← hs, AlgHom.comp_apply, ha', map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
  choose r r1 r2 r3 using hex
  let G : PDivGroup p k :=
    { height := 2 * A.dim
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, rfl, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

theorem height_eq {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] (A : AbVar k) (G : PDivGroup p k)
    (t : G.TorsionTower A.X) : G.height = 2 * A.dim := by
  have P := (TorsionTower.isPullback_y p k G A.X t 1).map (Over.forget _)
  have e : (toUnit (SpAlg k (G.A 1))).left = spMap (algebraMap k (G.A 1)) := by
    simpa using Over.w (toUnit (SpAlg k (G.A 1)))
  simp only [Over.forget_map] at P
  rw [e] at P
  have hf := finrank_torsion A (pow_ne_zero 1 hp.out.ne_zero) (t.y 1) P
  have hr := G.rank_eq 1 ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  change Module.finrank k (G.A 1) = _ at hr
  rw [hf, pow_one, Nat.one_mul] at hr
  exact (Nat.pow_right_injective hp.out.two_le hr).symm

theorem exists_tower_and_height_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k),
    (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧
      ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  intro p _ k _ A
  obtain ⟨G, -, hG⟩ := exists_tower p k A
  exact ⟨⟨G, hG⟩, fun G t => height_eq A G t⟩

end GlobalTheory.AVTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDimStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k), (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧ ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  first | exact @GlobalTheory.AVTower.exists_tower_and_height_eq | exact GlobalTheory.AVTower.exists_tower_and_height_eq | (intros; apply GlobalTheory.AVTower.exists_tower_and_height_eq <;> assumption)
end
end
