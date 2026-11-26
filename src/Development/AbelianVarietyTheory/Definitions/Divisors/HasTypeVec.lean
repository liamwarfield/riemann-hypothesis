module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedIntegralMatricesTwoSidedMu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)

noncomputable section

namespace GlobalTheory.TrMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def finFn (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : GfC V → ℂ :=
  fun g => ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v (g : GA D V))

def IsFinMeas (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ν : Measure (GfC V)) : Prop :=
  ν.IsHaarMeasure ∧ ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∫ g, finFn V ff g ∂ν = ∏ᶠ v, ∫ x, ff v x ∂μf v

def HasTypeVec {V : HSp D} (T : TypeDataG V) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Prop :=
  ∃ x : W, x ≠ 0 ∧ (∀ v ∉ T.S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x) ∧
    ∀ v : T.S, x ∈ Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ}

def SphRest {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : Prop :=
  ∀ v ∉ T.S, v ≠ U.u → ∀ k ∈ Kv V v, ∀ k' ∈ Kv V v, ∀ g, ff v (k * g * k') = ff v g

def IsIrrFam {V : HSp D} {n : ℕ} {W : Fin n → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GfC V) (W i)) : Prop :=
  (∀ i, (σ i).IsIrreducible) ∧ (∀ i, IsAdmissible (σ i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))

def SpecFin : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
      mCuspDS μ σ M < Cardinal.aleph0) ∧
    ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) →
      ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
        (σs : ∀ i, Representation ℂ (GfC V) (Ws i)), IsIrrFam σs ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
          mCuspDS μ σ M ≠ 0 → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i))

def SpecTrace : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs →
      (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
        mCuspDS μ σ M ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ i, Nonempty (σ.Equiv (σs i))) →
      ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) →
        HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) (∑ i, ((mCuspDS μ (σs i) M).toNat : ℂ) * c i)

def Separation : Prop :=
  ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S →
    ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs → ∀ a : Fin n → ℂ,
      (∀ ff, IsTestFin T U μf ff → SphRest T U ff →
        ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) → ∑ i, a i * c i = 0) →
      ∀ i, HasTypeVec T (σs i) → a i = 0

end GlobalTheory.TrMult

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X} {ρ : k →+* K}

def bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : CxPts p (τ.comp ρ) := CxPts.bcMap w τ z

theorem bcPt_val (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : (bcPt w τ z).1 = z.1 ≫ j := rfl

theorem continuous_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) : Continuous (bcPt w τ) :=
  CxPts.continuous_of_comp (bcPt_val w τ)

theorem cInfAt_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) {f : CxPts p (τ.comp ρ) → ℝ} {z : CxPts q τ}
    (h : CInfAt f (bcPt w τ z)) : CInfAt (fun y => f (bcPt w τ y)) z := by
  have hm : ∀ y, (bcPt w τ y).1 = y.1 ≫ j := bcPt_val w τ
  unfold CInfAt at h ⊢
  obtain ⟨W, ι, hι, g, F, O, hW, hO, hmem, hF, he⟩ := h
  refine ⟨j ⁻¹ᵁ W, ι, hι, fun a => j.app W (g a), F, O, (CxPts.mem_ptsIn_preimage hm).2 hW, hO, ?_, hF, ?_⟩
  · simpa only [CxPts.ev_of_comp hm] using hmem
  · filter_upwards [(continuous_bcPt w τ).continuousAt.tendsto.eventually he] with y hy
    simpa only [CxPts.ev_of_comp hm] using hy

def MLine.bc (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) : MLine q τ where
  B := A.B.pull j
  φ := A.φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => bcPt w τ) fun _ _ => rfl
  cInf i z hz := (cInfAt_bcPt w τ (A.cInf _ _ (mem_of_mem_linComb (m := fun _ => bcPt w τ z)
    (fun _ => rfl) hz PUnit.unit))).congr (.of_forall fun y => by simp [Weight.linComb])

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.GLFin

section Abstract

variable {Γ K : Type*} [Group Γ] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

end Abstract

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def word (l : List (Lie E a)) : Module.End ℂ (Sm E a) := (l.map (lie E a)).prod

variable (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]

variable {μ} {H : Submodule ℂ (L2 (latticeGL E a) μ)}







end GlobalTheory.GLFin

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGridModel

variable {D : D7}

def IsSum (A B : LSp D) (c : ℕ) (ε : D.host.E) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Prop :=
  ∃ d : HermitianOrthogonalExtensionData A.sp B.sp c ε, B.lat = d.lat A.lat 𝔟

theorem exists_sum (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) (c : ℕ) (neg : Bool)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h0 : ∀ p, 𝔟 p ≠ 0)
    (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) {ν' q' : ℕ} (h1 : ν + c = ν')
    (h2 : q + (if neg then (c + 1) / 2 else c / 2) = q') :
    ∃ Y : LSp D, Y.IsV ν' q' ∧ IsSum X Y c (if neg then -1 else 1) 𝔟 := by
  obtain ⟨B, ⟨d⟩, hB, hs⟩ := GlobalTheory.SignatureAddition.exists_hermitian_space_add_signature D X.sp (ν - q) q c neg hX.sigOK hX.sig
  refine ⟨⟨B, d.lat X.lat 𝔟⟩, ⟨?_, hB, fun τ => ?_, ?_⟩, d, rfl⟩
  · have := d.rank
    rw [hX.rank] at this
    exact this.symm.trans h1
  · rw [hs τ]
    cases neg <;> simp only [Bool.false_eq_true, if_true, if_false, Prod.mk.injEq] at h2 ⊢ <;> omega
  · exact GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D X.sp B c _ d X.lat 𝔟 (by cases neg <;> simp) hX.sd h0 hd

theorem exists_line (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) :
    ∃ Y : LSp D, Y.IsV (ν + 1) q ∧ IsSum X Y 1 1 fun _ => 1 := by
  refine exists_sum X hX hq 1 false (fun _ => 1) (fun _ => one_ne_zero) (fun _ x => ?_) rfl rfl
  rw [inv_one, FractionalIdeal.mem_one_iff, FractionalIdeal.mem_one_iff]
  have key : ∀ y : D.host.E, (∃ a : 𝓞 D.host.E, algebraMap _ _ a = y) → ∃ a : 𝓞 D.host.E, algebraMap _ _ a = star y := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨_, Examples₂.star_isIntegral _ a.2⟩, rfl⟩
  exact ⟨key x, fun h => by simpa using key _ h⟩

theorem exists_stair (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) (c : ℕ)
    {𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (h0 : 𝔞 ≠ 0) (hc : ∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) {ν' q' : ℕ}
    (h1 : ν + c = ν') (h2 : q + (c + 1) / 2 = q') :
    ∃ Y : LSp D, Y.IsV ν' q' ∧ IsSum X Y c (-1) (stairId 𝔞 𝔞' c) :=
  exists_sum X hX hq c true _ (fun p => (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D 𝔞 𝔞' h0 hc c p).1)
    (fun p => (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D 𝔞 𝔞' h0 hc c p).2) h1 h2

theorem nonempty_vertices : ∀ (D : D7) (T : Type) (L : LevCh D T) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E),
    IsSelfDualC (Yc D 0) (L.ΛY 0) → 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → Nonempty (Vertices L 𝔞 𝔞') := by
  intro D T L 𝔞 𝔞' hY h0 hc
  classical
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  obtain ⟨μ, hμ⟩ := D.R.m_even
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : sLen D = (D.R.r + 5) + 1 := rfl
  have hVr : ∀ i j, D.R.m ≤ rankV D i j := fun i j => by unfold rankV; omega
  have hPr : ∀ i, D.R.m ≤ rankP D i := fun i => by unfold rankP nRk; omega
  obtain ⟨hA0, hAc⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1

  have hstd : ∀ ν q : ℕ, ∃ X : LSp D, q ≤ ν → X.IsV ν q := fun ν q => by
    by_cases h : q ≤ ν
    · exact (GlobalTheory.ChiGrid.exists_isV D ν q h).imp fun _ hX _ => hX
    · exact ⟨⟨Yc D 0, L.ΛY 0⟩, fun h' => absurd h' h⟩
  choose S hS using hstd

  have hY0 : (⟨Yc D 0, L.ΛY 0⟩ : LSp D).IsV D.R.r (D.R.m / 2) := by
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, hY⟩
    · exact (D.sp.Y_rank 0 (Nat.zero_le _)).trans (by simp [Ranks.rankY])
    · refine (D.sp.baseSpace_signature_eq τ).trans ?_
      simp only [Ranks.sigY0, Ranks.rS, Prod.mk.injEq]
      omega
  obtain ⟨P₀, hP₀, d0, hd0⟩ := exists_line _ hY0 (by omega)
  let P : ℕ → LSp D := xOf P₀ fun i => S (rankP D i) ((D.R.m - i + 1) / 2)
  have hP : ∀ i, i ≤ D.R.m → (P i).IsV (rankP D i) ((D.R.m - i + 1) / 2) := by
    rintro (_ | i) hi
    · have e1 : rankP D 0 = D.R.r + 1 := by simp [rankP, nRk]
      have e2 : (D.R.m - 0 + 1) / 2 = D.R.m / 2 := by omega
      rw [e1, e2]; exact hP₀
    · exact hS _ _ (by have := hPr (i + 1); omega)

  have hVm : (S (rankV D D.R.m D.R.m) 0).IsV (rankV D D.R.m D.R.m) 0 := hS _ _ (Nat.zero_le _)
  obtain ⟨Xm, hXm, htop⟩ := exists_line _ hVm (Nat.zero_le _)
  let Xs : ℕ → LSp D := fun j => if j = D.R.m then Xm else S (rankX D j) 0
  have hX : ∀ j, (Xs j).IsV (rankX D j) 0 := fun j => by
    by_cases h : j = D.R.m
    · have e1 : rankX D j = rankV D D.R.m D.R.m + 1 := by
        simp only [h, rankX, rankP, rankV, nRk, hs, Nat.add_sub_cancel]; ring
      simp only [Xs, if_pos h]
      rw [e1]; exact hXm
    · simp only [Xs, if_neg h]
      exact hS _ _ (Nat.zero_le _)

  have hcol : ∀ i, ∃ Y : LSp D, 1 ≤ i → i ≤ D.R.m →
      Y.IsV (rankV D i 0) ((D.R.m - 0) / 2) ∧ IsSum (P i) Y (i - 1) (-1) (stairId 𝔞 𝔞' (i - 1)) := fun i => by
    by_cases h : 1 ≤ i ∧ i ≤ D.R.m
    · refine (exists_stair (P i) (hP i h.2) (by have := hPr i; omega) (i - 1) h0 hc ?_ (by omega)).imp fun _ hZ _ _ => hZ
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [rankP, rankV, nRk, hs, Nat.add_sub_cancel]; ring
    · exact ⟨P₀, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose C hC using hcol

  have hrow : ∀ j, ∃ Y : LSp D, j < D.R.m →
      Y.IsV (rankV D D.R.m j) ((D.R.m - j) / 2) ∧
        IsSum (Xs j) Y (D.R.m - 1 - j) (-1) (stairId D.host.AA D.host.AAbar (D.R.m - 1 - j)) := fun j => by
    by_cases h : j < D.R.m
    · refine (exists_stair (Xs j) (hX j) (Nat.zero_le _) (D.R.m - 1 - j) hA0 hAc ?_ (by omega)).imp fun _ hZ _ => hZ
      simp only [rankX, rankP, rankV, nRk, hs, Nat.add_sub_cancel, mul_add, mul_one]; omega
    · exact ⟨P₀, fun h1 => absurd h1 h⟩
  choose R hR using hrow
  let Vs : ℕ → ℕ → LSp D := fun i j =>
    if j = 0 then C i else if i = D.R.m ∧ j < D.R.m then R j else S (rankV D i j) ((D.R.m - j) / 2)
  have hv : ∀ i j, 1 ≤ i → vtxOf L Vs i j = Vs i j := by
    rintro (_ | i) j hi
    · omega
    · rfl
  have hx : ∀ X₀ j, 1 ≤ j → xOf X₀ Xs j = Xs j := by
    rintro X₀ (_ | j) hj
    · omega
    · rfl
  have hV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → (Vs i j).IsV (rankV D i j) ((D.R.m - j) / 2) := by
    intro i j h1 h2 h3
    simp only [Vs]
    split_ifs with ha hb
    · subst ha; exact (hC i h1 h2).1
    · rw [hb.1]; exact (hR j hb.2).1
    · exact hS _ _ (by have := hVr i j; omega)
  have h1 : ∀ i, 1 ≤ i → i ≤ D.R.m → IsSum (P i) (vtxOf L Vs i 0) (i - 1) (-1) (stairId 𝔞 𝔞' (i - 1)) := by
    intro i h h'
    rw [hv i 0 h]
    exact (hC i h h').2
  have h2 : ∀ j, j + 1 < D.R.m → IsSum (Xs (j + 1)) (vtxOf L Vs D.R.m (j + 1)) (D.R.m - 1 - (j + 1)) (-1)
      (stairId D.host.AA D.host.AAbar (D.R.m - 1 - (j + 1))) := by
    intro j h
    have e : Vs D.R.m (j + 1) = R (j + 1) := by
      simp only [Vs]
      rw [if_neg (Nat.succ_ne_zero j), if_pos ⟨trivial, h⟩]
    rw [hv _ _ (by omega), e]
    exact (hR _ h).2
  have h3 : IsSum (vtxOf L Vs D.R.m D.R.m) (xOf (P D.R.m) Xs D.R.m) 1 1 fun _ => 1 := by
    have e : Vs D.R.m D.R.m = S (rankV D D.R.m D.R.m) 0 := by
      simp only [Vs]
      rw [if_neg (by omega), if_neg (by omega), Nat.sub_self]
    have e' : Xs D.R.m = Xm := if_pos rfl
    rw [hv _ _ (by omega), hx _ _ (by omega), e, e']
    exact htop
  choose d1 hd1 using h1
  choose d2 hd2 using h2
  obtain ⟨d3, hd3⟩ := h3
  exact ⟨⟨Vs, P, Xs, hV, hP, fun j _ _ => hX j, d0, hd0, d1, hd1, d2, hd2, d3, hd3⟩⟩

theorem exists_gridData {T : Type} (L : LevCh D T) (sc : Consts) (P : Places L) (h0 : P.v0 ∉ S1 D)
    (hY : IsSelfDualC (Yc D 0) (L.ΛY 0)) : ∃ G : GridData L sc, G.pl = P := by
  obtain ⟨X⟩ := GlobalTheory.GridChars.nonempty_chars D T L P sc.cGap h0
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc
  obtain ⟨V⟩ := nonempty_vertices D T L _ _ hY h1 h2
  exact ⟨⟨P, X, V⟩, rfl⟩

theorem nonempty_gridData_iff {T : Type} (L : LevCh D T) (μ0 : T) (hL : L.Is μ0) (sc : Consts) :
    Nonempty (GridData L sc) ↔ ∃ P : Places L, P.v0 ∉ S1 D := by
  refine ⟨fun ⟨G⟩ => ⟨G.pl, G.ch.basePlace_not_mem_chiGridBadPlaces⟩, fun ⟨P, h⟩ => ?_⟩
  obtain ⟨G, -⟩ := exists_gridData L sc P h (GlobalTheory.ChiGrid.colY_isV D T L μ0 hL 0 (Nat.zero_le _)).sd
  exact ⟨G⟩

theorem nonempty_gridData {T : Type} (L : LevCh D T) (μ0 : T) (hL : L.Is μ0) (sc : Consts)
    (hg : ∀ k, D.host.g k % LevelStarExponents.condE D = 1) (h1 : D.host.pde % LevelStarExponents.condE D = 1) (h2 : D.host.pde' % LevelStarExponents.condE D = 1)
    (h3 : ∀ k, q0 D ≠ D.host.g k) (h4 : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) :
    Nonempty (GridData L sc) :=
  (nonempty_gridData_iff L μ0 hL sc).2 (GlobalTheory.GridPlaces.exists_places D T L μ0 hL hg h1 h2 h3 h4)


end GlobalTheory.ChiGridModel
end
