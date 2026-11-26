module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWitt
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWitt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.MonoBes

variable {D : D7}

theorem colMul_pX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) = rat (fun k l => d.e k i * d.qX i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, HypDec.pX, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qX i l) * y l * (incA D) (d.e k i) = (incA D) (d.e k i * d.qX i l) * y l
  rw [map_mul]
  ring

theorem colMul_pY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) = rat (fun k l => d.e' k i * d.qY i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jY, HypDec.pY, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qY i l) * y l * (incA D) (d.e' k i) = (incA D) (d.e' k i * d.qY i l) * y l
  rw [map_mul]
  ring

theorem mulVec_eq_sum_colMul {m n : ℕ} (x : Mx D m n) (w : Fin n → AE D) :
    x *ᵥ w = ∑ i, GlobalTheory.FinPl.colMul x i (w i) := by
  funext k
  simp only [mulVec, dotProduct, GlobalTheory.FinPl.colMul, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem mulVec_eq_sum_col {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    x *ᵥ w = ∑ i, fun k => x k i * w i := by
  funext k
  simp only [mulVec, dotProduct, Finset.sum_apply]

theorem rank_one_mulVec {m n k : ℕ} (a : Matrix (Fin m) (Fin k) D.host.E) (b : Matrix (Fin k) (Fin n) D.host.E)
    (i : Fin k) (x : Fin n → D.host.E) : (fun r l => a r i * b i l) *ᵥ x = fun r => a r i * (b *ᵥ x) i := by
  funext r
  simp only [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S)
    (hX : ∀ i, ∀ x ∈ L, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ L)
    (hY : ∀ i, ∀ x ∈ L, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L (L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) v := by
  have h0 : ∀ x ∈ L, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ L := by
    intro x hx
    have e : d.i₀ *ᵥ (d.q0 *ᵥ x) = x - d.e *ᵥ (d.qX *ᵥ x) - d.e' *ᵥ (d.qY *ᵥ x) := by
      have := congrArg (· *ᵥ x) d.sum_eq_one_rat
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      rw [sub_sub, eq_sub_iff_add_eq]
      calc _ = d.e *ᵥ (d.qX *ᵥ x) + d.i₀ *ᵥ (d.q0 *ᵥ x) + d.e' *ᵥ (d.qY *ᵥ x) := by abel
        _ = x := this
    rw [e, mulVec_eq_sum_col d.e, mulVec_eq_sum_col d.e']
    exact L.sub_mem (L.sub_mem hx (L.sum_mem fun i _ => hX i x hx)) (L.sum_mem fun i _ => hY i x hx)
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · rw [colMul_pX]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hX i x hx) hy
    · rw [colMul_pY]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hY i x hx) hy
    · exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.q0 h0 hy
  · rintro ⟨h1, h2, h3⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      have h : d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY = 1 := by
        have h := congrArg rat d.sum_eq_one_rat
        rw [rat_add, rat_add, rat_one] at h
        simpa only [HypDec.jX, HypDec.j0, HypDec.jY,
          HypDec.pX, HypDec.p0, HypDec.pY, rat, Matrix.map_mul] using h
      have := congrArg (· *ᵥ y) h
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      exact this.symm
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (AddSubgroup.sum_mem _ fun i _ => h1 i) ?_) (AddSubgroup.sum_mem _ fun i _ => h2 i)
    exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.i₀ (fun x hx => hx) h3

section SlopeTestRemainingChoices

variable {A B B₀ : HSp D} {c ρ : ℕ}

theorem antiDiagonalEpsilonGram_mulVec_of_rev_ne (ε : D.host.E) (u : Fin c → D.host.E) (j : Fin c) (hj : j.rev ≠ j) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) j = u j.rev := by
  simp only [mulVec, dotProduct, antiDiagonalSignGramMatrix]
  rw [Finset.sum_eq_single j.rev]
  · rw [if_pos (by simp only [Fin.val_rev]; omega), if_neg (Ne.symm hj), one_mul]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro h
    apply hb
    ext
    simp only [Fin.val_rev]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (j : Fin n) (x : D.host.E) (k : Fin m) :
    (M *ᵥ Pi.single j x) k = M k j * x := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem auxiliaryVectors_pairing_eq_antiDiagonal_gram (a : HermitianOrthogonalExtensionData A B c (-1)) (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    (a.aᴴ * B.gram) *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = antiDiagonalSignGramMatrix c (-1) *ᵥ u := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have h := congrArg Matrix.conjTranspose a.perp
    change ((frameMat B A a.ι)ᴴ * B.gram * a.a)ᴴ = 0ᴴ at h
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.conjTranspose_zero,
      Matrix.mul_assoc] using h
  have h2 : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, zero_mulVec, zero_add]

theorem proj_mem (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) (hd : IsAuxiliaryVectorWittDec a d) (Λ : Lat A)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ a.lat Λ 𝔟) ∧
      (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ a.lat Λ 𝔟) := by
  obtain ⟨hc, he, s, he'⟩ := hd
  have hrev : ∀ i : Fin ρ, (Fin.castLE (by omega) i : Fin c).rev ≠ Fin.castLE (by omega) i := by
    intro i h
    have := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.val_castLE] at this
    have := i.2
    omega
  have qX_eq : ∀ x (i : Fin ρ),
      (d.qX *ᵥ x) i = star (s i) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c).rev := by
    intro x i
    rw [HypDec.qX, he', ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have qY_eq : ∀ x (i : Fin ρ),
      (d.qY *ᵥ x) i = star ((-D.host.xi0) ^ (i.1 + 1)) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c) := by
    intro x i
    rw [HypDec.qY, he, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have scal : ∀ i : Fin ρ, star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    intro i
    have h1 : (fun k => d.e k i) =
        frameMat B A a.ι *ᵥ 0 + a.a *ᵥ Pi.single (Fin.castLE (by omega) i : Fin c) ((-D.host.xi0) ^ (i.1 + 1)) := by
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [he, mulVec_zero, zero_add, mulVec_single_apply]
      simp only [colsOf]
      ring
    have h2 : (d.e'ᴴ * B.gram * d.e) i i = (d.qX *ᵥ fun k => d.e k i) i := rfl
    have h3 := congrFun (congrFun d.e'e i) i
    rw [h2, h1, qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, Pi.single_eq_same,
      Matrix.one_apply_eq] at h3
    exact h3
  refine ⟨fun i x hx => ?_, fun i x hx => ?_⟩
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c) (u (Fin.castLE (by omega) i)), fun p => ?_, ?_⟩
    · by_cases hp : p = Fin.castLE (by omega) i
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, mulVec_zero,
        zero_add, mulVec_single_apply, he]
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i) * u (Fin.castLE (by omega) i)) * scal i
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c).rev (u (Fin.castLE (by omega) i : Fin c).rev),
      fun p => ?_, ?_⟩
    · by_cases hp : p = (Fin.castLE (by omega) i : Fin c).rev
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · have hs : s i * star ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
        have := congrArg star (scal i)
        rw [star_mul', star_star, star_one] at this
        exact this
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qY_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (hrev i), mulVec_zero, zero_add, mulVec_single_apply, he']
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i : Fin c).rev * u (Fin.castLE (by omega) i : Fin c).rev) * hs

end SlopeTestRemainingChoices

theorem monoAt_bes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Asc.Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := by
  intro D T L sc G F hF ρ h v
  have hL : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat _ _ h
  obtain ⟨hX, hY⟩ := proj_mem (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h) (hF.hB ρ h) (G.Λ (.core (2 * ρ + 2)))
    (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1))
  rw [← hL] at hX hY
  exact monoAt_of_proj (F.dB ρ h) _ hX hY v

end GlobalTheory.MonoBes

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWittStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_vertex_lattice_splits_along_witt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := by
  first | exact @GlobalTheory.MonoBes.monoAt_bes | exact GlobalTheory.MonoBes.monoAt_bes | (intros; apply GlobalTheory.MonoBes.monoAt_bes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEqThetaLiftDefiniteGroupForm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEqThetaLiftDefiniteGroupForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceLift

theorem exists_traceForm {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup H) (χ : J →* ℂˣ) (z₀ : H) (hfin : Finite (Bridge.stab ι J z₀)) (w : W) :
    ∃ f ∈ Bridge.AdForms ι ρ J χ, (∀ z, (¬ ∃ (γ : Γ) (k : J), z = ι γ * z₀ * k) → f z = 0) ∧
      ∀ L : W →ₗ[ℂ] ℂ, (∀ (γ : Γ) (hγ : z₀⁻¹ * ι γ * z₀ ∈ J), L ((χ ⟨_, hγ⟩ : ℂ) • ρ γ⁻¹ w) = L w) →
        L (f z₀) = (Nat.card (Bridge.stab ι J z₀) : ℂ) * L w := by
  let T : H → Γ → W := fun z γ => if h : z₀⁻¹ * ι γ * z ∈ J then (χ ⟨_, h⟩ : ℂ) • ρ γ⁻¹ w else 0
  have hS : ∀ z, Function.support (T z) ⊆ {γ | z₀⁻¹ * ι γ * z ∈ J} := fun z γ hγ => by
    by_contra h
    exact hγ (dif_neg h)
  have hS0 : {γ | z₀⁻¹ * ι γ * z₀ ∈ J} = (Bridge.stab ι J z₀ : Set Γ) := by
    ext γ
    exact (Bridge.mem_stab _).symm
  have hfin' : (Bridge.stab ι J z₀ : Set Γ).Finite := hfin
  have hF : ∀ z, {γ | z₀⁻¹ * ι γ * z ∈ J}.Finite := fun z => by
    rcases Set.eq_empty_or_nonempty {γ | z₀⁻¹ * ι γ * z ∈ J} with h | ⟨δ, hδ⟩
    · rw [h]; exact Set.finite_empty
    · refine (hfin'.image (· * δ)).subset fun γ hγ => ⟨γ * δ⁻¹, ?_, by simp⟩
      rw [← hS0]
      have := J.mul_mem hγ (J.inv_mem hδ)
      simpa [mul_assoc] using this
  have hT : ∀ z, (Function.support (T z)).Finite := fun z => (hF z).subset (hS z)
  refine ⟨fun z => ∑ᶠ γ, T z γ, fun δ z k => ?_, fun z hz => ?_, fun L hL => ?_⟩
  · have h1 : ∀ γ, T (ι δ * z * k) γ = ((χ k : ℂ) • ρ δ) (T z (γ * δ)) := fun γ => by
      have e : z₀⁻¹ * ι γ * (ι δ * z * k) = z₀⁻¹ * ι (γ * δ) * z * k := by rw [map_mul]; group
      by_cases h : z₀⁻¹ * ι (γ * δ) * z ∈ J
      · have h' : z₀⁻¹ * ι γ * (ι δ * z * k) ∈ J := by rw [e]; exact J.mul_mem h k.2
        have e2 : (⟨_, h'⟩ : J) = ⟨_, h⟩ * k := Subtype.ext e
        have e3 : ρ δ (ρ (γ * δ)⁻¹ w) = ρ γ⁻¹ w := by
          rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, mul_inv_cancel_left]
        simp only [T]
        rw [dite_eq_left h, dite_eq_left h', e2, map_mul, LinearMap.smul_apply, map_smul, e3, smul_smul, Units.val_mul, mul_comm]
      · have h' : z₀⁻¹ * ι γ * (ι δ * z * k) ∉ J := by rw [e, J.mul_mem_cancel_right k.2]; exact h
        simp only [T]
        rw [dif_neg h, dif_neg h', map_zero]
    show ∑ᶠ γ, T (ι δ * z * k) γ = ((χ k : ℂ) • ρ δ) (∑ᶠ γ, T z γ)
    rw [map_finsum _ (hT z), finsum_congr h1]
    exact finsum_comp_equiv (Equiv.mulRight δ) (f := fun γ => ((χ k : ℂ) • ρ δ) (T z γ))
  · refine finsum_eq_zero_of_forall_eq_zero fun γ => dif_neg fun h => hz ⟨γ⁻¹, ⟨_, h⟩, ?_⟩
    rw [map_inv]; group
  · show L (∑ᶠ γ, T z₀ γ) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [finsum_eq_sum_of_support_subset (s := hfin'.toFinset) _ (by rw [Set.Finite.coe_toFinset, ← hS0]; exact hS z₀),
      map_sum, Finset.sum_congr rfl (g := fun _ => L w) fun γ hγ => ?_]
    · rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin']
      rfl
    · have h : z₀⁻¹ * ι γ * z₀ ∈ J := (Bridge.mem_stab _).1 (hfin'.mem_toFinset.1 hγ)
      simp only [T]
      rw [dite_eq_left h, hL]

theorem finite_stab {H Γ I : Type} [Group H] [Group Γ] (ι : Γ →* H) (J : Subgroup H) {y : I → H} (hy : Bridge.IsReps ι J y)
    (hf : ∀ c, Finite (Bridge.stab ι J (y c))) (z : H) : Finite (Bridge.stab ι J z) := by
  obtain ⟨c, ⟨γ, m, e⟩, -⟩ := hy z
  have key : ∀ δ : Bridge.stab ι J z, γ⁻¹ * δ.1 * γ ∈ Bridge.stab ι J (y c) := fun δ => by
    have h1 : z⁻¹ * ι δ.1 * z ∈ J := (Bridge.mem_stab _).1 δ.2
    rw [Bridge.mem_stab]
    have h2 := J.mul_mem (J.mul_mem m.2 h1) (J.inv_mem m.2)
    generalize δ.1 = d at h2
    rw [e] at h2
    simpa [mul_assoc] using h2
  haveI := hf c
  refine Finite.of_injective (fun δ => (⟨_, key δ⟩ : Bridge.stab ι J (y c))) fun a b hab => ?_
  exact Subtype.ext (mul_left_cancel (mul_right_cancel (congrArg Subtype.val hab)))

theorem exists_isReps_through {H Γ I : Type} [Group H] [Group Γ] (ι : Γ →* H) (J : Subgroup H) {y : I → H}
    (hy : Bridge.IsReps ι J y) (z : H) : ∃ (y' : I → H) (c : I), Bridge.IsReps ι J y' ∧ y' c = z := by
  obtain ⟨c, ⟨γ, m, e⟩, -⟩ := hy z
  refine ⟨Function.update y c z, c, fun g => ?_, Function.update_self _ _ _⟩
  have hiff : ∀ j, (∃ (δ : Γ) (k : J), g = ι δ * Function.update y c z j * k) ↔ ∃ (δ : Γ) (k : J), g = ι δ * y j * k := by
    intro j
    by_cases hj : j = c
    · subst hj
      rw [Function.update_self, e]
      constructor
      · rintro ⟨δ, k, h⟩
        exact ⟨δ * γ, m * k, by rw [h, map_mul, Subgroup.coe_mul]; group⟩
      · rintro ⟨δ, k, h⟩
        exact ⟨δ * γ⁻¹, m⁻¹ * k, by rw [h, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group⟩
    · rw [Function.update_of_ne hj]
  simp only [hiff]
  exact hy g

theorem exists_form_sum {H Hf W : Type} [Group H] [Group Hf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (p : H →* Hf)
    (hp : Function.Surjective p) (Γ F R : Subgroup H) (ρ : H →* Module.End ℂ W) (J : Subgroup Hf) (χ : J →* ℂˣ)
    (hdec : ∀ u : H, ∃ k ∈ F, ∃ a ∈ R, u = k * a ∧ p k = p u) (hρ : ∀ k ∈ F, ρ k = 1)
    (Cl : Type) [Fintype Cl] (y : Cl → Hf) (hy : Bridge.IsReps (p.comp Γ.subtype) J y)
    (hfin : ∀ k, Finite (Bridge.stab (p.comp Γ.subtype) J (y k))) (h : H) (w : W) :
    ∃ f ∈ Bridge.AdForms (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ, ∃ r : Cl → H, (∀ k, r k ∈ F) ∧
      Bridge.IsReps (p.comp Γ.subtype) J (fun k => p (r k)) ∧
      ∀ {G' X : Type} [Group G'] (x₀ : X) (om : H × G' →* Module.End ℂ (X → ℂ)) (Λ : W →ₗ[ℂ] (X → ℂ)),
        (∀ γ ∈ Γ, ∀ z v, om (γ, 1) (om z (Λ v)) x₀ = om z (Λ v) x₀) → (∀ a ∈ R, ∀ v, om (a, 1) (Λ v) = Λ (ρ a v)) →
        (∀ k ∈ F, ∀ hk : p k ∈ J, ∀ v, om (k, 1) (Λ v) = ((χ ⟨p k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ v) →
        ∀ g : G', ∑ k, ((J.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p (r k))) : ℕ) : ℂ)⁻¹ *
          om (r k, g) (Λ (f (p (r k)))) x₀ = om (h, g) (Λ w) x₀ := by
  obtain ⟨h₀, hh₀, a, ha, rfl, -⟩ := hdec h
  obtain ⟨y', c₀, hy', e₀⟩ := exists_isReps_through _ _ hy (p h₀)
  have hlift : ∀ z : Hf, ∃ k ∈ F, p k = z := fun z => by
    obtain ⟨u, hu⟩ := hp z
    obtain ⟨k, hk, -, -, -, e⟩ := hdec u
    exact ⟨k, hk, e.trans hu⟩
  choose σ hσ hσ' using hlift
  let r : Cl → H := Function.update (fun k => σ (y' k)) c₀ h₀
  have hr : ∀ k, r k ∈ F ∧ p (r k) = y' k := fun k => by
    by_cases hk : k = c₀
    · subst hk
      simp only [r, Function.update_self]
      exact ⟨hh₀, e₀.symm⟩
    · simp only [r, Function.update_of_ne hk]
      exact ⟨hσ _, hσ' _⟩
  have hr0 : r c₀ = h₀ := Function.update_self _ _ _
  have hyr : (fun k => p (r k)) = y' := funext fun k => (hr k).2
  have hf0 := finite_stab _ _ hy hfin (p h₀)
  obtain ⟨f, hf, hz, hv⟩ := exists_traceForm (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ (p h₀) hf0 (ρ a w)
  refine ⟨f, hf, r, fun k => (hr k).1, by rw [hyr]; exact hy', fun {G' X} _ x₀ om Λ hom hΛa hΛk g => ?_⟩
  rw [Finset.sum_eq_single c₀ ?_ (fun h => absurd (Finset.mem_univ _) h)]
  · let L₀ : W →ₗ[ℂ] ℂ := (LinearMap.proj x₀ : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (om (h₀, g)) ∘ₗ Λ
    have hL₀ : ∀ v, L₀ v = om (h₀, g) (Λ v) x₀ := fun v => rfl
    have key := hv L₀ fun γ hγ => ?_
    · have hN : ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p h₀)) : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.card_pos).ne'
      have e1 : (h₀ * a, g) = ((h₀, g) : H × G') * (a, 1) := by rw [Prod.mk_mul_mk, mul_one]
      rw [hr0, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, ← hL₀, key, inv_mul_cancel_left₀ hN, hL₀, e1,
        map_mul, Module.End.mul_apply, hΛa a ha]
    · generalize ρ a w = v
      obtain ⟨k, hk, b, hb, e, e'⟩ := hdec ((γ : H)⁻¹ * h₀)
      have hκ : h₀⁻¹ * k ∈ F := mul_mem (inv_mem hh₀) hk
      have eκ : p (h₀⁻¹ * k) = ((p h₀)⁻¹ * (p.comp Γ.subtype) γ * p h₀)⁻¹ := by
        show p (h₀⁻¹ * k) = ((p h₀)⁻¹ * p γ * p h₀)⁻¹
        rw [map_mul, e', map_mul, map_inv, map_inv]
        group
      have hκ' : p (h₀⁻¹ * k) ∈ J := by rw [eκ]; exact inv_mem hγ
      have eχ : ((χ ⟨_, hκ'⟩ : ℂˣ) : ℂ)⁻¹ = χ ⟨_, hγ⟩ := by
        rw [show (⟨_, hκ'⟩ : J) = ⟨_, hγ⟩⁻¹ from Subtype.ext eκ, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      have eρ : (ρ.comp Γ.subtype) γ⁻¹ v = ρ b v := by
        have h1 := congrArg ρ e
        rw [map_mul, map_mul, hρ _ hh₀, hρ _ hk, mul_one, one_mul] at h1
        rw [← h1]
        rfl
      have e3 : ((h₀, g) : H × G') * (h₀⁻¹ * k, 1) * (b, 1) = (((γ : H)⁻¹, 1) : H × G') * (h₀, g) := by
        rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_inv_cancel_left, e, mul_one, mul_one, one_mul]
      rw [hL₀, hL₀, map_smul, eρ, ← eχ, ← hΛk _ hκ hκ', ← hΛa b hb, ← Module.End.mul_apply, ← Module.End.mul_apply,
        ← map_mul, ← map_mul, e3, map_mul]
      exact hom _ (inv_mem γ.2) _ _
  · intro k _ hk
    rw [hz _ ?_, map_zero, map_zero]
    · simp
    · intro hex
      obtain ⟨j, -, hu⟩ := hy' (y' k)
      refine hk ((hu k ⟨1, 1, by simp⟩).trans (hu c₀ ?_).symm)
      show ∃ (γ : Γ) (m : J), y' k = (p.comp Γ.subtype) γ * y' c₀ * m
      rw [e₀, ← (hr k).2]
      exact hex


set_option maxHeartbeats 1000000 in
theorem exists_thF_eq_thetaKO : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (h : GA D (Vc D i)) (w : (R.cV i).W), ∃ x : (R.HV i t).H, ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t x (fun ρ => u ρ) g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hlev hmod hth i t h w
  refine (hth.thF i t).elim fun thP hPF => ?_
  refine (exists_form_sum (finHom (Vc D i)).rangeRestrict (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i))
    (GfC (Vc D i)) (GinfC (Vc D i)) (R.cV i).ρ (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ
    (GlobalTheory.LiftUnfold.exists_fin_mul_real (Vc D i)) (hmod.cV i).1 _ (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (fun c => Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv) h w).elim fun f hf0 => hf0.2.elim fun r hr => ?_
  have hf : f ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ := hf0.1
  refine (LinearMap.mem_range.1 ((hmod.HV i t).2.1.ge hf)).elim fun x hx => ⟨x, fun u g => ?_⟩
  have hlaw : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ (levEnv _ (R.βV i) (R.datVt i t)).J,
      R.ωP i t (k, 1) (R.vP i t) =
        (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.vP i t := by
    intro k hkf hk
    have hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
        (Formalism.IndefR.Lev.flag1L (R.datVt i t)) := hk
    have hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k := ⟨hkf, hl.1, Subgroup.mem_bot.1 hl.2⟩
    have hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
      ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
    refine (GlobalTheory.VecInv.omega_lifts_vP R hlev hmod.inf hth.ωP hth.vP i t 1 k 1 hκ hκ').trans ?_
    exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t)
      (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ (levEnv _ (R.βV i) (R.datVt i t)).J, ∀ P,
      R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hmod.inf
      (hth.ωP i t) _ _ _ _ _ (hth.pt_theta i t) k hk 1 (one_mem _) _ (hlaw k hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hth.ωP i t) (D.sp.V_sig _) (hmod.vpos i) (R.cV i) (hmod.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hf
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hth.pt_theta i t _)
    (fun a ha w => (hth.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hmod.νV i t) _ _ r le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hr.2.1 hr.1 g
  have key2 := hr.2.2 (0 : WO (Vc D i) (Wc D i)) (R.ωP i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u))
    (fun γ hγ z v => (hth.ωP i t).om_aut γ hγ 1 (one_mem _) _ ((hth.ωP i t).om_pres _ _ (hth.pt_theta i t _)))
    (fun a ha w => (hth.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _) g
  have h1 := congrFun (hPF.2 x u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans key2)))
  rw [← hx]
  rfl

end GlobalTheory.TraceLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEqThetaLiftDefiniteGroupFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_eq_thetaLift_definiteGroup_form : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (h : GA D (Vc D i)) (w : (R.cV i).W), ∃ x : (R.HV i t).H, ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t x (fun ρ => u ρ) g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := by
  first | exact @GlobalTheory.TraceLift.exists_thF_eq_thetaKO | exact GlobalTheory.TraceLift.exists_thF_eq_thetaKO | (intros; apply GlobalTheory.TraceLift.exists_thF_eq_thetaKO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighest
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighest
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RenamedMinors

variable {D : D7} {S T : HSp D}

def phi (C : Ctx S T) : MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
  C.toH.comp (MvPolynomial.rename fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2))

theorem phi_varF_pos (C : Ctx S T) (τ : D.what₂.Tau) (b a : ℕ) (hb : b < C.X.p0) (ha : a < S.rank) :
    phi C (varF τ b a) = MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) *
      MvPolynomial.X (C.m.e τ, Sum.inr ⟨b, hb⟩, ⟨a, ha⟩) := by
  have hr := C.hr
  have hbm : b < T.rank := by omega
  rw [varF, dite_eq_left ⟨hbm, ha⟩, phi, AlgHom.comp_apply, MvPolynomial.rename_X, Ctx.toH, MvPolynomial.aeval_X]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [rowIdx_inr]
  simp only [revPos]
  rw [dite_eq_left ⟨hb, by omega⟩]

theorem phi_varF_neg (C : Ctx S T) (τ : D.what₂.Tau) (b a : ℕ) (hb : b < C.q0) (ha : a < S.rank) :
    phi C (varF τ (C.X.p0 + b) a) = MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) *
      MvPolynomial.X (C.m.e τ, Sum.inl ⟨b, hb⟩, ⟨a, ha⟩) := by
  have hr := C.hr
  have hbm : C.X.p0 + b < T.rank := by omega
  rw [varF, dite_eq_left ⟨hbm, ha⟩, phi, AlgHom.comp_apply, MvPolynomial.rename_X, Ctx.toH, MvPolynomial.aeval_X]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [rowIdx_inl]
  simp only [revPos]
  rw [dite_eq_right (by simp)]

theorem phi_minorPlus (C : Ctx S T) (hle : C.X.p0 ≤ S.rank) (τ : D.what₂.Tau) (i : Fin C.X.p0) :
    phi C (minorPlus τ (i.val + 1)) = MvPolynomial.C ((((2 / fockScale D τ : ℝ) : ℂ)) ^ (i.val + 1)) *
      Harm.yMinor (C.m.e τ) i (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) := by
  rw [minorPlus, AlgHom.map_det, Harm.yMinor]
  have h : (phi C).mapMatrix (Matrix.of fun α β : Fin (i.val + 1) =>
      (varF τ β α : MvPolynomial (FVar D T.rank S.rank) ℂ)) =
      (MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) : Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) • (Matrix.of fun a b : Fin (i.val + 1) =>
        (Harm.yForm (C.m.e τ) (Harm.lead i a)
          ((fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) (Harm.lead i b)) :
            Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)))ᵀ := by
    ext α β
    have hβ : (β : ℕ) < C.X.p0 := by have := β.2; have := i.2; omega
    have hα : (α : ℕ) < S.rank := by have := α.2; have := i.2; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul]
    rw [phi_varF_pos C τ β α hβ hα, Harm.yForm_single]
    rfl
  rw [h, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, ← map_pow]

theorem phi_minorMinus (C : Ctx S T) (hn : T.rank ≤ S.rank) (τ : D.what₂.Tau) (i : Fin C.q0) : ∃ κ : ℂ,
    phi C (minorMinus τ C.X.p0 (i.val + 1)) = MvPolynomial.C κ *
      Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
        have := C.hr; have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) := by
  have hr := C.hr
  have hi := i.2
  rw [minorMinus, AlgHom.map_det, Harm.xMinor]
  have h : (phi C).mapMatrix (Matrix.of fun α β : Fin (i.val + 1) =>
      (varF τ (C.X.p0 + β) (S.rank - (i.val + 1) + α) : MvPolynomial (FVar D T.rank S.rank) ℂ)) =
      ((MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) : Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) • (Matrix.of fun a b : Fin (i.val + 1) =>
        (Harm.xForm (C.m.e τ) (Harm.lead i a)
          ((fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) (Harm.lead i b)) :
            Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)))ᵀ).submatrix Fin.revPerm id := by
    ext α β : 1
    have hβ : (β : ℕ) < C.q0 := by have := β.2; omega
    have hα : S.rank - (i.val + 1) + (α : ℕ) < S.rank := by have := α.2; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul, Matrix.submatrix_apply, id]
    rw [phi_varF_neg C τ β _ hβ hα, Harm.xForm_single]
    have := α.2
    congr 1
    exact congrArg _ (Prod.ext rfl (Prod.ext rfl (Fin.ext (by
      simp only [Harm.lead, Fin.coe_castLE, Fin.revPerm_apply, Fin.val_rev]
      omega))))
  refine ⟨((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i.val + 1))) : ℤ) : ℂ) *
    (((2 / fockScale D τ : ℝ) : ℂ)) ^ (i.val + 1), ?_⟩
  rw [h, Matrix.det_permute, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  simp only [map_mul, map_pow, map_intCast]
  ring

theorem prod_range_pow_eq {σ : Type} (N : ℕ) (g : ℕ → MvPolynomial σ ℂ) (h : Fin N → MvPolynomial σ ℂ) (d : ℕ → ℕ)
    (hg : ∀ i : Fin N, ∃ κ : ℂ, g i = MvPolynomial.C κ * h i) :
    ∃ κ : ℂ, ∏ i ∈ Finset.range N, g i ^ d i = MvPolynomial.C κ * ∏ i : Fin N, h i ^ d i := by
  choose κ hκ using hg
  refine ⟨∏ i : Fin N, κ i ^ d i, ?_⟩
  rw [← Fin.prod_univ_eq_prod_range (fun i => g i ^ d i), map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hκ i, mul_pow, map_pow]

theorem phi_delta (C : Ctx S T) (hn : T.rank ≤ S.rank) (ap am : D.what₂.Tau → ℕ → ℕ) : ∃ κ : ℂ,
    phi C (delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am) =
      MvPolynomial.C κ * Harm.minorProd
        (fun σ (i : Fin C.q0) => am (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.q0 then am (C.m.e.symm σ) (i + 1) else 0)
        (fun σ (i : Fin C.X.p0) => ap (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.X.p0 then ap (C.m.e.symm σ) (i + 1) else 0)
        (fun _ (a : Fin C.q0) => (Pi.single (⟨S.rank - 1 - a, by
          have := C.hr; have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ))
        (fun _ (b : Fin C.X.p0) => (Pi.single (Fin.castLE (by have := C.hr; omega) b) (1 : ℂ) : Fin S.rank → ℂ)) := by
  have hr := C.hr
  have hle : C.X.p0 ≤ S.rank := by omega
  have hτ : ∀ τ : D.what₂.Tau, ∃ κ : ℂ, phi C (deltaAt (m := T.rank) (n := S.rank) τ C.X.p0 (ap τ) C.q0 (am τ)) =
      MvPolynomial.C κ *
        ((∏ i : Fin C.q0, Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) ^
            (am τ i - if (i : ℕ) + 1 < C.q0 then am τ (i + 1) else 0)) *
          ∏ i : Fin C.X.p0, Harm.yMinor (C.m.e τ) i
            (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) ^
            (ap τ i - if (i : ℕ) + 1 < C.X.p0 then ap τ (i + 1) else 0)) := by
    intro τ
    rw [deltaAt, map_mul, map_prod, map_prod]
    simp only [map_pow]
    obtain ⟨κ1, h1⟩ := prod_range_pow_eq C.X.p0 (fun i => phi C (minorPlus τ (i + 1)))
      (fun i : Fin C.X.p0 => Harm.yMinor (C.m.e τ) i
        (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)))
      (fun i => ap τ i - if i + 1 < C.X.p0 then ap τ (i + 1) else 0)
      (fun i => ⟨_, phi_minorPlus C hle τ i⟩)
    obtain ⟨κ2, h2⟩ := prod_range_pow_eq C.q0 (fun i => phi C (minorMinus τ C.X.p0 (i + 1)))
      (fun i : Fin C.q0 => Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)))
      (fun i => am τ i - if i + 1 < C.q0 then am τ (i + 1) else 0)
      (fun i => phi_minorMinus C hn τ i)
    refine ⟨κ1 * κ2, ?_⟩
    rw [h1, h2, map_mul]
    ring
  choose κ hκ using hτ
  refine ⟨∏ τ, κ τ, ?_⟩
  rw [delta, map_prod, Finset.prod_congr rfl (fun τ _ => hκ τ), Finset.prod_mul_distrib, ← map_prod, Harm.minorProd]
  congr 1
  exact Fintype.prod_equiv C.m.e _ _ (fun τ => by simp only [Equiv.symm_apply_apply])

end GlobalTheory.RenamedMinors


open GlobalTheory.RenamedMinors in
theorem GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (ap am : D.what₂.Tau → ℕ → ℕ), ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ∈ Harm.rowHighest ℂ c c' ∧ C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ≠ 0 := by
  intro D S T C hn ap am
  have hr := C.hr
  obtain ⟨κ, hκ⟩ := phi_delta C hn ap am
  refine ⟨fun σ (i : Fin C.q0) => am (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.q0 then am (C.m.e.symm σ) (i + 1) else 0,
    fun σ (i : Fin C.X.p0) => ap (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.X.p0 then ap (C.m.e.symm σ) (i + 1) else 0,
    ?_, ?_⟩
  · change phi C _ ∈ _
    rw [hκ, ← MvPolynomial.smul_eq_C_mul]
    refine Submodule.smul_mem _ κ (Harm.minorProd_mem_rowHighest _ _ fun t a b => ?_)
    rw [single_dotProduct, one_mul, Pi.single_apply, if_neg]
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.coe_castLE] at h'
    have := a.2
    have := b.2
    omega
  · change phi C _ ≠ 0
    have hf : Function.Injective fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2) :=
      Function.LeftInverse.injective (g := fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2))
        fun v => by simp only [revPos_revPos]
    have hinj : Function.Injective (phi C) := C.toH_bijective.1.comp (MvPolynomial.rename_injective _ hf)
    exact (map_ne_zero_iff (phi C) hinj).2 (GlobalTheory.FockDelta.delta_ne_zero _ _ _ _ (fun _ => by omega) hn)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighestStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedMinorProduct_mem_harmonicRowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (ap am : D.what₂.Tau → ℕ → ℕ), ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ∈ Harm.rowHighest ℂ c c' ∧ C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ≠ 0 := by
  first | exact @GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest | exact GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest | (intros; apply GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest <;> assumption)
end
end
