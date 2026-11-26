module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocBesChar
open GlobalTheory.LocFrame (hA hQ besselAuxiliaryVectors IsHermitianAuxiliaryVectorSystem ent colN)
open Finset (range)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem psiE_ι {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (y : k) :
    psiE ψ (p.ι y) = ψk (y / p.xi) := by
  rw [h]
  congr 1
  have : p.ι y = p.ι (p.π (incA D D.host.xi0 * p.ι (y / p.xi))) := by
    rw [RingHom.map_mul, p.π_ι]
    change _ = p.ι (p.xi * _)
    rw [mul_div_cancel₀ _ (Witness.xi_ne p)]
  rw [this, p.ι_π, mul_left_comm, Witness.e_ι]

theorem psiE_cA (ψ : AddChar (AF D.host.F) ℂ) (x : AE D) : psiE ψ (cA D x) = psiE ψ x := by
  rw [psiE, psiE, GlobalTheory.DualPairCheck.trace_cA]

theorem psiE_supp {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) {u : AE D}
    (hu : (p.e + cA D p.e) * u = u) : psiE ψ u = ψk ((p.π u + p.π (cA D u)) / p.xi) := by
  have e : u = p.ι (p.π u) + cA D (p.ι (p.π (cA D u))) := by
    rw [p.ι_π, p.ι_π, RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA, ← add_mul, hu]
  conv_lhs => rw [e]
  rw [psiE_add, psiE_cA, psiE_ι p h, psiE_ι p h, add_div, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem hA_supp {V : HSp D} {e : AE D} {g : GA D V} (hg : SuppAt e V g) {x y : Fin V.rank → D.host.E} (h : hQ V x y = 0) :
    (e + cA D e) * hA V g x y = hA V g x y := by
  have e1 : hA V g x y = (ratV (star y) ᵥ* gA V) ⬝ᵥ (mt V g - 1) *ᵥ ratV x := by
    rw [← dotProduct_mulVec, mulVec_mulVec, mul_sub, sub_mulVec, dotProduct_sub, ← mt_one V, ← hA, ← hA,
      ← GlobalTheory.LocFrame.incA_hQ, h, map_zero, sub_zero]
  rw [e1]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hg i j
  linear_combination ((ratV (star y) ᵥ* gA V) i * ratV x j) * this

theorem π_hA (V : HSp D) (g : GA D V) (x y : Fin V.rank → D.host.E) :
    p.π (hA V g x y) = (Witness.prH p ∘ (star y ᵥ* V.gram)) ⬝ᵥ (mt V g).map p.π *ᵥ (Witness.prH p ∘ x) := by
  have h1 : ratV (star y) ᵥ* gA V = ratV (star y ᵥ* V.gram) := funext fun i => (RingHom.map_vecMul (incA D) _ _ i).symm
  rw [hA, ← mulVec_mulVec, dotProduct_mulVec, h1, GlobalTheory.LocFrame.map_dot]
  rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem map_mt_inv {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) {g : GA D V} {q : GL Y k}
    (h : (mt V g).map p.π = F.β * q.val * F.γ) : (mt V g⁻¹).map p.π = F.β * (q⁻¹).val * F.γ := by
  have h1 : (mt V g⁻¹).map p.π * (mt V g).map p.π = 1 := by
    rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * q.val * F.γ) * (F.β * (q⁻¹).val * F.γ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc F.β (q⁻¹).val, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  rw [← Matrix.mul_one ((mt V g⁻¹).map p.π), ← h2, ← Matrix.mul_assoc, ← h, h1, Matrix.one_mul]

theorem col_ne_zero {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (j : Y) {t : k} {x : Fin N → k}
    (h : ∀ r, F.β r j = t * x r) : t ≠ 0 := fun e => by
  have h1 := congrFun (congrFun F.γβ j) j
  simp [Matrix.mul_apply, h, e] at h1

section Coef
variable {V X : HSp D} {jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E} {a : ℕ → Fin V.rank → D.host.E}
  {κ : ℕ → D.host.E} {t : ℕ → k} (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) {M : Matrix (Fin X.rank) n k} {F : Frame k V.rank (n ⊕ Fin c)}
  (hl : ∀ r b, F.β r (Sum.inl b) = (jX.map p.pr * M) r b) (hr : ∀ (i : Fin c) r, F.β r (Sum.inr i) = t i * p.pr (a i r))
include H hl hr

theorem π_coef {g : GA D V} {q : GL (n ⊕ Fin c) k} (h : (mt V g).map p.π = F.β * q.val * F.γ) (i j : Fin c) :
    t j * p.π (hA V g (a j) (a (c - 1 - i))) = p.pr (κ i) * t i * q.val (.inr i) (.inr j) := by
  set u := Witness.prH p ∘ (star (a (c - 1 - i)) ᵥ* V.gram) with hu
  have e1 : t j • (Witness.prH p ∘ a j) = F.β *ᵥ Pi.single (.inr j) 1 := by
    rw [mulVec_single_one]
    exact funext fun r => (hr j r).symm
  have e2 (b : n) : (u ᵥ* F.β) (.inl b) = 0 := by
    have : (u ᵥ* (jX.map (Witness.prH p) * M)) b = 0 := by
      rw [← vecMul_vecMul, show u ᵥ* jX.map (Witness.prH p) = 0 from funext fun s => by
        rw [hu, ← RingHom.map_vecMul, H.perp _ (by omega), Pi.zero_apply, map_zero, Pi.zero_apply], zero_vecMul, Pi.zero_apply]
    rw [← this]
    change ∑ r, u r * F.β r (.inl b) = ∑ r, u r * (jX.map p.pr * M) r b
    exact Finset.sum_congr rfl fun r _ => congrArg (u r * ·) (hl r b)
  have e3 (l : Fin c) : (u ᵥ* F.β) (.inr l) = if l = i then p.pr (κ i) * t i else 0 := by
    have h3 : (u ᵥ* F.β) (.inr l) = t l * Witness.prH p (hQ V (a l) (a (c - 1 - i))) := by
      rw [hQ, dotProduct_mulVec, RingHom.map_dotProduct, dotProduct, Finset.mul_sum]
      change ∑ r, u r * F.β r (.inr l) = _
      refine Finset.sum_congr rfl fun r _ => ?_
      change u r * F.β r (.inr l) = t l * (u r * p.pr (a l r))
      rw [hr]; ring
    rw [h3, H.pair i i.2 l l.2]
    by_cases e : l = i
    · subst e; rw [if_pos rfl, if_pos rfl, mul_comm]; rfl
    · rw [if_neg (fun e' => e (Fin.ext e')), if_neg e, map_zero, mul_zero]
  rw [π_hA, h, ← smul_eq_mul, ← dotProduct_smul, ← mulVec_smul, e1, mulVec_mulVec, Matrix.mul_assoc, F.γβ, Matrix.mul_one,
    ← mulVec_mulVec, dotProduct_mulVec, mulVec_single_one, dotProduct, Fintype.sum_sum_type]
  simp [← hu, e2, e3]

theorem π_simple {g : GA D V} {q : GL (n ⊕ Fin c) k} (h : (mt V g).map p.π = F.β * q.val * F.γ) {i : ℕ} (hi : i + 1 < c)
    {x : k} (hx : p.pr (κ i) * t i = x * t (i + 1)) : p.π (hA V g (a (i + 1)) (a (c - 1 - i))) = x * ent q i := by
  have h1 := π_coef p H hl hr h ⟨i, by omega⟩ ⟨i + 1, hi⟩
  have h2 : t (i + 1) ≠ 0 := col_ne_zero F _ (hr ⟨i + 1, hi⟩)
  rw [ent, dite_eq_left hi]
  refine mul_left_cancel₀ h2 (h1.trans ?_)
  simp only [hx]
  ring

end Coef

def scal {ρ : ℕ} (B : BesLev D ρ) (s : k) (i : ℕ) : k :=
  if i < ρ then s * p.xi ^ (ρ - i) else if i = ρ then s else s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - i))

theorem scal_lo {ρ : ℕ} (B : BesLev D ρ) (s : k) {i : ℕ} (hi : i < ρ) :
    p.pr (if i = ρ then hQ B.L B.ζ B.ζ else 1) * scal p B s i = p.xi * scal p B s (i + 1) := by
  rw [if_neg hi.ne, show p.pr 1 = 1 from (Witness.prH p).map_one, scal, scal, if_pos hi]
  split_ifs with h1 h2
  · rw [show ρ - i = ρ - (i + 1) + 1 by omega]; ring
  · rw [show ρ - i = 1 by omega]; ring
  · omega

theorem scal_hi {ρ : ℕ} (B : BesLev D ρ) (s : k) {i : ℕ} (hi : ρ ≤ i) (hi' : i < 2 * ρ) :
    p.pr (if i = ρ then hQ B.L B.ζ B.ζ else 1) * scal p B s i = -p.xi * scal p B s (i + 1) := by
  have hx := Witness.xi_ne p
  rw [scal, scal, if_neg (show ¬ i < ρ by omega), if_neg (show ¬ i + 1 < ρ by omega), if_neg (show ¬ i + 1 = ρ by omega)]
  split_ifs with h1
  · rw [show ρ - 1 - (2 * ρ - (i + 1)) = 0 by omega]
    change p.hz B * s = _
    field_simp
  · rw [show ρ - 1 - (2 * ρ - (i + 1)) = ρ - 1 - (2 * ρ - i) + 1 by omega, show p.pr 1 = 1 from (Witness.prH p).map_one, pow_succ]
    field_simp

theorem col_eq {ρ : ℕ} {B : BesLev D ρ} {s : k} {FA : Frame k B.A.rank n} {FV : Frame k B.V.rank (n ⊕ Fin c)}
    (h : p.IsBesFrame B s FA FV) (i : Fin c) (r) :
    FV.β r (Sum.inr i) = scal p B s i * p.pr (besselAuxiliaryVectors B.d (vecB B.o B.ζ) i r) := by
  obtain ⟨hc, -, h1, h2, h3⟩ := h
  have := i.2
  unfold scal besselAuxiliaryVectors
  split_ifs with e1 e2
  · rw [h1 ⟨i, e1⟩ i rfl r, colN, dite_eq_left e1]
  · exact h2 i e2 r
  · have e3 : 2 * ρ - i < ρ := by omega
    rw [h3 ⟨2 * ρ - i, e3⟩ i (by simp only; omega) r, colN, dite_eq_left e3]

theorem psiBes_isLoc : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → psiBes ψ B.d 1 (vecB B.o B.ζ) g = (ψk (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  intro D k _ _ _ _ p ψ ψk hψ σ B s n _ _ c FA FV hF g q hq hg
  obtain rfl := hF.1
  have H : IsHermitianAuxiliaryVectorSystem (2 * σ + 1) B.V B.A (B.d.i₀ * B.o.iA)
      (besselAuxiliaryVectors B.d (vecB B.o B.ζ)) (fun i => if i = σ then hQ B.L B.ζ B.ζ else 1) := by
    open GlobalTheory.LocFrame in
    exact {
  iso := by
    rw [conjTranspose_mul, Matrix.mul_assoc B.o.iAᴴ, Matrix.mul_assoc B.o.iAᴴ, ← Matrix.mul_assoc _ B.d.i₀, B.d.iso,
      ← Matrix.mul_assoc, B.o.isoA]
  perp := by
    intro i hi
    unfold besselAuxiliaryVectors
    split_ifs with h1 h2
    · rw [colN_eq_mulVec _ h1, ← vecMul_vecMul, perp_of_gram B.d.i₀e, zero_vecMul]
    · rw [vecB, mulVec_mulVec]
      refine perp_of_gram ?_ _
      rw [conjTranspose_mul, Matrix.mul_assoc B.o.iAᴴ, Matrix.mul_assoc B.o.iAᴴ, ← Matrix.mul_assoc _ B.d.i₀, B.d.iso,
        ← Matrix.mul_assoc, B.o.orth']
    · rw [colN_eq_mulVec _ (show 2 * σ - i < σ by omega), ← vecMul_vecMul, perp_of_gram B.d.i₀e', zero_vecMul]
  pair := by
    intro i hi l hl
    unfold besselAuxiliaryVectors
    rcases lt_trichotomy l σ with h | h | h <;> rcases lt_trichotomy i σ with h' | h' | h'
    · rw [if_pos h, if_neg (by omega), if_neg (by omega), hQ_XY B.d h (by omega), if_neg h'.ne]
      exact if_congr (by omega) rfl rfl
    · rw [if_pos h, if_neg (by omega), if_pos (by omega), wittDecomposition_hermitian_e_anisotropicPart B.d h, if_neg (by omega)]
    · rw [if_pos h, if_pos (by omega), hQ_XX B.d h (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega), hQ_0Y B.d (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos (by omega), hQ_vecB B.d B.o, if_pos (by omega), if_pos h']
    · rw [if_neg (by omega), if_pos h, if_pos (by omega), hQ_0X B.d (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hQ_YY B.d (by omega) (by omega),
        if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), wittDecomposition_hermitian_dual_anisotropicPart B.d (by omega),
        if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), hQ_YX B.d (by omega) (by omega), if_neg h'.ne']
      exact if_congr (by omega) rfl rfl
  ne := by
    intro i _
    split_ifs
    exacts [B.line.2, one_ne_zero]
  card := by have := B.d.rank_add; have := B.o.rank_add; have := B.line.1; omega
    }
  have hx := Witness.xi_ne p
  rw [psiBes, map_one, one_mul, GlobalTheory.LocFrame.simpleSum_eq_sum_hA, psiE_supp p hψ, GlobalTheory.LocFrame.simpleSum_eq_sum_ent]
  · congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [div_eq_iff hx, show 2 * σ + 1 - 1 = σ + σ by omega, Finset.sum_range_add, add_mul, map_sum, map_sum, map_sum,
      Finset.sum_mul, ← Finset.sum_range_reflect (fun i => ent q (σ + i)), Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have h1 := π_simple p H hF.2.1 (col_eq p hF) hg.2 (i := i) (by omega) (scal_lo p B s hi')
      rw [show σ + σ - i = 2 * σ + 1 - 1 - i by omega, h1, mul_comm]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have h1 := π_simple p H hF.2.1 (col_eq p hF) (map_mt_inv p FV hg.2) (i := σ + (σ - 1 - i)) (by omega)
        (scal_hi p B s (by omega) (by omega))
      rw [show 2 * σ + 1 - 1 - (σ + (σ - 1 - i)) = i + 1 by omega, show σ + (σ - 1 - i) + 1 = σ + σ - i by omega,
        GlobalTheory.LocFrame.ent_inv hq] at h1
      rw [GlobalTheory.LocFrame.cA_hA, h1]
      ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => hA_supp hg.1 ?_
    have hi' := Finset.mem_range.1 hi
    rw [H.pair i (by omega) _ (by omega), if_neg (by omega)]

end GlobalTheory.LocBesChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselCharacter_localElement_eq_simpleEntrySum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → psiBes ψ B.d 1 (vecB B.o B.ζ) g = (ψk (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  first | exact @GlobalTheory.LocBesChar.psiBes_isLoc | exact GlobalTheory.LocBesChar.psiBes_isLoc | (intros; apply GlobalTheory.LocBesChar.psiBes_isLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousKappa
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

open scoped Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ContractionLocal

section Tens
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']

def colTens (φ : SB (n → k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := ⟨fun x => Ξ.1 x.toCols₁ * φ.1 (fun r => x r (Sum.inr ())), by
    haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n) (n' := n' ⊕ Unit)
    refine GlobalTheory.FinPl.Comm.prod_mem_SB Ξ.2 φ.2 (p := fun x : Matrix n (n' ⊕ Unit) k => x.toCols₁)
      (r := fun x r => x r (Sum.inr ())) (s := fun z => Matrix.fromCols z.1 (Matrix.of fun r _ => z.2 r))
      (by unfold Matrix.toCols₁; fun_prop) (continuous_pi fun r => by fun_prop) ?_ ?_
    · refine continuous_matrix fun i j => ?_
      rcases j with j | j
      · exact continuous_fst.matrix_elem i j
      · exact (continuous_apply i).comp continuous_snd
    · intro x
      ext i (j | j)
      · rfl
      · rfl⟩
  map_add' Ξ Ξ' := by ext x; simp [add_mul]
  map_smul' c Ξ := by ext x; simp [mul_assoc]

@[simp] theorem colTens_apply (φ : SB (n → k)) (Ξ : SB (Matrix n n' k)) (x : Matrix n (n' ⊕ Unit) k) :
    (colTens φ Ξ).1 x = Ξ.1 x.toCols₁ * φ.1 (fun r => x r (Sum.inr ())) := rfl

def rowTens (φ : SB (n → k)) : SB (Matrix n'' n k) →ₗ[ℂ] SB (Matrix (n'' ⊕ Unit) n k) where
  toFun Ξ := ⟨fun x => Ξ.1 x.toRows₁ * φ.1 (x (Sum.inr ())), by
    haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := n'' ⊕ Unit) (n' := n)
    refine GlobalTheory.FinPl.Comm.prod_mem_SB Ξ.2 φ.2 (p := fun x : Matrix (n'' ⊕ Unit) n k => x.toRows₁)
      (r := fun x => x (Sum.inr ())) (s := fun z => Matrix.fromRows z.1 (Matrix.of fun _ => z.2))
      (by unfold Matrix.toRows₁; fun_prop) (continuous_pi fun j => continuous_id.matrix_elem _ j) ?_ ?_
    · refine continuous_matrix fun i j => ?_
      rcases i with i | i
      · exact continuous_fst.matrix_elem i j
      · exact (continuous_apply j).comp continuous_snd
    · intro x
      ext (i | i) j
      · rfl
      · rfl⟩
  map_add' Ξ Ξ' := by ext x; simp [add_mul]
  map_smul' c Ξ := by ext x; simp [mul_assoc]

@[simp] theorem rowTens_apply (φ : SB (n → k)) (Ξ : SB (Matrix n'' n k)) (x : Matrix (n'' ⊕ Unit) n k) :
    (rowTens φ Ξ).1 x = Ξ.1 x.toRows₁ * φ.1 (x (Sum.inr ())) := rfl

end Tens

section Bil
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem continuous_kappa {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') (S : HSp D) : Continuous (l.κ S) := by
  unfold Link.κ GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj
  have h : Continuous fun w : WO S L' => giA S ⬝ (adj (rat l.τ ⬝ w) ⬝ gA B.L) :=
    Continuous.matrix_mul continuous_const (Continuous.matrix_mul
      (GlobalTheory.MixModel.continuous_adj.comp (continuous_const.matrix_mul continuous_id)) continuous_const)
  exact h.const_smul ((incA D) (-D.host.xi0⁻¹))

theorem integrable_contr (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {Ξ₁ : WO B.V₀ S → ℂ} {Ξ₂ : WO S B'.V₀ → ℂ}
    (h₁ : IsThetaFunO ψ B.V₀ S Ξ₁) (h₂ : IsThetaFunO ψ S B'.V₀ Ξ₂) (u : WO B.A S) (v : WO S B'.A) :
    Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)))
      (vL.μ.restrict vL.𝓕) := by
  haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
  haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ h₁
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ h₂
  have hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) :=
    (h₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))).mul
      (h₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp
        (Continuous.prodMk continuous_const (continuous_kappa l S))))
  refine (integrable_const (C₂ * C₁)).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [norm_mul]
  exact mul_le_mul (hC₂ _) (hC₁ _) (norm_nonneg _) ((norm_nonneg _).trans (hC₂ 0))

def contrBil (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (T₁ : M₁ →ₗ[ℂ] (WO B.V₀ S → ℂ)) (T₂ : M₂ →ₗ[ℂ] (WO S B'.V₀ → ℂ))
    (h₁ : ∀ Φ, IsThetaFunO ψ B.V₀ S (T₁ Φ)) (h₂ : ∀ Φ, IsThetaFunO ψ S B'.V₀ (T₂ Φ)) :
    M₁ →ₗ[ℂ] M₂ →ₗ[ℂ] (WO B.A S → WO S B'.A → ℂ) :=
  LinearMap.mk₂ ℂ (fun Ψ₁ Ψ₂ => GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂))
    (fun a a' b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_add (f := _), Pi.add_apply, mul_add]
      exact integral_add (integrable_contr hψ l S vL (h₁ a) (h₂ b) u v)
        (integrable_contr hψ l S vL (h₁ a') (h₂ b) u v))
    (fun c a b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; funext w; ring)
    (fun a b b' => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_add (f := _), Pi.add_apply, add_mul]
      exact integral_add (integrable_contr hψ l S vL (h₁ a) (h₂ b) u v)
        (integrable_contr hψ l S vL (h₁ a) (h₂ b') u v))
    (fun c a b => by
      funext u v
      simp only [GlobalTheory.Unf.contr, map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← integral_const_mul]; congr 1; funext w; ring)

@[simp] theorem contrBil_apply (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ}
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁]
    [AddCommGroup M₂] [Module ℂ M₂] (T₁ : M₁ →ₗ[ℂ] (WO B.V₀ S → ℂ)) (T₂ : M₂ →ₗ[ℂ] (WO S B'.V₀ → ℂ))
    (h₁ : ∀ Φ, IsThetaFunO ψ B.V₀ S (T₁ Φ)) (h₂ : ∀ Φ, IsThetaFunO ψ S B'.V₀ (T₂ Φ)) (Ψ₁ : M₁) (Ψ₂ : M₂) :
    contrBil hψ l S vL T₁ T₂ h₁ h₂ Ψ₁ Ψ₂ = GlobalTheory.Unf.contr l S vL (T₁ Ψ₁) (T₂ Ψ₂) := rfl

end Bil

end GlobalTheory.ContractionLocal

namespace GlobalTheory.ContractionLocal

theorem exists_normPair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψk : AddChar k Circle) (ν : Measure k) (hψ : Continuous ψk)
    (hν : ν.IsAddHaarMeasure) (n : Type) [Fintype n] [DecidableEq n] :
    ∃ φ₀ φ₀' : SB (n → k), ∫ u, φ₀'.1 u * GlobalTheory.StepData.hat ψk ν (-1) φ₀.1 u ∂(Measure.pi fun _ => ν) = 1 := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI := hν
  haveI := GlobalTheory.SplitWeil.secondCountable k
  let L := GlobalTheory.LatPair.stdLat k n
  have hc := GlobalTheory.FinPl.Comm.fpair_ne_zero ψk hψ (-1) (Or.inr rfl) (Measure.pi fun _ => ν) L
  set c := GlobalTheory.FinPl.Comm.fpair ψk (-1) (Measure.pi fun _ => ν) (GlobalTheory.FinPl.vecInd L) (GlobalTheory.FinPl.dualInd L)
  refine ⟨⟨_, GlobalTheory.FinPl.Comm.vecInd_mem L⟩, c⁻¹ • ⟨_, GlobalTheory.FinPl.Comm.dualInd_mem L⟩, ?_⟩
  have e : c = ∫ u, (GlobalTheory.FinPl.dualInd L u) * GlobalTheory.StepData.hat ψk ν (-1) (GlobalTheory.FinPl.vecInd L) u
      ∂(Measure.pi fun _ => ν) := by
    simp only [c, GlobalTheory.FinPl.Comm.fpair, GlobalTheory.StepData.hat]
    congr 1; funext u; ring
  simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [integral_const_mul, ← e, inv_mul_cancel₀ hc]

theorem contr_tens {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψk : AddChar k Circle) (ν : Measure k)
    {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (φ₀ φ₀' : SB (n → k)) (Ξ₁ : SB (Matrix n n' k)) (Ξ₂ : SB (Matrix n'' n k)) (q : Matrix n n' k × Matrix n'' n k) :
    GlobalTheory.LocFlat.contr ψk ν (colTens φ₀ Ξ₁).1 (rowTens φ₀' Ξ₂).1 q =
      Ξ₁.1 q.1 * Ξ₂.1 q.2 * ∫ u, φ₀'.1 u * GlobalTheory.StepData.hat ψk ν (-1) φ₀.1 u ∂(Measure.pi fun _ => ν) := by
  simp only [GlobalTheory.LocFlat.contr, colTens_apply, rowTens_apply, Matrix.toCols₁_fromCols, Matrix.toRows₁_fromRows,
    GlobalTheory.StepData.hat]
  rw [← integral_const_mul]
  congr 1; funext u
  have h1 : (Matrix.fromRows q.2 (Matrix.of fun _ : Unit => u)) (Sum.inr ()) = u := rfl
  have h2 : ∀ y : n → k, (fun r => Matrix.fromCols q.1 (Matrix.of fun r (_ : Unit) => y r) r (Sum.inr ())) = y :=
    fun y => rfl
  simp only [h1, h2]
  rw [show (∫ y, Ξ₁.1 q.1 * φ₀.1 y * ((ψk ((-1) * (u ⬝ᵥ y)) : Circle) : ℂ) ∂(Measure.pi fun _ => ν)) =
      Ξ₁.1 q.1 * ∫ y, φ₀.1 y * ((ψk ((-1) * (u ⬝ᵥ y)) : Circle) : ℂ) ∂(Measure.pi fun _ => ν) by
    rw [← integral_const_mul]; congr 1; funext y; ring]
  ring
end GlobalTheory.ContractionLocal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepWeilExponentsFockVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepWeilExponentsFockVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChainTw.StepExpTw

theorem twStepExpVac : ∀ D : D7, ForStepQ D fun c _ k s s' p => ∀ hk : k < D.R.m,
    IsWeilExp c.ψ s.V s'.V (GlobalTheory.Chain.expS D ⟨k, hk⟩) (GlobalTheory.Chain.expT D ⟨k, hk⟩) p.ω ∧
      GlobalTheory.Chain.IsVacVec c.ψ c.θ s.M s'.M p.f := by
  intro D _ c w hw k _ s s' hs hs' p hp hk
  obtain ⟨hr, _, hsf⟩ := hs
  obtain ⟨hr', _, hsf'⟩ := hs'
  refine ⟨⟨c.chS (k + 1), c.chT (k + 1), hp.weil, fun τ => StepExp.chrStep_exp' hw.com ⟨k, hk⟩ τ⟩, ?_⟩
  obtain ⟨f₀, hv⟩ := hp.vec
  have hrk : s.V.rank ≤ s'.V.rank := by
    have h1 : s.V.rank = D.R.rankY k := hsf.rank
    have h2 : s'.V.rank = D.R.rankY (k + 1) := hsf'.rank
    rw [h1, h2]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right D.R.t (Nat.le_succ k)) D.R.r
  obtain ⟨a, b, d⟩ := StepVac.stepVec_vac hsf.selfDual hsf'.selfDual hrk hv
  exact { theta := a, ne := b, vac := d }

end GlobalTheory.ChainTw.StepExpTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepWeilExponentsFockVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_chain_step_weil_exponents_fock_vacuum : ∀ D : D7, ForStepQ D fun c _ k s s' p => ∀ hk : k < D.R.m, IsWeilExp c.ψ s.V s'.V (GlobalTheory.Chain.expS D ⟨k, hk⟩) (GlobalTheory.Chain.expT D ⟨k, hk⟩) p.ω ∧ GlobalTheory.Chain.IsVacVec c.ψ c.θ s.M s'.M p.f := by
  first | exact @GlobalTheory.ChainTw.StepExpTw.twStepExpVac | exact GlobalTheory.ChainTw.StepExpTw.twStepExpVac | (intros; apply GlobalTheory.ChainTw.StepExpTw.twStepExpVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

noncomputable section

namespace GlobalTheory.FinPl.Rebase

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nsmul_half (p : SplitPt D k) {S T : HSp D} {LS MS : Lat S} {LT MT : Lat T} (hLS : IsSelfDualC S LS)
    (hLT : IsSelfDualC T LT) (hMS : IsSelfDualC S MS) (hMT : IsSelfDualC T MT) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v),
      IsHalf p.e u → N • u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) := by
  obtain ⟨ε, hε, heq⟩ := p.above
  have he := p.split.1
  have hec := p.split.2.1
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hLS
  letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hLT
  obtain ⟨M, hM, hMm⟩ := GlobalTheory.DiagLiftFix.exists_nsmul_latO (ΛS' := LS) (ΛT' := LT)
    hMS.1.fg hMT.1.fg inferInstance inferInstance
  refine ⟨M, hM, fun u hu hh => ?_⟩
  have h1 := (GlobalTheory.PlaceModel.idem_smul_mem hε he heε (hMm u (GlobalTheory.PlaceModel.latO_le_top _ hu))).1
  have h2 : p.e • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh)
  rwa [smul_comm, h2] at h1

theorem isHalf_nsmul {S T : HSp D} {e : AE D} {u : WO S T} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem sbHalf_mono : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S T : HSp D) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → ∀ Φ : WO S T → ℂ, IsSBHalf p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) Φ := by
  intro D k _ _ _ _ p S T LS MS LT MT hLS hLT hMS hMT Φ hΦ
  obtain ⟨N, hN, hNm⟩ := exists_nsmul_half p hMS hMT hLS hLT
  obtain ⟨M, hM, hMm⟩ := exists_nsmul_half p hLS hLT hMS hMT
  obtain ⟨h1, k', hk', h2, h3⟩ := hΦ
  refine ⟨h1, k' * N * M, Nat.mul_pos (Nat.mul_pos hk' hN) hM, fun u hu hh t => ?_, fun t ht => ?_⟩
  · have hu' : M • u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) :=
      nsmul_mem hu M
    have e : (k' * N * M) • u = k' • (N • (M • u)) := by rw [smul_smul, smul_smul, mul_assoc]
    rw [e]
    exact h2 _ (hNm _ hu' (isHalf_nsmul hh M)) (isHalf_nsmul (isHalf_nsmul hh M) N) t
  · have ht' := h1 t ht
    have e : (k' * N * M) • t = M • (N • (k' • t)) := by
      rw [smul_smul, smul_smul, mul_comm M N, mul_comm (N * M) k', mul_assoc]
    rw [e]
    exact hMm _ (nsmul_mem (h3 t ht) N) (isHalf_nsmul (isHalf_nsmul ht' k') N)

theorem placeIdem_mul {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {a : AE D} (ha : a ∈ idAt D (· = v)) :
    algebraMap (AF D.host.F) (AE D) ε * a = a := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  obtain ⟨hi, hw⟩ := GlobalTheory.FinPl.LatMem.mem_idAt_iff.1 ha
  refine GlobalTheory.AdelicU.Supp.adTens_ext (fun w => ?_) fun w => ?_
  · rw [map_mul, GlobalTheory.FinPl.LatMem.compInf_eq_zero hi, mul_zero]
  · rw [map_mul]
    have he : GlobalTheory.AdelicU.compFin D.host.F D.host.E w (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) =
        evalV D.host.F w β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    by_cases hv : w = v
    · subst hv
      rw [he, h1]
      exact one_mul _
    · rw [GlobalTheory.FinPl.LatMem.compFin_eq_compAt a w, hw w hv, mul_zero]

theorem eq_add_halves (p : SplitPt D k) {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {u : WO S T} (hu : u ∈ latO S T LS LT (· = p.v)) : p.e • u + cA D p.e • u = u := by
  obtain ⟨ε, hε, heq⟩ := p.above
  rw [← add_smul, heq]
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact placeIdem_mul hε (GlobalTheory.FinPl.LatMem.latO_mxAt hu i j)

theorem smul_conj_zero (e e' : AE D) (h : e' * cA D e' = 0) {S T : HSp D} (u : WO S T) (hu : e' • u = u) :
    cA D e' • (e • u) = 0 := by
  rw [← hu, smul_smul, smul_smul]
  rw [mul_comm (cA D e') e]
  rw [mul_assoc]
  rw [mul_comm (cA D e') e']
  rw [h, mul_zero, zero_smul]

theorem isHalf_add {S T : HSp D} {e : AE D} {a b : WO S T} (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e (a + b) :=
  fun i j => by rw [Matrix.add_apply, mul_add, ha i j, hb i j]

theorem latVac_image : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 f₀ Tm → IsLatVac (heisO ψ S T) (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)) (Tm (halfInd p.e (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v)))) := by
  intro D k _ _ _ _ p ψ hψ S T LS MS LT MT hLS hLT hMS hMT f₀ Tm hTm
  obtain ⟨ε, hε, heq⟩ := p.above
  have he := p.split.1
  have hec := p.split.2.1
  have hce : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination hce + hec
  set Λ' := latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (· = p.v) with hΛ'
  have hΦ₀ : IsSBHalf p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v))
      (halfInd p.e Λ') :=
    sbHalf_mono D k p S T LS MS LT MT hLS hLT hMS hMT _ (GlobalTheory.isSBHalf_halfInd p.e Λ')
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T MS MT hψ hMS hMT).1
  have hLL' : ∀ x ∈ Λ', IsHalf p.e x → ∀ y ∈ Λ', ψ (symplO S T x y) = 1 := fun x hx hh y hy =>
    (hdual x (GlobalTheory.PlaceModel.infPart_half hε heε ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh))).1
      (GlobalTheory.PlaceModel.latO_le_top _ hx) y (GlobalTheory.PlaceModel.latO_le_top _ hy)
  have hX : ∀ x ∈ Λ', IsHalf p.e x → heisO ψ S T x (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro x hx hh
    rw [← hTm.trans _ hΦ₀ x hh]
    congr 1
    funext t
    have hc : (t + x ∈ Λ' ∧ IsHalf p.e (t + x)) ↔ (t ∈ Λ' ∧ IsHalf p.e t) := by
      rw [Λ'.add_mem_cancel_right hx]
      refine and_congr_right fun _ => forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.add_apply, mul_add, hh i j, add_left_inj]
    show halfInd p.e Λ' (t + x) = halfInd p.e Λ' t
    unfold halfInd
    by_cases h : t ∈ Λ' ∧ IsHalf p.e t
    · rw [if_pos (hc.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h]
  have hY : ∀ y ∈ Λ', IsHalf (cA D p.e) y → heisO ψ S T y (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro y hy hh
    rw [← hTm.modul _ hΦ₀ y hh]
    congr 1
    funext t
    by_cases h : t ∈ Λ' ∧ IsHalf p.e t
    · rw [hLL' t h.1 h.2 y hy, one_mul]
    · simp [halfInd, h]
  have key : ∀ x y : WO S T, x ∈ Λ' → IsHalf p.e x → y ∈ Λ' → IsHalf (cA D p.e) y →
      ψ (symplOH S T y x) = 1 → heisO ψ S T (x + y) (Tm (halfInd p.e Λ')) = Tm (halfInd p.e Λ') := by
    intro x y hx hxh hy hyh h1
    have h := GlobalTheory.PlaceModel.heisL_heisL S T ψ y x (Tm (halfInd p.e Λ'))
    change heisO ψ S T y (heisO ψ S T x (Tm (halfInd p.e Λ'))) =
      ψ (symplOH S T y x) • heisO ψ S T (y + x) (Tm (halfInd p.e Λ')) at h
    rw [hX x hx hxh, hY y hy hyh, h1, one_smul, add_comm] at h
    exact h.symm
  have hpart : ∀ u ∈ Λ', (p.e • u ∈ Λ' ∧ IsHalf p.e (p.e • u)) ∧
      (cA D p.e • u ∈ Λ' ∧ IsHalf (cA D p.e) (cA D p.e • u)) := by
    intro u hu
    have a1 := GlobalTheory.PlaceModel.idem_smul_mem hε he heε (GlobalTheory.PlaceModel.latO_le_top _ hu)
    have a2 := GlobalTheory.PlaceModel.idem_smul_mem hε hce heε' (GlobalTheory.PlaceModel.latO_le_top _ hu)
    exact ⟨⟨a1.1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 a1.2⟩, ⟨a2.1, (GlobalTheory.PlaceModel.isHalf_iff S T).2 a2.2⟩⟩
  refine ⟨fun w hw => ?_, fun e' hse' u hu hh => ?_⟩
  · obtain ⟨⟨hx, hxh⟩, ⟨hy, hyh⟩⟩ := hpart w hw
    have e2 : 2 • w = (p.e • w + p.e • w) + (cA D p.e • w + cA D p.e • w) := by
      conv_lhs => rw [← eq_add_halves p hw]
      abel
    rw [e2]
    refine key _ _ (add_mem hx hx) (isHalf_add hxh hxh) (add_mem hy hy) (isHalf_add hyh hyh) ?_
    have hb : ψ (symplO S T (cA D p.e • w) (p.e • w)) = 1 := by
      rw [GlobalTheory.PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, hLL' _ hx hxh _ hy, inv_one]
    have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
      norm_num
    have h3 : symplOH S T (cA D p.e • w + cA D p.e • w) (p.e • w + p.e • w) =
        symplO S T (cA D p.e • w) (p.e • w) + symplO S T (cA D p.e • w) (p.e • w) := by
      unfold symplOH
      simp only [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right]
      linear_combination (2 * symplO S T (cA D p.e • w) (p.e • w)) * h2
    rw [h3, AddChar.map_add_eq_mul, hb, one_mul]
  · obtain ⟨⟨hx, hxh⟩, ⟨hy, hyh⟩⟩ := hpart u hu
    rw [← eq_add_halves p hu]
    refine key _ _ hx hxh hy hyh ?_
    obtain ⟨-, hse2, -⟩ := hse'
    have hu' : e' • u = u := (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hh)
    have h0 : symplO S T (cA D p.e • u) (p.e • u) = 0 := by
      have e1 : cA D p.e • u = e' • (cA D p.e • u) := by rw [smul_comm, hu']
      have e2 : cA D e' • (p.e • u) = 0 := smul_conj_zero p.e e' hse2 u hu'
      rw [e1, GlobalTheory.PlaceModel.symplO_smul, e2, GlobalTheory.PlaceModel.symplO_zero_right]
    unfold symplOH
    rw [h0, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.FinPl.Rebase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

namespace GlobalTheory.LocFlag

theorem conj_vanish {k : Type} [CommRing k] {Z Y M : Type} [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
    [Fintype M] [DecidableEq M] (lv : Z → ℕ) (lw : Y → ℕ) (P : Matrix Z M k) (J : Matrix M Z k) (β : Matrix M Y k)
    (γ : Matrix Y M k) (hPJ : P * J = 1) (hJP : J * P = 1) (hβγ : β * γ = 1) (hγβ : γ * β = 1)
    (hA : ∀ a r, lv a ≠ lw r → (P ⬝ β) a r = 0) (q : Matrix Y Y k)
    (hq : ∀ r s, lw s ≤ lw r → q r s = (1 : Matrix Y Y k) r s) (a b : Z) (hab : lv b ≤ lv a) :
    (P ⬝ (β * q * γ - 1) ⬝ J) a b = 0 := by
  have hAB : (P * β) * (γ * J) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc β, hβγ, Matrix.one_mul, hPJ]
  have hBA : (γ * J) * (P * β) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJP, Matrix.one_mul, hγβ]
  have hB : ∀ t b, lw t ≠ lv b → (γ ⬝ J) t b = 0 := by
    intro t b h
    generalize P * β = A at hA hAB hBA
    generalize γ * J = B at hAB hBA
    have h1 : diagonal (fun a => if lv a = lv b then (1 : k) else 0) * A =
        A * diagonal (fun r => if lw r = lv b then (1 : k) else 0) := by
      ext a r
      rw [diagonal_mul, mul_diagonal]
      by_cases e : lv a = lw r
      · rw [e, mul_comm]
      · rw [hA a r e, mul_zero, zero_mul]
    have h2 : B * diagonal (fun a => if lv a = lv b then (1 : k) else 0) =
        diagonal (fun r => if lw r = lv b then (1 : k) else 0) * B := by
      rw [← Matrix.mul_one (B * _), ← hAB, ← Matrix.mul_assoc, Matrix.mul_assoc B, h1, ← Matrix.mul_assoc, hBA,
        Matrix.one_mul]
    have h3 := congrFun (congrFun h2 t) b
    rwa [diagonal_mul, mul_diagonal, if_pos rfl, if_neg h, mul_one, zero_mul] at h3
  have e : P * (β * q * γ - 1) * J = (P * β) * (q - 1) * (γ * J) := by
    rw [← hβγ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul]
  rw [e, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  by_cases ht : lw t = lv b
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro r _
    by_cases hr : lv a = lw r
    · rw [Matrix.sub_apply, hq r t (by omega), sub_self, mul_zero]
    · rw [hA a r hr, zero_mul]
  · rw [hB t b ht, mul_zero]

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def wl (σ r : ℕ) : Fin σ ⊕ (Fin r ⊕ Fin σ) → ℕ :=
  Sum.elim (fun i => i.val + 1) (Sum.elim (fun _ => σ + 1) fun i => 2 * σ - i.val + 1)

def wJ {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : Matrix (Fin V.rank) (Fin σ ⊕ (Fin V₀.rank ⊕ Fin σ)) D.host.E :=
  fromCols d.e (fromCols d.i₀ d.e')

noncomputable def wP {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) :
    Matrix (Fin σ ⊕ (Fin V₀.rank ⊕ Fin σ)) (Fin V.rank) D.host.E :=
  fromRows d.qX (fromRows d.q0 d.qY)

theorem wJ_wP {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : wJ d * wP d = 1 := by
  rw [wJ, wP, fromCols_mul_fromRows, fromCols_mul_fromRows, ← add_assoc, d.sum_eq_one_rat]

theorem wP_wJ {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) : wP d * wJ d = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 (wJ_wP d)

theorem frame_cols {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA FV) (r : n ⊕ Fin c) :
    ∃ x : Fin σ ⊕ (Fin B.V₀.rank ⊕ Fin σ) → k, (∀ z, wl σ _ z ≠ lev (σ + 1) r → x z = 0) ∧
      ∀ u, FV.β u r = ∑ z, (wJ B.d).map (Witness.prH p) u z * x z := by
  obtain ⟨hc, h1, h2, h3, h4⟩ := h
  rcases r with a | j
  · refine ⟨Sum.elim 0 (Sum.elim (fun w => (B.o.iA.map (Witness.prH p) * FA.β) w a) 0), ?_, fun u => ?_⟩
    · rintro (z | z | z) hz
      · rfl
      · exact absurd rfl hz
      · rfl
    · rw [h1]
      change ((B.d.i₀ * B.o.iA).map (Witness.prH p) * FA.β) u a = _
      rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply]
      simp [wJ]
  · have hj := j.isLt
    rcases lt_trichotomy j.val σ with hlt | heq | hgt
    · refine ⟨Pi.single (Sum.inl ⟨j.val, hlt⟩) (s * p.xi ^ (σ - j.val)), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩
      · rintro rfl
        exact hz rfl
      · rw [h2 ⟨j.val, hlt⟩ j rfl, Finset.sum_eq_single (Sum.inl ⟨j.val, hlt⟩), Pi.single_eq_same, mul_comm]
        · rfl
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, mul_zero]
        · simp
    · refine ⟨Sum.elim 0 (Sum.elim (fun w => s * Witness.prH p (vecB B.o B.ζ w)) 0), ?_, fun u => ?_⟩
      · rintro (z | z | z) hz
        · rfl
        · exact absurd (by simp [wl, lev, heq]) hz
        · rfl
      · rw [h3 j heq]
        change s * Witness.prH p (∑ w, B.d.i₀ u w * vecB B.o B.ζ w) = _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.mul_sum]
        simp [wJ, mul_left_comm]
    · have hi : 2 * σ - j.val < σ := by omega
      refine ⟨Pi.single (Sum.inr (Sum.inr ⟨_, hi⟩))
        (s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (σ - 1 - (2 * σ - j.val))), fun z hz => Pi.single_eq_of_ne ?_ _, fun u => ?_⟩
      · rintro rfl
        exact hz (by simp only [wl, lev, Sum.elim_inr]; omega)
      · rw [h4 ⟨_, hi⟩ j (by simp only; omega), Finset.sum_eq_single (Sum.inr (Sum.inr ⟨_, hi⟩)), Pi.single_eq_same, mul_comm]
        · rfl
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb, mul_zero]
        · simp

theorem comp_vanish {σ : ℕ} (B : BesLev D σ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)) (h : p.IsBesFrame B s FA FV)
    (M : Mx D B.V.rank B.V.rank) (q : GL (n ⊕ Fin c) k) (hq : q ∈ N k n c (σ + 1))
    (hM : M.map p.π = FV.β * q.val * FV.γ) (a b : Fin σ ⊕ (Fin B.V₀.rank ⊕ Fin σ)) (hab : wl σ _ b ≤ wl σ _ a) :
    p.π (((wP B.d).map (incA D) ⬝ (M - 1) ⬝ (wJ B.d).map (incA D)) a b) = 0 := by
  have h1 : (wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p) = 1 := by
    rw [← Matrix.map_mul, wP_wJ, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (wJ B.d).map (Witness.prH p) * (wP B.d).map (Witness.prH p) = 1 := by
    rw [← Matrix.map_mul, wJ_wP, Matrix.map_one _ (map_zero _) (map_one _)]
  have key := conj_vanish (wl σ _) (lev (σ + 1)) _ _ FV.β FV.γ h1 h2 FV.βγ FV.γβ (fun a r har => by
    obtain ⟨x, hx, hβ⟩ := frame_cols p B s FA FV h r
    have : (((wP B.d).map (Witness.prH p)) ⬝ FV.β) a r =
        (((wP B.d).map (Witness.prH p) * (wJ B.d).map (Witness.prH p)) *ᵥ x) a := by
      rw [← Matrix.mulVec_mulVec, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun u _ => by rw [hβ]; rfl
    rw [this, h1, Matrix.one_mulVec, hx a har]) q.val ((GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq) a b hab
  rw [← key, ← hM, ← Matrix.map_apply (f := p.π), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub p.π),
    Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem entry_zero {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {l m : ℕ} (P : Mx D l V.rank) (J : Mx D V.rank m) (i j)
    (h1 : p.π ((P ⬝ (mt V g - 1) ⬝ J) i j) = 0)
    (h2 : p.π (((adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P)) j i) = 0) : (P ⬝ (mt V g - 1) ⬝ J) i j = 0 := by
  have e1 : (p.e + cA D p.e) • (mt V g - 1) = mt V g - 1 := Matrix.ext hg
  have e2 : (p.e + cA D p.e) * (P ⬝ (mt V g - 1) ⬝ J) i j = (P ⬝ (mt V g - 1) ⬝ J) i j := by
    conv_rhs => rw [← e1, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have e3 : (adj J ⬝ gA V) ⬝ (mt V g⁻¹ - 1) ⬝ (giA V ⬝ adj P) = adj (P ⬝ (mt V g - 1) ⬝ J) := by
    simp only [mt_inv, adj_mul, adj_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, gA_giA_cancel,
      Matrix.one_mul]
  rw [e3] at h2
  change p.π (cA D ((P ⬝ (mt V g - 1) ⬝ J) i j)) = 0 at h2
  generalize (P ⬝ (mt V g - 1) ⬝ J) i j = x at h1 h2 e2
  have a1 : p.e * x = 0 := by rw [← p.ι_π, h1, map_zero]
  have a2 : p.e * cA D x = 0 := by rw [← p.ι_π, h2, map_zero]
  have a3 : cA D p.e * x = 0 := by
    have := congrArg (cA D) a2
    rwa [map_mul, cA_cA, map_zero] at this
  rw [← e2, add_mul, a1, a3, add_zero]

theorem unip_of_blocks {R : Type} [CommRing R] {m r σ : ℕ} (jX jY : Matrix (Fin m) (Fin σ) R) (j0 : Matrix (Fin m) (Fin r) R)
    (pX pY : Matrix (Fin σ) (Fin m) R) (p0 : Matrix (Fin r) (Fin m) R) (h : jX * pX + j0 * p0 + jY * pY = 1)
    (M : Matrix (Fin m) (Fin m) R) (zXX : GlobalTheory.BesselChar.StrictUp (pX * (M - 1) * jX)) (z0X : p0 * (M - 1) * jX = 0)
    (zYX : pY * (M - 1) * jX = 0) (z00 : p0 * (M - 1) * j0 = 0) (zY0 : pY * (M - 1) * j0 = 0) :
    GlobalTheory.BesselChar.Unip jX pY M := by
  obtain ⟨L, rfl⟩ : ∃ L, M = 1 + L := ⟨M - 1, by abel⟩
  rw [add_sub_cancel_left] at zXX z0X zYX z00 zY0
  have cX : L * jX = jX * (pX * L * jX) := by
    conv_lhs => rw [← Matrix.one_mul L, ← h]
    simp only [Matrix.mul_assoc] at z0X zYX
    simp only [Matrix.add_mul, Matrix.mul_assoc, z0X, zYX, Matrix.mul_zero, add_zero]
  have c0 : L * j0 = jX * (pX * L * j0) := by
    conv_lhs => rw [← Matrix.one_mul L, ← h]
    simp only [Matrix.mul_assoc] at z00 zY0
    simp only [Matrix.add_mul, Matrix.mul_assoc, z00, zY0, Matrix.mul_zero, add_zero]
  refine ⟨⟨_, zXX, by rw [← cX, Matrix.add_mul, Matrix.one_mul]⟩, fun y hy => ?_⟩
  refine ⟨(pX * L * jX) *ᵥ (pX *ᵥ y) + (pX * L * j0) *ᵥ (p0 *ᵥ y), ?_⟩
  have hy' : y = jX *ᵥ (pX *ᵥ y) + j0 *ᵥ (p0 *ᵥ y) := by
    conv_lhs => rw [← Matrix.one_mulVec y, ← h]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hy, Matrix.mulVec_zero, add_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec _ jX, Matrix.mulVec_mulVec _ jX, ← cX, ← c0,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hy', Matrix.add_mulVec, Matrix.one_mulVec]

theorem mem_of_blocks {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (g : GA D V)
    (zXX : GlobalTheory.BesselChar.StrictUp (d.pX ⬝ (mt V g - 1) ⬝ d.jX)) (z0X : d.p0 ⬝ (mt V g - 1) ⬝ d.jX = 0)
    (zYX : d.pY ⬝ (mt V g - 1) ⬝ d.jX = 0) (z00 : d.p0 ⬝ (mt V g - 1) ⬝ d.j0 = 0)
    (zY0 : d.pY ⬝ (mt V g - 1) ⬝ d.j0 = 0) : g ∈ flagN d := by
  unfold flagN
  rw [GlobalTheory.BesselChar.mem_NFlag_iff V d.e (isIsoSub_e d).1]
  exact unip_of_blocks d.jX d.jY d.j0 d.pX d.pY d.p0 d.sum_eq_one _ zXX z0X zYX z00 zY0

theorem blocks_vanish {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (M : Mx D V.rank V.rank)
    (W : ∀ a b, wl σ _ b ≤ wl σ _ a → p.π (((wP d).map (incA D) ⬝ M ⬝ (wJ d).map (incA D)) a b) = 0) :
    (∀ i j, j ≤ i → p.π ((d.pX ⬝ M ⬝ d.jX) i j) = 0) ∧ (d.p0 ⬝ M ⬝ d.jX).map p.π = 0 ∧ (d.pY ⬝ M ⬝ d.jX).map p.π = 0 ∧
      (d.p0 ⬝ M ⬝ d.j0).map p.π = 0 ∧ (d.pY ⬝ M ⬝ d.j0).map p.π = 0 ∧
      ∀ i j, i ≤ j → p.π ((d.pY ⬝ M ⬝ d.jY) i j) = 0 := by
  refine ⟨fun i j h => W (Sum.inl i) (Sum.inl j) ?_, Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inl j) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inl j) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) ?_,
    Matrix.ext fun i j => W (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)) ?_,
    fun i j h => W (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) ?_⟩ <;>
  simp only [wl, Sum.elim_inr, Sum.elim_inl] <;> omega

theorem mem_flagN : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → g ∈ flagN B.d := by
  intro D k _ _ _ _ p σ B s n _ _ c FA FV hF g q hq hg
  obtain ⟨hS, hg⟩ := hg
  have hg' : (mt B.V g⁻¹).map p.π = FV.β * (q⁻¹).val * FV.γ := by
    have h1 : (mt B.V g⁻¹).map p.π * (mt B.V g).map p.π = 1 := by
      rw [← Matrix.map_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : (FV.β * q.val * FV.γ) * (FV.β * (q⁻¹).val * FV.γ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc FV.β (q⁻¹).val, ← Matrix.mul_assoc FV.γ, FV.γβ, Matrix.one_mul,
        Matrix.mul_assoc, ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, FV.βγ]
    rw [← Matrix.mul_one (Matrix.map _ _), ← h2, ← Matrix.mul_assoc _ (FV.β * q.val * FV.γ), ← hg, h1, Matrix.one_mul]
  obtain ⟨XX, OX, YX, OO, YO, -⟩ := blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q hq hg)
  obtain ⟨-, OX', YX', OO', YO', YY'⟩ := blocks_vanish p B.d _ (comp_vanish p B s FA FV hF _ q⁻¹ (inv_mem hq) hg')
  generalize B.d = d at *
  have aX : giA B.V ⬝ adj d.pX = d.jY := by rw [d.pX_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have aY : giA B.V ⬝ adj d.pY = d.jX := by rw [d.pY_eq, adj_mul, adj_adj, adj_gA, giA_gA_cancel]
  have a0 : giA B.V ⬝ adj d.p0 = d.j0 ⬝ giA B.V₀ := by
    rw [d.p0_eq, adj_mul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]
  have b0 : adj d.j0 ⬝ gA B.V = gA B.V₀ ⬝ d.p0 := by rw [d.p0_eq, gA_giA_cancel]
  have ev : ∀ {l m : ℕ} {x : Mx D l m}, x.map p.π = 0 → ∀ i j, p.π (x i j) = 0 := fun h i j => congrFun (congrFun h i) j
  refine mem_of_blocks d g (fun i j hij => entry_zero p hS _ _ i j (XX i j hij) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OX i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YX i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev OO i j) ?_)
    (Matrix.ext fun i j => entry_zero p hS _ _ i j (ev YO i j) ?_)
  · rw [aX, ← d.pY_eq]
    exact YY' j i hij
  · refine ev ?_ j i
    rw [a0, ← d.pY_eq, ← Matrix.mul_assoc, Matrix.map_mul, YO', Matrix.zero_mul]
  · rw [aY, ← d.pY_eq]
    exact ev YX' j i
  · refine ev ?_ j i
    rw [a0, b0, ← Matrix.mul_assoc, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _),
      Matrix.map_mul, Matrix.map_mul, OO', Matrix.mul_zero, Matrix.zero_mul]
  · refine ev ?_ j i
    rw [aY, b0, Matrix.mul_assoc (gA _), Matrix.mul_assoc (gA _), Matrix.map_mul, OX', Matrix.mul_zero]

end GlobalTheory.LocFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_flagUnipotentRadical_of_besselNormalFrameLocal : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → g ∈ flagN B.d := by
  first | exact @GlobalTheory.LocFlag.mem_flagN | exact GlobalTheory.LocFlag.mem_flagN | (intros; apply GlobalTheory.LocFlag.mem_flagN <;> assumption)
end
end
