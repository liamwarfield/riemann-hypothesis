module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColon
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColon
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ColonInt

theorem mem_int_of_pow {E : Type} [Field E] [NumberField E] (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (c y : Q.adicCompletion E) (hc : c ≠ 0) (h : ∀ n : ℕ, c * y ^ n ∈ Q.adicCompletionIntegers E) :
    y ∈ Q.adicCompletionIntegers E := by
  have h' : ∀ n : ℕ, Valued.v (c * y ^ n) ≤ 1 := fun n =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := Q)).1 (h n)
  refine (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := Q)).2 ?_
  by_contra hy
  push_neg at hy
  have hc' : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 hc'
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.1 hy0
  have hb1 : (1 : Multiplicative ℤ) < b := by
    rw [← hb] at hy
    exact WithZero.coe_lt_coe.1 hy
  have h2 := h' (Int.natAbs (Multiplicative.toAdd a) + 1)
  rw [Valuation.map_mul, Valuation.map_pow, ← ha, ← hb, ← WithZero.coe_pow, ← WithZero.coe_mul] at h2
  have h3 : a * b ^ (Int.natAbs (Multiplicative.toAdd a) + 1) ≤ 1 := WithZero.coe_le_coe.1 h2
  have h4 : Multiplicative.toAdd a + (Int.natAbs (Multiplicative.toAdd a) + 1 : ℕ) * Multiplicative.toAdd b ≤ 0 := by
    have := Multiplicative.toAdd_le.2 h3
    simpa [toAdd_mul, toAdd_pow] using this
  have h5' : 0 < Multiplicative.toAdd b := by
    have := Multiplicative.toAdd_lt.2 hb1
    simpa using this
  have h5 : 1 ≤ Multiplicative.toAdd b := by omega
  push_cast at h4
  have h6 : (0:ℤ) ≤ |Multiplicative.toAdd a| := abs_nonneg _
  have h7 : -Multiplicative.toAdd a ≤ |Multiplicative.toAdd a| := neg_le_abs _
  nlinarith

variable {D : D7}

def evQ {E : Type} [Field E] [NumberField E] (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E where
  toFun x := x Q
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem herm_cols {S : HSp D} {ρ : ℕ} (A B : Mx D S.rank ρ) (κ a : AE D) (l l' : Fin ρ) :
    GlobalTheory.IwaPlace.hermAt S (fun j => a * A j l) (fun i => κ * B i l') = cA D κ * a * (adj B * (gA S * A)) l' l := by
  simp only [GlobalTheory.IwaPlace.hermAt, Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mul_incA_mem {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) (o : 𝓞 D.host.E) :
    a * incA D (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
  rw [map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 (AddSubgroup.subset_closure ⟨1, fun w => ?_, o, ?_⟩)
  · rw [map_one]; exact one_mem _
  · rfl

theorem exists_den {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι κ D.host.E) :
    ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ ∀ k l, ∃ o : 𝓞 D.host.E, (t : D.host.E) * M k l = o := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E))
    (Finset.univ : Finset (ι × κ)) (fun p => M p.1 p.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun k l => ?_⟩
  obtain ⟨o, ho⟩ := hb (k, l) (Finset.mem_univ _)
  refine ⟨o, ?_⟩
  rw [show ((o : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E o from rfl, ho, Algebra.smul_def]

theorem colon_int : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (x : AE D), x - 1 ∈ idAt D (· = v) → (∀ r ∈ idAt D (· = v), (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → ∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * x * a) ∈ latV S L (· = v)) → x - 1 ∈ intAt D (· = v) := by
  intro D S S₀ ρ d L L₀ v _ hL _ i j x hx hK
  obtain ⟨hsupp, ⟨m, hm, hmul⟩, hchar⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL
  obtain ⟨ε, hcε, hε, hεa⟩ := GlobalTheory.IwaPlace.LocSD.exists_idem (D := D) v
  have hεε : ε * ε = ε := hεa ε hε.1
  obtain ⟨t, ht0, ht⟩ := exists_den (Matrix.fromCols d.e d.e')
  set T : AE D := incA D (t : D.host.E) with hT
  have hX : ∀ κ : AE D, κ ∈ intAt D (· = v) → ∀ l k, κ * (T * d.jX k l) ∈ intAt D (· = v) := by
    intro κ hκ l k
    obtain ⟨o, ho⟩ := ht k (Sum.inl l)
    have e : T * d.jX k l = incA D (o : D.host.E) := by
      rw [← ho, Matrix.fromCols_apply_inl, map_mul]; rfl
    rw [e]; exact mul_incA_mem hκ o
  have hY : ∀ κ : AE D, κ ∈ intAt D (· = v) → ∀ l k, κ * (T * d.jY k l) ∈ intAt D (· = v) := by
    intro κ hκ l k
    obtain ⟨o, ho⟩ := ht k (Sum.inr l)
    have e : T * d.jY k l = incA D (o : D.host.E) := by
      rw [← ho, Matrix.fromCols_apply_inr, map_mul]; rfl
    rw [e]; exact mul_incA_mem hκ o
  have hU : ∀ l (a : AE D), colMul d.jX l a ∈ latV S L (· = v) →
      ((m : AE D) * ε * cA D T) * a ∈ intAt D (· = v) := by
    intro l a ha
    have hxΛ : (fun k => ((m : AE D) * (ε * T)) * d.jY k l) ∈ latV S L (· = v) := by
      have := hmul (fun k => ε * (T * d.jY k l)) (fun k => hY ε hε l k)
      convert this using 1
      funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have h1 := ((hchar _ (hsupp _ ha)).1 ha) _ hxΛ
    rw [show colMul d.jX l a = fun j => a * d.jX j l from rfl, herm_cols, d.gram_YX, Matrix.one_apply_eq,
      mul_one] at h1
    convert h1 using 1
    rw [map_mul, map_mul, map_natCast, hcε]; ring
  obtain ⟨β, hβ⟩ : ∃ β : AE D, β = (m : AE D) * ε * cA D T := ⟨_, rfl⟩
  rw [← hβ] at hU
  have hβI : β ∈ idAt D (· = v) := by
    rw [hβ]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hε.1)
  have hc0 : colMul d.jX j ((m : AE D) * (ε * T)) ∈ latV S L (· = v) := by
    have := hmul (fun k => ε * (T * d.jX k j)) (fun k => hX ε hε j k)
    convert this using 1
    funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = (m : AE D) * (T * β) := ⟨_, rfl⟩
  have hcK : ∀ a, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (c * a) ∈ latV S L (· = v) := by
    intro a ha
    have := hmul (fun k => (β * a) * (T * d.jX k i)) (fun k => hX _ (hU j a ha) i k)
    convert this using 1
    funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul, hc]; ring
  have hcI : c ∈ idAt D (· = v) := by
    rw [hc]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hβI)
  have hit : ∀ n : ℕ, c * x ^ n ∈ idAt D (· = v) ∧ ∀ a, colMul d.jX j a ∈ latV S L (· = v) →
      colMul d.jX i (c * x ^ n * a) ∈ latV S L (· = v) := by
    intro n
    refine ⟨Ideal.mul_mem_right _ _ hcI, ?_⟩
    induction n with
    | zero => rw [pow_zero, mul_one]; exact hcK
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact hK _ (Ideal.mul_mem_right _ _ hcI) ih
  have hbd : ∀ n : ℕ, β * (c * x ^ n * ((m : AE D) * (ε * T))) ∈ intAt D (· = v) := fun n =>
    hU i _ ((hit n).2 _ hc0)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine ⟨hx, (hΦ.int _).2 fun Q => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AE D →+* Q.adicCompletion D.host.E, ∀ z, ψ z = Φ z Q :=
    ⟨(evQ Q).comp Φ, fun _ => rfl⟩
  have hψinc : ∀ e : D.host.E, ψ (incA D e) = algebraMap D.host.E _ e := fun e => by
    rw [hψ, hΦ.inc]; rfl
  have hεQ : ψ ε = 0 ∨ ψ ε = 1 := by
    have h := congrArg ψ hεε
    rw [map_mul] at h
    rcases mul_eq_zero.1 (show ψ ε * (ψ ε - 1) = 0 by rw [mul_sub, h, mul_one, sub_self]) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  rw [← hψ]
  rcases hεQ with h0 | h1
  · rw [← hεa _ hx, map_mul, h0, zero_mul]; exact zero_mem _
  · rw [map_sub, map_one]
    refine sub_mem ?_ (one_mem _)
    have ht' : (t : D.host.E) ≠ 0 := by exact_mod_cast ht0
    have hκ : (m : D.host.E) ^ 4 * star (t : D.host.E) ^ 2 * (t : D.host.E) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hm.ne')) (pow_ne_zero _ (star_ne_zero.2 ht')))
        (pow_ne_zero _ ht')
    refine mem_int_of_pow Q _ (ψ x) ((map_ne_zero (algebraMap D.host.E _)).2 hκ) fun n => ?_
    have h := (hΦ.int _).1 (hbd n).2 Q
    rw [← hψ] at h
    have e1 : ψ T = algebraMap D.host.E _ (t : D.host.E) := hψinc _
    have e2 : ψ (cA D T) = algebraMap D.host.E _ (star (t : D.host.E)) := hψinc _
    rw [hc, hβ] at h
    simp only [RingHom.map_mul, RingHom.map_pow, map_natCast, h1] at h ⊢
    rw [← e1, ← e2]
    convert h using 1
    ring

end GlobalTheory.ColonInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColonStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_keeps_selfDualLatticeLineColon : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (x : AE D), x - 1 ∈ idAt D (· = v) → (∀ r ∈ idAt D (· = v), (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → ∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * x * a) ∈ latV S L (· = v)) → x - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.ColonInt.colon_int | exact GlobalTheory.ColonInt.colon_int | (intros; apply GlobalTheory.ColonInt.colon_int <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOrthSummandSlicesSobolevBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOrthSummandSlicesSobolevBounded
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

def slA (o : OrthDec S A B) (f : WO S T → ℂ) : WO A T → ℂ := fun u => f ((o.resS T).symm (u, 0))

def extA (o : OrthDec S A B) (T : HSp D) : WO A T →+ WO S T :=
  (o.resS T).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem extA_apply (o : OrthDec S A B) (u : WO A T) : extA o T u = (o.resS T).symm (u, 0) := rfl

theorem symm_left (o : OrthDec S A B) (u : WO A T) : (o.resS T).symm (u, 0) = u ⬝ o.pA := by
  rw [o.resS_symm_apply, Matrix.zero_mul, add_zero]

theorem symm_swap (o : OrthDec S A B) (v : WO B T) : (o.symm.resS T).symm (v, 0) = (o.resS T).symm (0, v) := by
  rw [OrthDec.resS_symm_apply, OrthDec.resS_symm_apply]
  exact add_comm _ _

theorem compAt_pA {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B) (τ : D.what₂.Tau) :
    compAt θ τ o.pA = o.qA.map (tauE D τ) := by
  unfold compAt OrthDec.pA GlobalTheory.MixModel.rat
  rw [Matrix.map_map]
  congr 1
  funext e
  exact GlobalTheory.FockCompare.comp_incA hθ τ e

theorem lineAt_slice {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin A.rank) ℂ) (t : ℝ) :
    (o.resS T).symm (lineAt θ τ z t, 0) = lineAt θ τ (z * o.qA.map (tauE D τ)) t := by
  have hL := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ z
  let L : ℝ →+ WO S T := (extA o T).comp (lineAt θ τ z)
  have hL' : IsLineAt θ τ (z * o.qA.map (tauE D τ)) L := by
    refine ⟨(o.continuous_resS_symm T).comp (hL.1.prodMk continuous_const), fun t => ?_, fun t τ' => ?_⟩
    · show ((o.resS T).symm (lineAt θ τ z t, 0)).map (finPart D) = 0
      rw [symm_left, Matrix.map_mul, hL.2.1, Matrix.zero_mul]
    · show compAt θ τ' ((o.resS T).symm (lineAt θ τ z t, 0)) = _
      rw [symm_left, GlobalTheory.OrientedHeis.compAt_mul, hL.2.2, compAt_pA hθ]
      split_ifs with h
      · subst h
        rw [Matrix.smul_mul]
      · rw [Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ _) hL']
  rfl

theorem heisO_slice (ψ : AddChar (AF D.host.F) ℂ) (o : OrthDec S A B) (u : WO A T) (g : WO S T → ℂ) :
    heisO ψ A T u (slA o g) = slA o (heisO ψ S T ((o.resS T).symm (u, 0)) g) := by
  funext w
  simp only [slA, heisO]
  rw [o.symplOH_resS T, ← map_add (f := _), Prod.mk_add_mk, add_zero]
  simp only [AddEquiv.apply_symm_apply, symplOH_zero_left, add_zero]

theorem dRho_slice (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin A.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ A T) θ τ z (slA o g) =
      slA o (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z * o.qA.map (tauE D τ)) g) := by
  funext w
  simp only [Formalism.IndefR.Datum.dRho, heisO_slice, lineAt_slice hθ]
  rfl

end GlobalTheory.SliceForm

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

def dirA (o : OrthDec S A B) (a : D.what₂.Tau × Fin T.rank × Fin A.rank × Bool) : Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) * o.qA.map (tauE D a.1)

def opA (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (o : OrthDec S A B)
    (a : D.what₂.Tau × Fin T.rank × Fin A.rank × Bool) (g : WO S T → ℂ) : WO S T → ℂ :=
  Formalism.IndefR.Datum.dRho (heisO ψ S T) θ a.1 (dirA o a) g

theorem word_slice (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    (l : List (D.what₂.Tau × Fin T.rank × Fin A.rank × Bool)) (g : WO S T → ℂ) :
    wordAct (heisDer ψ θ) l (slA o g) = slA o (wordAct (opA ψ θ o) l g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordAct_cons, wordAct_cons, ih]
    exact dRho_slice ψ hθ o a.1 _ _

abbrev supN (φ : WO S T → ℂ) : ℝ≥0∞ := ⨆ w, ‖φ w‖ₑ

theorem word_bound {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    (o : OrthDec S A B) (l : List (D.what₂.Tau × Fin T.rank × Fin A.rank × Bool)) :
    ∃ c : ℝ≥0, ∀ g, IsThetaFunO ψ S T g → ∀ k,
      wordSum (heisDer ψ θ) supN k (wordAct (opA ψ θ o) l g) ≤ c * wordSum (heisDer ψ θ) supN (k + l.length) g := by
  induction l with
  | nil => exact ⟨1, fun g _ k => by simp⟩
  | cons a l ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨Real.toNNReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) * c, fun g hg k => ?_⟩
    have hg' : IsThetaFunO ψ S T (wordAct (opA ψ θ o) l g) :=
      wordAct_rel (B := opA ψ θ o) (R := fun x _ => IsThetaFunO ψ S T x) l
        (fun a _ _ _ h => theta_dRho hθ hψ a.1 _ h) (y := g) hg
    rw [wordAct_cons]
    calc _ ≤ ENNReal.ofReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) *
          wordSum (heisDer ψ θ) supN (k + 1) (wordAct (opA ψ θ o) l g) :=
          GlobalTheory.Size.SupWord.ws_dRho_le hψ hθ GlobalTheory.Size.SupWord.supN_add_le GlobalTheory.Size.SupWord.supN_smul hg' a.1 _ k
      _ ≤ ENNReal.ofReal (∑ i, ∑ j, (|(dirA o a i j).re| + |(dirA o a i j).im|)) *
          (c * wordSum (heisDer ψ θ) supN (k + 1 + l.length) g) := by gcongr; exact hc g hg (k + 1)
      _ = _ := by
        rw [List.length_cons, show k + (l.length + 1) = k + 1 + l.length by omega, ← mul_assoc, ENNReal.ofReal,
          ENNReal.coe_mul]

theorem l2O_le_supN_of_measure_eq_one {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (h1 : μ 𝓕 = 1) (φ : WO S T → ℂ) (hφ : Continuous φ) :
    l2O μ 𝓕 φ ≤ supN φ := by
  have h : l2O μ 𝓕 φ ^ 2 ≤ supN φ ^ 2 := by
    have : BorelSpace (WO S T) := ⟨rfl⟩
    have he : l2O μ 𝓕 φ ^ 2 = ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ := by
      simpa [l2O] using eLpNorm_nnreal_pow_eq_lintegral (μ := μ.restrict 𝓕) (p := 2)
        two_ne_zero hφ.measurable.aestronglyMeasurable
    rw [he]
    calc ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ ≤ ∫⁻ _ in 𝓕, supN φ ^ 2 ∂μ :=
          lintegral_mono fun w => by gcongr; exact le_iSup (fun w => ‖φ w‖ₑ) w
      _ = supN φ ^ 2 := by rw [setLIntegral_const, h1, mul_one]
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem supN_slice (o : OrthDec S A B) (φ : WO S T → ℂ) : supN (slA o φ) ≤ supN φ :=
  iSup_le fun _ => le_iSup (fun w => ‖φ w‖ₑ) _

end GlobalTheory.SliceForm

namespace GlobalTheory.SliceForm

open GlobalTheory.Size GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {S A B T : HSp D}

theorem sobO_slice_le {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ)
    (o : OrthDec S A B) (d : ℕ) : ∃ K : ℝ≥0, ∀ (μ : Measure (WO A T)) (𝓕 : Set (WO A T)), μ 𝓕 = 1 →
      ∀ f, IsThetaFunO ψ S T f → sobO ψ θ μ 𝓕 d (slA o f) ≤ K * supSob ψ θ d f := by
  choose c hc using word_bound (T := T) hψ hθ o
  refine ⟨∑ k ∈ Finset.range (d + 1), ∑ a : Fin k → D.what₂.Tau × Fin T.rank × Fin A.rank × Bool, c (List.ofFn a),
    fun μ 𝓕 h1 f hf => ?_⟩
  unfold sobO supSob wordSum
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [word_slice ψ hθ o]
  have hg : IsThetaFunO ψ S T (wordAct (opA ψ θ o) (List.ofFn a) f) :=
    wordAct_rel (B := opA ψ θ o) (R := fun x _ => IsThetaFunO ψ S T x) (List.ofFn a)
      (fun a _ _ _ h => theta_dRho hθ hψ a.1 _ h) (y := f) hf
  have hs : Continuous (slA o (wordAct (opA ψ θ o) (List.ofFn a) f)) :=
    hg.cont.comp ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
  calc l2O μ 𝓕 (slA o (wordAct (opA ψ θ o) (List.ofFn a) f)) ≤ supN (wordAct (opA ψ θ o) (List.ofFn a) f) :=
        (l2O_le_supN_of_measure_eq_one h1 _ hs).trans (supN_slice o _)
    _ = wordSum (heisDer ψ θ) supN 0 (wordAct (opA ψ θ o) (List.ofFn a) f) := (wordSum_zero _ _ _).symm
    _ ≤ c (List.ofFn a) * wordSum (heisDer ψ θ) supN (0 + (List.ofFn a).length) f := hc _ f hf 0
    _ ≤ c (List.ofFn a) * wordSum (heisDer ψ θ) supN d f := by
        gcongr
        exact wordSum_mono (by rw [List.length_ofFn]; omega) f
    _ = _ := rfl

theorem isSobForm_slice {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) (o : OrthDec S A B)
    {χ χ' : (AE D)ˣ →* Circle} {om : Om A T} (hom : IsWeilDatumO ψ A T χ χ' om) (p : GA D A × GA D T) :
    IsSobForm ψ θ S T (fun f => om p (fun u => f ((o.resS T).symm (u, 0))) 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g _ _
    exact congrFun ((om p).map_add (slA o f) (slA o g)) 0
  · intro c f _
    exact congrFun ((om p).map_smul c (slA o f)) 0
  · intro U hU
    have hψ := hom.std
    let U' : AddSubgroup (WO A T) := U.comap (extA o T)
    have hU' : IsOpen (U' : Set (WO A T)) :=
      hU.preimage ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
    obtain ⟨e, d, hK⟩ := GlobalTheory.KernelSeminorm.thetaGrowth_onObjects D A.rank T.rank
    obtain ⟨C, hC⟩ := hK A T rfl rfl ψ θ hθ U' hU'
    obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne A T
    obtain ⟨K, hKs⟩ := sobO_slice_le (T := T) hψ hθ o d
    refine ⟨d, C * (ENNReal.ofReal ((height A p.1 * height T p.2) ^ e)).toNNReal * K, fun f hf => ?_⟩
    have hsl : slA o f ∈ GlobalTheory.Size.thetaLevel ψ A T U' := by
      refine ⟨((GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf.1).1 0, fun u hu h0 => ?_⟩
      rw [heisO_slice, ← extA_apply, hf.2 _ hu]
      rw [extA_apply, symm_left, Matrix.map_mul, h0, Matrix.zero_mul]
    have h := hC χ χ' om hom μ 𝓕 hμ (slA o f) hsl p.1 p.2
    have h2 := hKs μ 𝓕 hμ.2.2 f hf.1
    have hfin : ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc ‖om p (fun u => f ((o.resS T).symm (u, 0))) 0‖ₑ = ‖thetaKO om p.1 p.2 (slA o f)‖ₑ := rfl
      _ ≤ C * sobO ψ θ μ 𝓕 d (slA o f) * ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) := h
      _ ≤ C * (K * supSob ψ θ d f) * ENNReal.ofReal ((height A p.1 * height T p.2) ^ e) := by gcongr
      _ = _ := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hfin]
        ring

theorem weil_slice_isSobForm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (S A B T : HSp D) (o : OrthDec S A B),
      (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om →
        ∀ p, IsSobForm ψ θ S T fun f => om p (fun u => f ((o.resS T).symm (u, 0))) 0) ∧
      ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om →
        ∀ p, IsSobForm ψ θ S T fun f => om p (fun v => f ((o.resS T).symm (0, v))) 0 := by
  intro D ψ θ hθ S A B T o
  refine ⟨fun χ χ' om hom p => isSobForm_slice hθ o hom p, fun χ χ' om hom p => ?_⟩
  have e : (fun f : WO S T → ℂ => om p (fun v => f ((o.resS T).symm (0, v))) 0) =
      fun f => om p (fun v => f ((o.symm.resS T).symm (v, 0))) 0 := by
    funext f
    simp only [symm_swap]
  rw [e]
  exact isSobForm_slice hθ o.symm hom p

end GlobalTheory.SliceForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOrthSummandSlicesSobolevBoundedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_orth_summand_slices_sobolev_bounded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, IsSobForm ψ θ S T fun f => om p (fun u => f ((o.resS T).symm (u, 0))) 0) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, IsSobForm ψ θ S T fun f => om p (fun v => f ((o.resS T).symm (0, v))) 0 := by
  first | exact @GlobalTheory.SliceForm.weil_slice_isSobForm | exact GlobalTheory.SliceForm.weil_slice_isSobForm | (intros; apply GlobalTheory.SliceForm.weil_slice_isSobForm <;> assumption)
end
end
