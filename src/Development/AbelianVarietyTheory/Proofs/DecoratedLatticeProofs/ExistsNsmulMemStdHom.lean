module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairSchrodingerFunctionContinuousIntegrab

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm

variable {D : D7}

theorem coe_colStdLat (n : ℕ) :
    ((Formalism.L2.Col.stdLat D.host.E n : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun hy => ⟨⟨_, hy⟩, rfl⟩⟩

theorem exists_nsmul_mem_stdHom (S T : HSp D) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
    (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → K • t ∈ stdHom S T := by
  have hfull (n : ℕ) : Submodule.IsFullLattice D.host.E (Formalism.L2.Col.stdLat D.host.E n) := by
    letI := Formalism.L2.Col.stdLat_lattice (E := D.host.E) (n := n)
    constructor
    apply eq_top_iff.mpr
    intro x _
    rw [pi_eq_sum_univ' x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (by simpa using Formalism.L2.Col.single_mem_stdLat (E := D.host.E) i 1))
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (hfull S.rank) (hfull T.rank)
  refine ⟨K, hK, fun t ht hi => ?_⟩
  have := h t ht hi
  rwa [coe_colStdLat, coe_colStdLat] at this

theorem infPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (GlobalTheory.LatticeStable.liftFin D x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => exact GlobalTheory.LatVac.infPart_pair a m
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy, add_zero]

theorem finPart_liftFin (x : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (GlobalTheory.LatticeStable.liftFin D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, RingHom.map_zero]
  | tmul a m => rfl
  | add x y hx hy => rw [LinearMap.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem toEAf_eq_comm (z : AE D) :
    toEAf D z = Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D z) := rfl

theorem toEAf_liftFin (r : EAf D) :
    toEAf D (GlobalTheory.LatticeStable.liftFin D ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm r)) = r := by
  rw [toEAf_eq_comm, finPart_liftFin, AlgEquiv.apply_symm_apply]

theorem toEAf_approx_eq_zero (t L : AE D) (x : D.host.E) (M : ℕ) (r : EAf D)
    (ht : toEAf D t = eToEAf D x + (M : EAf D) * r) (hL : toEAf D L = -r) :
    toEAf D (incA D x - t - (M : AE D) * L) = 0 := by
  have hi : toEAf D (incA D x) = eToEAf D x := rfl
  rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, map_natCast, hi, ht, hL]
  ring

theorem approx_entry (t : AE D) (M : ℕ) (hM : 0 < M) : ∃ (x : D.host.E) (w : AE D), infPart D w = 0 ∧
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ finPart D (incA D x - t - (M : AE D) * w) = 0 := by
  have hM0 : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  obtain ⟨x, r, hr, e⟩ := GlobalTheory.AdeleBaseChange.exists_approx (F := D.host.F) (E := D.host.E)
    (eToEAf D (M : D.host.E)⁻¹ * toEAf D t)
  let c := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
  refine ⟨M * x, GlobalTheory.LatticeStable.liftFin D (c.symm (-r)), infPart_liftFin _, ?_, ?_⟩
  · rw [toEAf_liftFin]
    exact neg_mem hr
  · have ht : toEAf D t = eToEAf D (M * x) + (M : EAf D) * r := by
      have e2 := congrArg (eToEAf D (M : D.host.E) * ·) e
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul] at e2
      rw [e2, map_mul, map_natCast, mul_add]
      rfl
    have hz := toEAf_approx_eq_zero t _ (M * x) M r ht (toEAf_liftFin (-r))
    rw [toEAf_eq_comm] at hz
    exact c.injective (hz.trans (map_zero c).symm)

theorem exists_rat_half_approx : ∀ {D : D7} (S T : HSp D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → ∀ (N : ℕ), 0 < N → ∀ y : WO S T, ∃ (γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T ∧ IsHalf e v ∧ γ₀.map (fun r => e * incA D r) = e • y + N • v := by
  intro D S T e P he N hN y
  obtain ⟨K, hK, hKm⟩ := exists_nsmul_mem_stdHom S T
  choose x w hw0 hwi hz using fun i j => approx_entry (y i j) (N * K) (Nat.mul_pos hN hK)
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hKw : K • (Matrix.of fun i j => w i j) ∈ stdHom S T := hKm _ (Matrix.ext fun i j => hw0 i j) hwi
  refine ⟨Matrix.of x, e • (K • Matrix.of fun i j => w i j), ?_, ?_, ?_⟩
  · exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hKw
  · intro i j
    change e * (e * _) = e * _
    rw [← mul_assoc, hee]
  · ext i j
    have h0 : e * (incA D (x i j) - y i j - ((N * K : ℕ) : AE D) * w i j) = 0 := by
      refine GlobalTheory.LatVac.eq_zero_of_parts _ ?_ ?_
      · rw [map_mul, hinf, zero_mul]
      · rw [map_mul, hz i j, mul_zero]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul]
    push_cast at h0
    linear_combination h0

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.LastTwoSteps
open GlobalTheory.StepData GlobalTheory.SymChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem intInd_mem_SB (a b : Type) [Fintype a] [Fintype b] :
    Set.indicator {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => (1 : ℂ)) ∈ SB (Matrix a b k) := by
  classical
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : T2Space (Matrix a b k) := inferInstanceAs (T2Space (a → b → k))
  have e : {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} =
      Set.pi Set.univ fun _ : a => Set.pi Set.univ fun _ : b => (𝒪[k] : Set k) := by
    ext x; exact ⟨fun h r _ q _ => h r q, fun h r q => h r trivial q trivial⟩
  have hK : IsCompact {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} := by
    rw [e]; exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k
  have ho : IsOpen {x : Matrix a b k | ∀ r q, x r q ∈ 𝒪[k]} := by
    rw [e]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
  have := GlobalTheory.FinPl.Comm.ite_mem_SB hK ho
  convert this using 1
  funext x
  by_cases h : ∀ r q, x r q ∈ 𝒪[k] <;> simp [Set.indicator_apply, h]

variable [MeasurableSpace k] [BorelSpace k]

theorem hat_const_mul {n : Type} [Fintype n] (ψ : AddChar k Circle) (ν : Measure k) (ε : k) (c : ℂ)
    (f : (n → k) → ℂ) (η : n → k) : hat ψ ν ε (fun y => c * f y) η = c * hat ψ ν ε f η := by
  simp only [hat, mul_assoc]
  rw [integral_const_mul]


open Classical in
theorem hat_int {n : Type} [Fintype n] [DecidableEq n] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k}
    (hν : IsUnitVol ν) {ε : k} (hε : valuation k ε = 1) (η : n → k) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0)) η = if ∀ i, η i ∈ 𝒪[k] then 1 else 0 := by
  classical
  have := hν.1
  have := secondCountable k
  split_ifs with hη
  · have hε' : ε ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, hε]
    rw [GlobalTheory.StepData.Model.hat_coset hψ hν hε' 0 hη]
    simp
  · have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
        cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0) (x + z) =
        cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk 0) x := fun z hz x => by
      have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
        (Submodule.Quotient.eq _).2 (by simpa using hz)
      simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
    refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
      (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
    · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
    · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

section Entries
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]

theorem psi_mem_SB (T : Chain k s X Z) (hT : T.Regular) (y : X (s + 1) → k) :
    (fun x₀ => T.Psi 1 x₀ y) ∈ SB (Matrix (X (s + 1)) (X s) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := X (s + 1)) (n' := X s)
  refine GlobalTheory.FinPl.Comm.comp_mem_SB (om_mem_SB (T.mu (s + 1)) 1 1 (hT.1 s 0 rfl))
    (p := fun x₀ => withCol x₀ y) (s := fun x => x.toBlocks₁₁) ?_ ?_ fun x => rfl
  · unfold withCol; fun_prop
  · exact continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))

variable [MeasurableSpace k] [BorelSpace k]

theorem xiTop_mem_SB (T : Chain k s X Z) (hT : T.Regular) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1)
    {ν : Measure k} (hν : IsUnitVol ν) {ε : k} (hε : valuation k ε = 1) (yb : (X (s + 1) → k) ⧸ box (X (s + 1)) (1 : kˣ)) :
    T.xiTop (box _ (1 : kˣ)) ψ ν ε yb ∈ SB (Matrix (Z ⊕ Unit) (X (s + 1)) k) := by
  haveI := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField (k := k) (n := Z ⊕ Unit) (n' := X (s + 1))
  have hh := (GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol k ψ ν ε hψ hν hε (X (s + 1)) 1 1 _ (cosetInd_mem_SB 1 yb)).1
  refine GlobalTheory.FinPl.Comm.prod_mem_SB hT.2.1 hh
    (p := fun x : Matrix (Z ⊕ Unit) (X (s + 1)) k => fromCols x.toRows₁ (0 : Matrix Z (Fin 0) k))
    (r := fun x => x (Sum.inr ()))
    (s := fun z => fromRows z.1.toCols₁ (Matrix.of fun (_ : Unit) => z.2)) ?_ ?_ ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases j with j | j
      · exact (continuous_apply j).comp (continuous_apply (Sum.inl i))
      · exact j.elim0
  · exact continuous_apply _
  · exact continuous_pi fun i => continuous_pi fun j => by
      rcases i with i | i
      · exact (continuous_apply (Sum.inl j)).comp ((continuous_apply i).comp continuous_fst)
      · exact (continuous_apply j).comp continuous_snd
  · intro x; ext (i | i) j <;> rfl

end Entries

section Ones
variable {a b c : Type} [Fintype a] [DecidableEq a] [Fintype b] [Fintype c]


open Classical in
theorem cosetInd_zero (y : a → k) :
    cosetInd (box a (1 : kˣ)) (Submodule.Quotient.mk 0) y = if ∀ i, y i ∈ 𝒪[k] then 1 else 0 := by
  have hy : (Submodule.Quotient.mk y : (a → k) ⧸ box a (1 : kˣ)) = Submodule.Quotient.mk 0 ↔ ∀ i, y i ∈ 𝒪[k] := by
    simp [Submodule.Quotient.eq, mem_box, Valuation.mem_integer_iff]
  unfold cosetInd
  by_cases h : ∀ i, y i ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {y : a → k | Submodule.Quotient.mk y = Submodule.Quotient.mk 0}) (a := y)
      (hy.2 h), if_pos h]
  · rw [Set.indicator_of_notMem (s := {y : a → k | Submodule.Quotient.mk y = Submodule.Quotient.mk 0}) (a := y)
      (mt hy.1 h), if_neg h]


open Classical in
theorem intInd_fromCols (q : Matrix a b k) (y : a → k) :
    Set.indicator {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ))
        (fromCols q (Matrix.of fun r _ => y r)) =
      Set.indicator {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q *
        cosetInd (box a (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
  have hf : (∀ r c, fromCols q (Matrix.of fun r (_ : Unit) => y r) r c ∈ 𝒪[k]) ↔
      (∀ r c, q r c ∈ 𝒪[k]) ∧ ∀ i, y i ∈ 𝒪[k] := by
    constructor
    · intro h
      exact ⟨fun r c => by simpa using h r (Sum.inl c), fun r => by simpa using h r (Sum.inr ())⟩
    · rintro ⟨hq, hy⟩ r (c | c)
      · simpa using hq r c
      · simpa using hy r
  rw [cosetInd_zero]
  by_cases h : ∀ r c, fromCols q (Matrix.of fun r (_ : Unit) => y r) r c ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]}) (a := _) h,
      Set.indicator_of_mem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) (hf.1 h).1, if_pos (hf.1 h).2,
      mul_one]
  · rw [Set.indicator_of_notMem (s := {x : Matrix a (b ⊕ Unit) k | ∀ r c, x r c ∈ 𝒪[k]}) (a := _) h]
    by_cases hq : ∀ r c, q r c ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) hq,
        if_neg fun h2 => h (hf.2 ⟨hq, h2⟩), mul_zero]
    · rw [Set.indicator_of_notMem (s := {x : Matrix a b k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) hq, zero_mul]


open Classical in
theorem intInd_rows (q : Matrix (c ⊕ Unit) a k) :
    Set.indicator {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q =
      Set.indicator {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]} (fun _ => (1 : ℂ)) q.toRows₁ *
        if ∀ i, q (Sum.inr ()) i ∈ 𝒪[k] then 1 else 0 := by
  have hr : (∀ r c, q r c ∈ 𝒪[k]) ↔ (∀ r c, q.toRows₁ r c ∈ 𝒪[k]) ∧ ∀ i, q (Sum.inr ()) i ∈ 𝒪[k] := by
    constructor
    · intro h
      exact ⟨fun r c => h (Sum.inl r) c, fun i => h (Sum.inr ()) i⟩
    · rintro ⟨hr, hη⟩ (r | r) c
      · exact hr r c
      · exact hη c
  by_cases h : ∀ r c, q r c ∈ 𝒪[k]
  · rw [Set.indicator_of_mem (s := {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) h,
      Set.indicator_of_mem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) (hr.1 h).1,
      if_pos (hr.1 h).2, mul_one]
  · rw [Set.indicator_of_notMem (s := {x : Matrix (c ⊕ Unit) a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q) h]
    by_cases h1 : ∀ r c, q.toRows₁ r c ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) h1,
        if_neg fun h2 => h (hr.2 ⟨h1, h2⟩), mul_zero]
    · rw [Set.indicator_of_notMem (s := {x : Matrix c a k | ∀ r c, x r c ∈ 𝒪[k]}) (a := q.toRows₁) h1, zero_mul]

end Ones

theorem gLast : ∀ (D : D7), LastLoc D → GlobalTheory.SymChain.AtMostOne → GLast D := by
  classical
  intro D hLL hAMO k _ _ _ _ _ _ ν hν p s κ S t _ _ ψ hstd hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz
    FA F₀ FS FT FX hcore hFX c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hΦ₁ hΦ₂ hO₁ hO₂
  have := hν.1
  obtain ⟨-, -, h1, h2, -⟩ := hAMO k ν hν s κ S t
  obtain ⟨Λ, hΛ, hK⟩ := hLL k p ν hν.1 ψ hstd S.ψ hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz _ _ _ FA F₀ FS FT FX
    hcore hFX T₁ T₂ hT₁ hT₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Φ₁ Φ₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁ O₂
  have hreg : (S.T t).Regular := Chain.ofType_regular _ _ _ _ _
  have hv1 : valuation k (-1 : k) = 1 := by simp
  let Ξ₁ : SB (Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) := ⟨_, psi_mem_SB _ hreg (S.y0 t)⟩
  let Ξ₂ : SB (Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) :=
    ⟨_, xiTop_mem_SB _ hreg S.cond hν hv1 (Submodule.Quotient.mk (S.y0 t))⟩
  let O₁' : SB (Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k) := ⟨_, intInd_mem_SB _ _⟩
  let O₂' : SB (Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k) := ⟨_, intInd_mem_SB _ _⟩
  have hcp : ∀ x₀ y, (S.T t).Psi 1 x₀ y =
      (S.T t).Psi 1 x₀ (S.y0 t) * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk (S.y0 t)) y := fun x₀ y => by
    by_cases hy : y - S.y0 t ∈ box _ (1 : kˣ)
    · rw [h2 x₀ y hy, cosetInd, Set.indicator_of_mem, mul_one]
      exact (Submodule.Quotient.eq _).2 hy
    · rw [cosetInd, Set.indicator_of_notMem, mul_zero]
      · exact not_not.1 (mt (h1 x₀ y) hy)
      · exact fun h => hy ((Submodule.Quotient.eq _).1 h)
  have hprod : ∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2 := fun q => by
    rw [hΞ q, hΦ₂]
    have e : (fun y => Φ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        (S.T t).Psi 1 q.1 (S.y0 t) * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk (S.y0 t)) y := by
      funext y
      rw [hΦ₁, ← hcp]
      rfl
    rw [e, hat_const_mul]
    show _ = (S.T t).Psi 1 q.1 (S.y0 t) * ((S.T t).PhiTop (fromCols q.2.toRows₁ 0) * _)
    ring
  have hone : ∀ q, Ξ'.1 q = O₁'.1 q.1 * O₂'.1 q.2 := fun q => by
    rw [hΞ' q, hO₂]
    have e : (fun y => O₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix (XIx (Fin κ) t (s + 1)) (XIx (Fin κ) t s) k | ∀ r q, x r q ∈ 𝒪[k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
      funext y
      rw [hO₁]
      exact intInd_fromCols q.1 y
    rw [e, hat_const_mul, hat_int S.cond hν hv1]
    simp only [O₁', O₂']
    rw [intInd_rows q.2]
    ring
  have key := (GlobalTheory.T.heisenbergCombination_twoVariableModel_and_lineExtension D k p ψ _ _ _).1 B.A W X FA FS FX Λ c₁ c₂ Ξ₁ O₁' Ξ₂ O₂' Ξ Ξ' hΛ hc₁ hc₂ rfl rfl hprod hone
  have e1 := funext hΞK
  have e2 := funext hΞ'K
  rw [e1, e2]
  exact key

end GlobalTheory.LastTwoSteps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValQOfValQr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QVal

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def places {r : ℕ} (Q : Fin r → QStep S) : GlobalTheory.FinPl.Pl D → Prop := fun v => ∃ i, (Q i).q.v = v

def integrand {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  GlobalTheory.PosOne.comb (conv (List.ofFn fun i => (Q i).e₀.mapDomain (Q i).gl₀)) fun a =>
    S.val c₁ c₂ (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₁)) f₁) (comb ψ _ _ (aconv (List.ofFn fun i => (Q i).D₂)) f₂)
      φ f (g * a) (h₁ * x) (h₂ * y)

def value {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : ℂ :=
  (∏ i, (Q i).volJ) * ∑ γ : ∀ i, (Q i).A₁, ∑ β : ∀ i, (Q i).A₂, (∏ i, (Q i).w₁ (γ i) * (Q i).w₂ (β i)) *
    S.val (aconv (c₁ :: List.ofFn fun i => (Q i).d₁ (γ i))) (aconv (c₂ :: List.ofFn fun i => (Q i).d₂ (γ i) (β i))) f₁ f₂ φ
      (trc (conv (List.ofFn fun i => ((Q i).e₂ (β i)).mapDomain (Q i).gl₂)) f) g h₁ h₂

def innerVal {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) (x : GA D S.J.W) (y : GA D S.B'.V) : ℂ :=
  (Q 0).volJ * ∑ γ : (Q 0).A₁, ∑ β : (Q 0).A₂, ((Q 0).w₁ γ * (Q 0).w₂ β) *
    integrand (fun i => Q i.succ) (aconv [c₁, (Q 0).d₁ γ]) (aconv [c₂, (Q 0).d₂ γ β]) f₁ f₂ φ
      (trc (((Q 0).e₂ β).mapDomain (Q 0).gl₂) f) g h₁ h₂ x y

def Hyps {r : ℕ} (Q : Fin r → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V) : Prop :=
  (∀ i, (Q i).Away c₁ ∧ (Q i).Away c₂) ∧ IsThetaFunO ψ _ _ f₁ ∧ IsThetaFunO ψ _ _ f₂ ∧ (∀ i, (Q i).Vac f₁ f₂) ∧
    IsContAut S.B.A φ ∧ IsContAut S.B'.V f ∧ (∀ i, (Q i).Typed f) ∧ g ∈ GlobalTheory.FinPl.grpOff S.B.V (places Q) ∧
    h₁ ∈ GlobalTheory.FinPl.grpOff S.J.W (places Q) ∧ h₂ ∈ GlobalTheory.FinPl.grpOff S.B'.V (places Q)

def Norm {r : ℕ} (Q : Fin r → QStep S) (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q)))
    (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q)))) (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))) : Prop :=
  μ₁.IsHaarMeasure ∧ ρ₁.IsHaarMeasure ∧ μ₂.IsHaarMeasure ∧ ρ₂.IsHaarMeasure ∧
    μ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1} = 1 ∧ ρ₁ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₁ x.1.1} = 1 ∧
    μ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1} = 1 ∧ ρ₂ {x | ∀ i, IntAt (Q i).q.v (Q i).gl₂ x.1.1} = 1

def LocNorm (Q₀ : QStep S) (m₁ : Measure (GL (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1)) Q₀.k)) (s₁ : Measure (RFJ Q₀.k Q₀.n₁ (Q₀.c + 1 + 1) (σ + 1)))
    (m₂ : Measure (GL (Q₀.n₂ ⊕ Fin (Q₀.c + 1)) Q₀.k)) (s₂ : Measure (R Q₀.k Q₀.n₂ (Q₀.c + 1) (σ + 1))) : Prop :=
  m₁.IsHaarMeasure ∧ m₁ (KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))) = 1 ∧ s₁.IsHaarMeasure ∧
    s₁ {x | x.1 ∈ KO Q₀.k (Q₀.n₁ ⊕ Fin (Q₀.c + 1 + 1))} = 1 ∧ m₂.IsHaarMeasure ∧ m₂ (KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))) = 1 ∧
    s₂.IsHaarMeasure ∧ s₂ {x | x.1 ∈ KO Q₀.k (Q₀.n₂ ⊕ Fin (Q₀.c + 1))} = 1

def levJ {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.J.W (places Q)) :=
  (⨆ i, (Q i).L₁.J.map (Q i).gl₁).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))

def levB {r : ℕ} (Q : Fin r → QStep S) : Subgroup (GlobalTheory.FinPl.grpAt S.B'.V (places Q)) :=
  (⨆ i, (Q i).L₂.J.map (Q i).gl₂).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q))

end GlobalTheory.QVal

namespace GlobalTheory.QVal

def ValQr (D : D7) (r : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : Fin r → QStep S),
    Function.Injective (fun i => (Q i).q.v) →
  ∀ (μ₁ : Measure (GlobalTheory.FinPl.grpAt S.J.W (places Q))) (ρ₁ : Measure ((jacGrp S.J.d).subgroupOf (GlobalTheory.FinPl.grpAt S.J.W (places Q))))
    (μ₂ : Measure (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))
    (ρ₂ : Measure ((besGrp S.B'.d S.B'.o).subgroupOf (GlobalTheory.FinPl.grpAt S.B'.V (places Q)))), Norm Q μ₁ ρ₁ μ₂ ρ₂ →
  ∀ c₁ c₂ f₁ f₂ φ f g h₁ h₂, Hyps Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ →
    Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun x y => integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ x.1 y.1) (value Q c₁ c₂ f₁ f₂ φ f g h₁ h₂)

theorem valQ_of_valQr (D : D7) (h : ∀ r, ValQr D r) : ValQ D := by
  intro ψ hψ σ S r Q hinj P hP μ₁ ρ₁ μ₂ ρ₂ a1 a2 a3 a4 a5 a6 a7 a8 c₁ c₂ hc f₁ f₂ t1 t2 hv φ f hφ hf ht g hg h₁ hh₁ h₂ hh₂
  have e : P = places Q := funext fun v => propext (hP v)
  subst e
  exact h r ψ hψ σ S Q hinj μ₁ ρ₁ μ₂ ρ₂ ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ c₁ c₂ f₁ f₂ φ f g h₁ h₂
    ⟨hc, t1, t2, hv, hφ, hf, ht, hg, hh₁, hh₂⟩

end GlobalTheory.QVal

namespace GlobalTheory.QVal
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

def pint {r : ℕ} (Q : Fin (r + 1) → QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ)
    (f₁ : WO S.B.V S.J.W → ℂ) (f₂ : WO S.J.W S.B'.V → ℂ) (φ : GA D S.B.A → ℂ) (f : GA D S.B'.V → ℂ)
    (g : GA D S.B.V) (h₁ : GA D S.J.W) (h₂ : GA D S.B'.V)
    (x : GlobalTheory.FinPl.grpAt S.J.W (places fun i => Q i.succ) × GL ((Q 0).n₁ ⊕ Fin ((Q 0).c + 1 + 1)) (Q 0).k)
    (y : GlobalTheory.FinPl.grpAt S.B'.V (places fun i => Q i.succ) × GL ((Q 0).n₂ ⊕ Fin ((Q 0).c + 1)) (Q 0).k) : ℂ :=
  integrand Q c₁ c₂ f₁ f₂ φ f g h₁ h₂ (x.1.1 * (Q 0).gl₁ x.2) (y.1.1 * (Q 0).gl₂ y.2)
end GlobalTheory.QVal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfOfIsIdemSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.CongAtIdem

theorem read_rel {A B K E : Type} [CommRing A] [CommRing B] [CommRing K] [CommRing E] {m n : Type} [Fintype m] [Fintype n]
    (t : A →+* B) (φ : B →+* K) (i : E →+* A) (j : E →+* B) (hij : ∀ x, t (i x) = j x) {e : A} (he : φ (t e) = 1)
    (X : Matrix m m A) (Z : Matrix n n A) (γ γ₀ : Matrix m n E) (v : Matrix m n A) (k : ℕ)
    (h : γ₀.map (fun r => e * i r) = X * γ.map (fun r => e * i r) * Z + k • v) (r : m) (s : n) :
    φ ((X.map t * γ.map j * Z.map t - γ₀.map j) r s) = -((k : K) * φ (t (v r s))) := by
  have h1 := congrArg (fun W : Matrix m n A => φ (t (W r s))) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, map_add (f := _), map_sum, map_mul, he,
    one_mul, hij, nsmul_eq_mul, map_natCast] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, h1]
  ring

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem adAt_toEAf_of_isIdemAt {f : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hf : Formalism.L2.NTheta.IsIdemAt f P) : adAt D.host.F P (toEAf D f) = 1 := by
  let ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (afIso D.host.F D.host.E)
  have h1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := fun x =>
    afIso_tmul_one D.host.F D.host.E x
  have h2 : ∀ y, y ∈ intAE D ↔ ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y Q) ≤ 1 := fun y =>
    (GlobalTheory.IdemSupport.mem_intAE_iff y).trans (mem_rInt_iff D.host.F D.host.E _)
  exact GlobalTheory.ChrOff.comp_idem ι h1 h2 hf

theorem adAt_toEAf_of_isIdemSum {e : AE D} {Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    (he : IsIdemSum e Ps) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Ps) :
    adAt D.host.F P (toEAf D e) = 1 := by
  obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
  have h := congrArg (fun z => adAt D.host.F P (toEAf D z)) hae
  simp only [map_mul, adAt_toEAf_of_isIdemAt ha, one_mul] at h
  exact h

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem isIntegral_of_eq {x : D.host.E} (h : ∃ r : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E r = x) :
    IsIntegral ℤ x := by
  obtain ⟨r, rfl⟩ := h
  exact r.2

theorem tmul_one_mem_rInt {x : D.host.E} (hx : IsIntegral ℤ x) :
    x ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨x, ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩)

theorem one_tmul_mem_rInt {α : FiniteAdeleRing (𝓞 D.host.F) D.host.F} (hα : α ∈ intAf D.host.F) :
    (1 : D.host.E) ⊗ₜ[D.host.F] α ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)

theorem exists_den_stdHom (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s,
    ((d : EF D) * toEAf D (v r s) : Formalism.L2.DIV.AfE D.host.F D.host.E) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hint⟩ := GlobalTheory.AdeleBaseChange.exists_nat_mul_integral
    (insert ((a0 : D.host.E))⁻¹ (Finset.image (fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2) Finset.univ))
  have hx0 : IsIntegral ℤ ((d : D.host.E) * ((a0 : D.host.E))⁻¹) := by
    rw [← nsmul_eq_mul]; exact isIntegral_of_eq (hint _ (Finset.mem_insert_self _ _))
  have hG : ∀ k j, IsIntegral ℤ ((d : D.host.E) * S.gram k j) := fun k j => by
    rw [← nsmul_eq_mul]
    exact isIntegral_of_eq (hint _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)))
  refine ⟨d * d, Nat.mul_pos hd hd, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        refine isIntegral_of_eq ⟨y, ?_⟩
        rw [hy, Algebra.smul_def]
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((d : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul
          ((hs k).map (starRingEnd D.host.E).toIntAlgHom) (hG k c)
      have e : ((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((d : D.host.E) * S.gram k c) = (d : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * d * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e]
      exact ((hx0.mul hA).mul (ht r)).mul hsum
    change ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) ∈ _
    have e3 : ((d * d : ℕ) : EF D) * ((a * t r * ∑ k, star (s k) * S.gram k c) ⊗ₜ[D.host.F] α) =
        ((((d * d : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) ⊗ₜ[D.host.F]
          (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] α) := by
      have hc : ((d * d : ℕ) : EF D) = ((d * d : ℕ) : D.host.E) ⊗ₜ[D.host.F] (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
        (map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := D.host.E)
          (B := FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d * d)).symm
      rw [hc]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e3]
    exact mul_mem (tmul_one_mem_rInt hint') (one_tmul_mem_rInt hα)
  | zero => intro r s; simp
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, RingHom.map_add (toEAf D), mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, RingHom.map_neg (toEAf D), mul_neg]; exact neg_mem (hx r s)

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

variable {D : D7}

theorem finM_rfl (V : HSp D) (x : GA D V) : finM V rfl x = (Formalism.L2.Theta.mt V x).map (toEAf D) := by
  simp [finM, finCongr_refl]

theorem mt_mul' (V : HSp D) (x y : GA D V) :
    Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := by
  show (matHom V (x * y)).1 = (matHom V x).1 * (matHom V y).1
  rw [map_mul, Units.val_mul]

theorem mt_one' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem inv_val_eq (V : HSp D) (x : GA D V) (Y : GL (Fin V.rank) (EF D)) (hY : finM V rfl x = Y.1) :
    (Y⁻¹ : GL (Fin V.rank) (EF D)).1 = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
  have h1 : (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1 = 1 := by
    rw [← hY, finM_rfl, ← Matrix.map_mul, ← mt_mul', inv_mul_cancel, mt_one',
      Matrix.map_one _ (map_zero _) (map_one _)]
  calc (Y⁻¹ : GL (Fin V.rank) (EF D)).1
      = ((Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) * Y.1) * (Y⁻¹ : GL (Fin V.rank) (EF D)).1 := by
        rw [h1, Matrix.one_mul]
    _ = (Formalism.L2.Theta.mt V x⁻¹).map (toEAf D) := by
        rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.AdForm.CongAtIdem

namespace GlobalTheory.AdForm.CongAtIdem

theorem cong_at_idem : ∀ {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (e : AE D)
    (Ps : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e Ps → ∃ d : ℕ, 0 < d ∧
    ∀ (g : GA D S) (h : GA D T) (Y : GL (Fin a) (EF D)) (Y' : GL (Fin b) (EF D)), finM S hS g = Y.1 → finM T hT h = Y'.1 →
    ∀ (M : ℕ) (γ γ₀ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (v : WO S T), v ∈ stdHom S T →
      γ₀.map (fun r => e * incA D r) = actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r) + (d * M) • v →
      ∀ P ∈ Ps, ∀ r s, Valued.v (adAt D.host.F P
        ((HMul.hMul (HMul.hMul ((Y'⁻¹ : GL (Fin b) (EF D)).1 : Matrix (Fin b) (Fin b) (EF D))
          (((LinearMap.toMatrix' (toHom S T hS hT γ)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))))
          (Y.1 : Matrix (Fin a) (Fin a) (EF D)) -
          ((LinearMap.toMatrix' (toHom S T hS hT γ₀)).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Matrix (Fin b) (Fin a) (EF D))) r s)) ≤
        Valued.v ((M : ℕ) : P.adicCompletion D.host.E) := by
  intro D S T a b hS hT e Ps he
  subst hS; subst hT
  obtain ⟨d, hd, hden⟩ := exists_den_stdHom S T
  refine ⟨d, hd, ?_⟩
  intro g h Y Y' hY hY' M γ γ₀ v hv hH P hP r s
  rw [← hY, finM_rfl, inv_val_eq T h Y' hY']
  simp only [toHom, LinearMap.toMatrix'_toLin', finCongr_refl, Matrix.reindex_refl_refl]
  rw [actO, inv_inv] at hH
  have key := read_rel (toEAf D) (adAt D.host.F P) (incA D)
    (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (fun _ => rfl)
    (adAt_toEAf_of_isIdemSum he hP) _ _ γ γ₀ v (d * M) hH r s
  have hint : Valued.v (adAt D.host.F P ((d : EF D) * toEAf D (v r s))) ≤ 1 :=
    (mem_rInt_iff D.host.F D.host.E _).1 (hden v hv r s) P
  rw [RingHom.map_mul, map_natCast (adAt D.host.F P)] at hint
  refine (congrArg Valued.v key).trans_le ?_
  rw [Valuation.map_neg, Nat.cast_mul, mul_right_comm, Valuation.map_mul]
  exact mul_le_of_le_one_left' hint

end GlobalTheory.AdForm.CongAtIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem mt_mul (S : HSp D) (g h : GA D S) : mt S (g * h) = mt S g * mt S h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

def locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) : GA D S →* GL Y k where
  toFun g := ⟨F.γ * (mt S g).map q.pr * F.β, F.γ * (mt S g⁻¹).map q.pr * F.β, by
      rw [show F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S g⁻¹).map q.pr * F.β) =
        F.γ * ((mt S g).map q.pr * (F.β * F.γ) * (mt S g⁻¹).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ], by
      rw [show F.γ * (mt S g⁻¹).map q.pr * F.β * (F.γ * (mt S g).map q.pr * F.β) =
        F.γ * ((mt S g⁻¹).map q.pr * (F.β * F.γ) * (mt S g).map q.pr) * F.β by simp only [Matrix.mul_assoc],
        F.βγ, Matrix.mul_one, ← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.mul_one, F.γβ]⟩
  map_one' := by
    ext1; simp only [mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, F.γβ]; rfl
  map_mul' g h := by
    ext1
    change F.γ * (mt S (g * h)).map q.pr * F.β = F.γ * (mt S g).map q.pr * F.β * (F.γ * (mt S h).map q.pr * F.β)
    rw [mt_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem locHom_val (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) :
    (locHom q S F g).val = F.γ * (mt S g).map q.pr * F.β := rfl

theorem eq_locHom_iff (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) (g : GA D S) (x : GL Y k) :
    (mt S g).map q.pr = F.β * x.val * F.γ ↔ x = locHom q S F g := by
  constructor
  · intro h
    ext1
    rw [locHom_val, h]
    simp only [Matrix.mul_assoc, F.γβ, Matrix.mul_one]
    rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]
  · rintro rfl
    rw [locHom_val]
    simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

theorem continuous_locHom (q : SplitPt D k) (S : HSp D) (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    Continuous (locHom q S F) := by
  rw [Units.continuous_iff]
  have hm : Continuous fun g : GA D S => (mt S g).map q.pr :=
    (GlobalTheory.MixModel.continuous_mt S).matrix_map q.cont_pr
  refine ⟨(continuous_const.matrix_mul hm).matrix_mul continuous_const, ?_⟩
  have hi : Continuous fun g : GA D S => (mt S g⁻¹).map q.pr :=
    ((GlobalTheory.MixModel.continuous_mt S).comp continuous_inv).matrix_map q.cont_pr
  exact (continuous_const.matrix_mul hi).matrix_mul continuous_const

theorem vol_mul_relIndex {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H H' : Subgroup G) (hle : H' ≤ H)
    (hc : IsCompact (H : Set G)) (ho : IsOpen (H' : Set G)) : μ.real H' * (H'.relIndex H : ℝ) = μ.real H := by
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hle ho
  have ho' : IsOpen ((H'.subgroupOf H : Subgroup H) : Set H) := ho.preimage continuous_subtype_val
  haveI : Finite (H ⧸ H'.subgroupOf H) := (H'.subgroupOf H).quotient_finite_of_isOpen ho'
  haveI : (H'.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hemb : MeasurableEmbedding (H.subtype : H → G) := MeasurableEmbedding.subtype_coe hHo.measurableSet
  have : (μ.comap (H.subtype : H → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  have key := (H'.subgroupOf H).index_mul_measure ho'.measurableSet (μ.comap (H.subtype : H → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (H.subtype : H → G) '' Set.univ = (H : Set G) := by ext x; simp
  have e2 : (H.subtype : H → G) '' ((H'.subgroupOf H : Subgroup H) : Set H) = (H' : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  rw [Subgroup.relIndex, Measure.real, Measure.real, ← key, ENNReal.toReal_mul, mul_comm]
  simp

end GlobalTheory.LevIdx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.AllCombProof

variable {D : D7}

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (h : ∀ x, Q x → P x) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hmono : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (h v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hmono hu), fun e he u hu hh => hf.2.2 e he u (hmono hu) hh⟩

theorem combAt_mono {S T : HSp D} {P Q : Pl D → Prop} (h : ∀ x, P x → Q x) {c : WO S T →₀ ℂ} (hc : CombAt P c) :
    CombAt Q c := fun x hx => GlobalTheory.DisjComb.mxAt_mono h (hc x hx)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  {p : ι → SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_nil {f f' : WO S T → ℂ} : OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {i : ι} {J : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔
      ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

theorem over_unique (hψ : IsStdChar D ψ (-1)) {i : ι} {g f' f'' : WO S T → ℂ}
    (h' : Over ψ (α i) (β i) LS LT g (Ψ i) f') (h'' : Over ψ (α i) (β i) LS LT g (Ψ i) f'') : f' = f'' :=
  ((GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k (p i) n n' ψ hψ S T (α i) (β i) LS LT h'.1 h'.2.1 g h'.2.2.1).1 (Ψ i) h'.2.2.2.1).unique h' h''

theorem overAll_unique (hψ : IsStdChar D ψ (-1)) (J : List ι) : ∀ f f' f'' : WO S T → ℂ,
    OverAll ψ α β LS LT Ψ J f f' → OverAll ψ α β LS LT Ψ J f f'' → f' = f'' := by
  induction J with
  | nil => intro f f' f'' h' h''; rw [overAll_nil.1 h', overAll_nil.1 h'']
  | cons i J ih =>
    intro f f' f'' h' h''
    obtain ⟨g, hg, h'⟩ := overAll_cons.1 h'
    obtain ⟨g', hg', h''⟩ := overAll_cons.1 h''
    obtain rfl := ih f g g' hg hg'
    exact over_unique hψ h' h''

theorem over_comb (hψ : IsStdChar D ψ (-1)) {i : ι} (hu : (p i).UnitAA) {Q : Pl D → Prop} (hQ : ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) {g f : WO S T → ℂ} (h : Over ψ (α i) (β i) LS LT g (Ψ i) f) :
    Over ψ (α i) (β i) LS LT (comb ψ S T d g) (Ψ i) (comb ψ S T d f) := by
  obtain ⟨c, hc, hcf⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ hu S T (α i) (β i) LS LS LT LT h.1 h.2.1 h.1 h.2.1).2
    (Ψ i) h.2.2.2.1
  have M := GlobalTheory.DisjComb.main D ψ hψ S T Q (· = (p i).v) (fun x hx hx' => hQ (hx' ▸ hx))
  have hf : f = comb ψ S T c g := over_unique hψ h (hcf g h.2.2.1)
  rw [hf, M.1 d c hd hc g]
  exact hcf _ ((M.2.1 d hd).2 LS LT g h.2.2.1)

theorem overAll_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) {Q : Pl D → Prop} (hQ : ∀ i, ¬ Q (p i).v)
    {d : WO S T →₀ ℂ} (hd : CombAt Q d) (J : List ι) (f : WO S T → ℂ) : ∀ f', OverAll ψ α β LS LT Ψ J f f' →
      OverAll ψ α β LS LT Ψ J (comb ψ S T d f) (comb ψ S T d f') := by
  induction J with
  | nil => intro f' h; rw [overAll_nil.1 h]; exact overAll_nil.2 rfl
  | cons i J ih =>
    intro f' h
    obtain ⟨g, hg, h⟩ := overAll_cons.1 h
    exact overAll_cons.2 ⟨_, ih g hg, over_comb hψ (hu i) (hQ i) hd h⟩

theorem exists_comb (hψ : IsStdChar D ψ (-1)) (hu : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (hLS : IsSelfDualC S LS) (hLT : IsSelfDualC T LT) (hΨ : ∀ i, Ψ i ∈ SB (Matrix n n' k)) (J : List ι) (hJ : J.Nodup) :
    ∃ c : WO S T →₀ ℂ, CombAt (fun x => ∃ i ∈ J, x = (p i).v) c ∧
      ∀ f, (∀ i ∈ J, Vac ψ S T LS LT (· = (p i).v) f) → OverAll ψ α β LS LT Ψ J f (comb ψ S T c f) := by
  induction J with
  | nil =>
    exact ⟨Finsupp.single 0 1, OffTest.combAt_single_zero _ _, fun f _ => overAll_nil.2 (OffTest.comb_single_zero ψ S T f)⟩
  | cons i J ih =>
    obtain ⟨hi, hJ'⟩ := List.nodup_cons.1 hJ
    obtain ⟨c', hc', hf'⟩ := ih hJ'
    obtain ⟨c, hc, hcf⟩ := (GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination D k (p i) n n' ψ hψ (hu i) S T (α i) (β i) LS LS LT LT hLS hLT hLS hLT).2
      (Ψ i) (hΨ i)
    have M := GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ∃ j ∈ J, x = (p j).v) (· = (p i).v) (by
      rintro x ⟨j, hj, rfl⟩ hx
      exact hi (hinj hx ▸ hj))
    obtain ⟨c'', hc'', heq⟩ := M.2.2.2.1 c c' (combAt_mono (fun x hx => Or.inr hx) hc)
      (combAt_mono (fun x hx => Or.inl hx) hc')
    refine ⟨c'', combAt_mono ?_ hc'', fun f hf => ?_⟩
    · rintro x (⟨j, hj, rfl⟩ | rfl)
      · exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
      · exact ⟨i, List.mem_cons_self, rfl⟩
    · rw [heq]
      exact overAll_cons.2 ⟨_, hf' f fun j hj => hf j (List.mem_cons_of_mem _ hj),
        hcf _ ((M.2.1 c' hc').2 LS LT f (hf i List.mem_cons_self))⟩

end GlobalTheory.FinPl.AllCombProof

namespace GlobalTheory.FinPl


open AllCombProof in
theorem allComb : ∀ D : D7, AllComb D := by
  intro D k _ _ _ _ ι p I P hP n n' _ _ _ _ ψ hψ S T α β LS LT hLS hLT Ψ
  refine ⟨fun hΨ => ?_, overAll_unique hψ I, fun d hd f hf => ⟨?_, ?_⟩⟩
  · obtain ⟨c, hc, hf⟩ := exists_comb (α := α) (β := β) hψ hP.unit hP.inj hLS hLT hΨ I hP.nodup
    refine ⟨c, combAt_mono ?_ hc, fun f h => hf f fun i _ => vac_mono ?_ h⟩
    · rintro x ⟨i, -, rfl⟩
      exact (hP.mem _).2 ⟨i, rfl⟩
    · rintro x rfl
      exact (hP.mem _).2 ⟨i, rfl⟩
  · exact ((GlobalTheory.DisjComb.main D ψ hψ S T (fun x => ¬ P x) P fun x hx => hx).2.1 d hd).2 LS LT f hf
  · exact overAll_comb hψ hP.unit (fun i h => h ((hP.mem _).2 ⟨i, rfl⟩)) hd I f

end GlobalTheory.FinPl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataAsCombinationsAtSplitPlacesProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataAsCombinationsAtSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.AllComb D := by
  first | exact @GlobalTheory.FinPl.allComb | exact GlobalTheory.FinPl.allComb | (intros; apply GlobalTheory.FinPl.allComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairSchrodingerFunctionContinuousIntegrabStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledPairSchrodingerFunction_continuous_integrable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → Continuous (sch ψ A B ν 𝓨 f) ∧ Integrable (sch ψ A B ν 𝓨 f) ν := by
  first | exact @GlobalTheory.Core.Rk.SchInt.sch_continuous_integrable | exact GlobalTheory.Core.Rk.SchInt.sch_continuous_integrable | (intros; apply GlobalTheory.Core.Rk.SchInt.sch_continuous_integrable <;> assumption)
end
