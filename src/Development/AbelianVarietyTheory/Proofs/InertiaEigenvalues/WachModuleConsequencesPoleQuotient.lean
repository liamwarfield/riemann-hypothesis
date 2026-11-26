module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdGammaSubJumpUnitsAnnihilatesQuotient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJump
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJump
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpVec

theorem exists_letter_of_jump : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ, IsJumpV ((D.loc l).PD K) T.ρ τ a → ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∉ FilAt ((D.loc l).PD K) T τ (a + 1) := by
  intro D HW l _ K s LL h T hC i ζ τ hPt a hJ
  obtain ⟨-, hemb, ι, hComp⟩ := (GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hPt
  obtain ⟨-, -, -, hc, hc0⟩ := GlobalTheory.NL.Points.points D HW l K s LL h
  have hC3 := (GlobalTheory.NL.CompD.component_tied (D.locT l) K LL T hc hc0 hC τ ι hComp.2.2 _ hemb).2.2.1
  have hlt : FildR ((D.loc l).PD K) T.ρ τ (a + 1) < FildR ((D.loc l).PD K) T.ρ τ a :=
    lt_of_le_of_ne (GlobalTheory.DeRhamCompare.FildR_succ_le _ _ τ a) hJ
  obtain ⟨w, hwa, hwa1⟩ := SetLike.exists_of_lt hlt
  obtain ⟨d, hd, hdw⟩ := hC3 w hwa.1
  refine ⟨d, hd, ?_, ?_⟩
  · have : ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d =
        w + (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hwa hdw
  · intro hmem
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    have hdis := GlobalTheory.Per.FilLetUnram.iSupIndep_DdRE ((D.loc l).PD K) T.ρ τ
    have hD : w - y ∈ DdRE ((D.loc l).PD K) T.ρ τ := Submodule.sub_mem _ hwa.1 hy.1
    have hS : w - y ∈ ⨆ (τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (_ : τ' ≠ τ), DdRE ((D.loc l).PD K) T.ρ τ' := by
      have : w - y = z - (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d - w) := by
        rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hz hdw
    have h0 : w - y = 0 := Submodule.disjoint_def.1 hdis _ hD hS
    have : w = y := sub_eq_zero.1 h0
    exact hwa1 (this ▸ hy)

end GlobalTheory.NL.JumpVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLetterOfHodgeJumpStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystallineLetter_of_hodgeJump : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → ∀ a : ℤ, IsJumpV ((D.loc l).PD K) T.ρ τ a → ∃ d ∈ Di (HW l) h T i, ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∈ FilAt ((D.loc l).PD K) T τ a ∧ ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) d ∉ FilAt ((D.loc l).PD K) T τ (a + 1) := by
  first | exact @GlobalTheory.NL.JumpVec.exists_letter_of_jump | exact GlobalTheory.NL.JumpVec.exists_letter_of_jump | (intros; apply GlobalTheory.NL.JumpVec.exists_letter_of_jump <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFinite
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpsFinite


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem jumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ →
    (Jumps (PD := (D.loc l).PD K) T).Finite := by
  intro D HW l _ K s LL h T hcrys
  have hP := GlobalTheory.NL.Points.points D HW l K s LL h
  have hfin : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hP.2.2.2.1]
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    exact Module.finrank_pos.ne'
  have hsub : Jumps (PD := (D.loc l).PD K) T ⊆
      ⋃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, {a | IsJumpV ((D.loc l).PD K) T.ρ τ a} := by
    rintro a ⟨τ, hτ⟩
    exact Set.mem_iUnion.2 ⟨τ, hτ⟩
  refine (Set.finite_iUnion fun τ => ?_).subset hsub
  obtain ⟨i, ζ, hpt⟩ := hP.2.2.1 τ
  obtain ⟨-, hemb, ι, hcomp⟩ := hP.2.1 i ζ τ hpt
  have hrank := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l _ _
    (D.locT l) K LL T.V T.ρ).1 hP.2.2.2.2 hcrys (((HW l).W K s LL h).emb i)
  set Dm := Di (HW l) h T i with hDm
  have hDfin : FiniteDimensional ↥LL.1 ↥Dm := by
    rcases Nat.eq_zero_or_pos (Module.finrank ↥LL.1 T.V) with h0 | hpos
    · have hV : Subsingleton T.V := Module.finrank_zero_iff.1 h0
      have hVB : Subsingleton (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := by
        refine ⟨fun x y => ?_⟩
        have hz : ∀ z : T.V ⊗[ℚ_[l]] (D.loc l).R.B, z = 0 := by
          intro z
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add x y hx hy => rw [hx, hy, add_zero]
        rw [hz x, hz y]
      infer_instance
    · exact Module.finite_of_finrank_pos (hrank ▸ hpos)
  let S : ℤ → Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := fun a =>
    Dm ⊓ (FilAt ((D.loc l).PD K) T τ a).comap (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))
  have hSanti : Antitone S := by
    refine antitone_int_of_succ_le fun a => inf_le_inf_left _ (Submodule.comap_mono ?_)
    exact sup_le_sup_right (GlobalTheory.Pst.filDR_succ_le ((D.loc l).PD K) T.ρ τ a) _
  let f : ℤ → ℕ := fun a => Module.finrank ↥LL.1 ↥(S a)
  have hfS : ∀ a, Module.finrank ↥LL.1 ↥(S a) ≤ Module.finrank ↥LL.1 ↥Dm := fun a =>
    Submodule.finrank_mono inf_le_left
  have hlt : ∀ a b, IsJumpV ((D.loc l).PD K) T.ρ τ a → a < b → f b < f a := by
    intro a b ha hab
    obtain ⟨d, hd, h1, h2⟩ := GlobalTheory.T.exists_crystallineLetter_of_hodgeJump D HW l K s LL h T hcrys i ζ τ hpt a ha
    have hle : S b ≤ S (a + 1) := hSanti (by omega)
    have hlt' : S (a + 1) < S a := by
      refine lt_of_le_of_ne (hSanti (by omega)) fun heq => h2 ?_
      have : d ∈ S a := ⟨hd, h1⟩
      rw [← heq] at this
      exact this.2
    haveI : FiniteDimensional ↥LL.1 ↥(S a) :=
      Submodule.finiteDimensional_of_le (inf_le_left : S a ≤ Dm)
    exact lt_of_le_of_lt (Submodule.finrank_mono hle) (Submodule.finrank_lt_finrank_of_lt hlt')
  refine Set.Finite.of_finite_image (f := f) ((Set.finite_Iic (Module.finrank ↥LL.1 ↥Dm)).subset ?_) ?_
  · rintro _ ⟨a, -, rfl⟩
    exact hfS a
  · intro a ha b hb hab
    rcases lt_trichotomy a b with hh | hh | hh
    · exact absurd hab (hlt a b ha hh).ne'
    · exact hh
    · exact absurd hab (hlt b a hb hh).ne

end GlobalTheory.NL.JumpsFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFiniteStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (Jumps (PD := (D.loc l).PD K) T).Finite := by
  first | exact @GlobalTheory.NL.JumpsFinite.jumps_finite | exact GlobalTheory.NL.JumpsFinite.jumps_finite | (intros; apply GlobalTheory.NL.JumpsFinite.jumps_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaEigenvalueOnWachLatticeQPowerQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConvXPowMul
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.Approx

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_sum (e : PowerSeries L) (f : ℤ → M) (k : ℤ) (N : ℕ)
    (hN : ∀ j : ℕ, N ≤ j → f (k - j) = 0) :
    conv e f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j e • f (k - j) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hc
  exact hj (by rw [hN j (not_lt.1 hc), smul_zero])

theorem exists_bound {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (k : ℤ) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → f (k - j) = 0 := by
  refine ⟨(k - m₀ + 1).toNat, fun j hj => hf _ ?_⟩
  have h1 := Int.self_le_toNat (k - m₀ + 1)
  have h2 : (((k - m₀ + 1).toNat : ℕ) : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  omega

theorem conv_add {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (e e' : PowerSeries L) :
    conv (e + e') f = conv e f + conv e' f := by
  funext k
  obtain ⟨N, hN⟩ := exists_bound hf k
  simp only [Pi.add_apply, conv_eq_sum _ f k N hN, map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem conv_smul {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (c : L) (e : PowerSeries L) :
    conv (c • e) f = c • conv e f := by
  funext k
  obtain ⟨N, hN⟩ := exists_bound hf k
  simp only [Pi.smul_apply, conv_eq_sum _ f k N hN, map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem conv_smul_add {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (c : L) (e e' : PowerSeries L) :
    conv (c • (e + e')) f = c • conv e f + c • conv e' f := by
  rw [conv_smul hf, conv_add hf, smul_add]

theorem conv_X_pow_mul {f : ℤ → M} {m₀ : ℤ} (hf : ∀ k < m₀, f k = 0) (m : ℕ) (p : PowerSeries L)
    (k : ℤ) : conv (PowerSeries.X ^ m * p) f k = conv p f (k - m) := by
  obtain ⟨N, hN⟩ := exists_bound hf (k - m)
  have hN' : ∀ j : ℕ, m + N ≤ j → f (k - j) = 0 := by
    intro j hj
    have := hN (j - m) (by omega)
    rwa [show k - (m : ℤ) - ((j - m : ℕ) : ℤ) = k - j by push_cast [show m ≤ j by omega]; ring] at this
  rw [conv_eq_sum _ f k _ hN', conv_eq_sum _ f (k - m) N hN, Finset.sum_range_add]
  rw [Finset.sum_eq_zero, zero_add]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_X_pow_mul', if_pos (by omega), show m + j - m = j by omega]
    congr 2
    push_cast
    ring
  · intro j hj
    rw [Finset.mem_range] at hj
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]

theorem combine {ι : Type} [Fintype ι] (F : ι → ℤ → M) (m₀ : ι → ℤ) (hbd : ∀ j, ∀ k < m₀ j, F j k = 0)
    (c : L) (e p : ι → PowerSeries L) (m : ℕ) (k : ℤ) :
    (∑ j, conv (c • (e j + PowerSeries.X ^ m * p j)) (F j)) k - c • (∑ j, conv (e j) (F j)) k =
      (∑ j, c • conv (p j) (F j)) (k - m) := by
  simp only [fun j => conv_smul_add (hbd j) c (e j) (PowerSeries.X ^ m * p j), Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, Finset.sum_add_distrib, Finset.smul_sum, fun j => conv_X_pow_mul (hbd j) m (p j) k]
  abel

end Series


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem approx : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∀ g ∈ Lat C h T i ζ, ∀ m : ℕ, ∃ (n : ↥(W.N T)) (c : ↥LL.1), c ≠ 0 ∧ ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ n j - c • g j = f (j - m) := by
  intro D HW F Cm l _ K s LL h W C T hT i ζ hζ g hg m
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := ⟨s, hζ⟩
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  have hFull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ
  obtain ⟨hsm, hB⟩ := GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ hζ' hFull
  obtain ⟨-, hspan, -⟩ := hB _ nb
  obtain ⟨e, rfl⟩ := hspan g hg
  have hW := (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).2.2.1 i ζ hζ'
  choose a c hc hdiv using fun j => hW (e j) m
  choose p hp using hdiv
  haveI := LL.2
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ↥(OL LL)) c
  have ho : ∀ j, ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = (b : ↥(OL LL)) • c j :=
    fun j => RingHom.mem_rangeS.1 (hb j)
  choose o ho using ho
  obtain ⟨cc, hccd⟩ : ∃ x : ↥LL.1, x = algebraMap ↥(OL LL) ↥LL.1 (b : ↥(OL LL)) := ⟨_, rfl⟩
  have hcc : cc ≠ 0 := hccd ▸ IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have ho' : ∀ j, algebraMap ↥(OL LL) ↥LL.1 (o j) = cc * c j := by
    intro j
    rw [ho j, hccd, Algebra.smul_def]
  choose m0 hm0 using fun j => (C.C K s LL h).tie.levB_supp T i ζ (nb j)
  have hlev : ∀ j, W.lev i ζ (o j • a j) = cc • (e j + PowerSeries.X ^ m * p j) := by
    intro j
    rw [map_smul, ← algebraMap_smul ↥LL.1 (o j), ho' j, mul_smul, ← hp j, add_sub_cancel]
  have hbd : ∀ j, ∀ k < m0 j, ex C h T i ζ (nb j) k = 0 := hm0
  have hexn : ex C h T i ζ (∑ j, (o j • a j) • nb j) =
      ∑ j, conv (cc • (e j + PowerSeries.X ^ m * p j)) (ex C h T i ζ (nb j)) := by
    have := map_sum ((C.C K s LL h).tie.levB T i ζ) (fun j => (o j • a j) • nb j) Finset.univ
    refine this.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [← hlev j]
    exact hsm _ _
  refine ⟨∑ j, (o j • a j) • nb j, cc, hcc, ∑ j, cc • conv (p j) (ex C h T i ζ (nb j)),
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p j, nb j, rfl⟩),
    fun k => ?_⟩
  rw [hexn]
  exact combine _ m0 hbd cc e p m k

end GlobalTheory.NL.Approx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaEigenvalueOnWachLatticeQPowerQuotient
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.IntegralScalarUnits

def GoodP {L M : Type} [Field L] [AddCommGroup M] [Module L M] (Sub : ℤ → Submodule L M) (y : ℕ)
    (k : ℤ) (d : M) (f : ℤ → M) (lam : L) : Prop :=
  (∃ m : ℤ, ∀ j < m, f j = 0) ∧ (∀ j, f j ∈ Sub j) ∧ (∀ j < k, f j ∈ Sub (j - y)) ∧
    f k - lam • d ∈ Sub (k - y)

theorem goodP_conv_sub_smul {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M]
    (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M) (hS : Monotone Sub) (y : ℕ) (k : ℤ)
    (d : M) (f : ℤ → M) (lam c' : L) (hf : GoodP Sub y k d f lam) :
    GoodP Sub y k d (conv w (fun m => u ^ m • f m) - c' • f)
      ((PowerSeries.constantCoeff w * u ^ k - c') * lam) := by
  obtain ⟨hb, h1, h2, h3⟩ := hf
  obtain ⟨t1, t2, t3, t4⟩ := GlobalTheory.NL.Twist.tri w u Sub hS y f hb h1 k h2
  obtain ⟨m1, hm1⟩ := t1
  obtain ⟨m2, hm2⟩ := hb
  refine ⟨⟨min m1 m2, fun j hj => ?_⟩, fun j => ?_, fun j hj => ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply]
    rw [hm1 j (lt_of_lt_of_le hj (min_le_left _ _)), hm2 j (lt_of_lt_of_le hj (min_le_right _ _)),
      smul_zero, sub_zero]
  · exact Submodule.sub_mem _ (t2 j) (Submodule.smul_mem _ _ (h1 j))
  · exact Submodule.sub_mem _ (t3 j hj) (Submodule.smul_mem _ _ (h2 j hj))
  · have e : (conv w (fun m => u ^ m • f m) - c' • f) k -
        ((PowerSeries.constantCoeff w * u ^ k - c') * lam) • d =
        (conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k) +
          (PowerSeries.constantCoeff w * u ^ k - c') • (f k - lam • d) := by
      simp only [Pi.sub_apply, Pi.smul_apply]
      module
    rw [e]
    exact Submodule.add_mem _ t4 (Submodule.smul_mem _ _ h3)

theorem algebraMap_units_zpow {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (v : Oˣ) (m : ℤ) :
    algebraMap O LL ((v ^ m : Oˣ) : O) = (algebraMap O LL (v : O)) ^ m := by
  have e := map_zpow (Units.map (algebraMap O LL : O →* LL)) v m
  calc algebraMap O LL ((v ^ m : Oˣ) : O)
      = ((Units.map (algebraMap O LL : O →* LL) (v ^ m) : LLˣ) : LL) := rfl
    _ = (((Units.map (algebraMap O LL : O →* LL) v) ^ m : LLˣ) : LL) := by rw [e]
    _ = (algebraMap O LL (v : O)) ^ m := by rw [Units.val_zpow_eq_zpow_val]; rfl

theorem algebraMap_units_ne_zero {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (v : Oˣ) :
    algebraMap O LL (v : O) ≠ 0 :=
  (Units.map (algebraMap O LL : O →* LL) v).ne_zero


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 20000000 in
theorem ex_smul_O (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL)
    (hT : IsCrys ((D.loc l).PD K) T.ρ) (i : Let K) (ζ : ↥LL.1) (hprim : IsPrimitiveRoot ζ (l ^ s))
    (c' : ↥(OL LL)) (x : ↥(((HW l).W K s LL h).N T)) :
    ex (Cm l) h T i ζ (c' • x) = algebraMap ↥(OL LL) ↥LL.1 c' • ex (Cm l) h T i ζ x := by
  have hfull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hprim
  have hlin := (GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hprim⟩ hfull).1
  have hx : c' • x = (c' • (1 : AA K LL)) • x := by
    exact (smul_one_smul (AA K LL) c' x).symm
  rw [hx, hlin]
  have key : ∀ q : ℕ, PowerSeries.coeff q (((HW l).W K s LL h).lev i ζ (c' • (1 : AA K LL))) =
      if q = 0 then algebraMap ↥(OL LL) ↥LL.1 c' else 0 := by
    intro q
    rw [map_smul, map_one]
    rcases q with _ | q
    · simp [Algebra.algebraMap_eq_smul_one]
    · simp
  funext m
  simp only [conv, Pi.smul_apply]
  rw [finsum_eq_single _ 0]
  · rw [key]; simp
  · intro q hq
    rw [key, if_neg hq, zero_smul]

theorem goodP_prod {O L M X : Type} [CommRing O] [Field L] [TopologicalSpace L] [Algebra O L]
    [AddCommGroup M] [Module L M] [AddCommGroup X] [Module O X]
    (γ : X →ₗ[O] X) (P : Submodule O X) (hP : ∀ x ∈ P, γ x ∈ P) (E : X → ℤ → M)
    (w : PowerSeries L) (u : L)
    (hE : ∀ x ∈ P, ∀ c : O, E (γ x - c • x) = conv w (fun m => u ^ m • E x m) - algebraMap O L c • E x)
    (Sub : ℤ → Submodule L M) (hS : Monotone Sub) (y : ℕ) (k : ℤ) (d : M) (x₀ : X) (hx₀ : x₀ ∈ P)
    (lam₀ : L) (h₀ : GoodP Sub y k d (E x₀) lam₀) (S : Finset Oˣ) :
    Polynomial.aeval γ (∏ c ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c : O))) x₀ ∈ P ∧
    GoodP Sub y k d (E (Polynomial.aeval γ (∏ c ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c : O))) x₀))
      (lam₀ * ∏ c ∈ S, (PowerSeries.constantCoeff w * u ^ k - algebraMap O L (c : O))) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ⟨hx₀, h₀⟩
  | insert c S hc ih =>
    obtain ⟨hm, hg⟩ := ih
    have e : Polynomial.aeval γ (∏ c' ∈ insert c S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀ =
        γ (Polynomial.aeval γ (∏ c' ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀) -
          (c : O) • Polynomial.aeval γ (∏ c' ∈ S, ((Polynomial.X : Polynomial O) - Polynomial.C (c' : O))) x₀ := by
      rw [Finset.prod_insert hc, map_mul, Module.End.mul_apply]
      simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
        Module.algebraMap_end_apply]
    rw [e, Finset.prod_insert hc, mul_left_comm, hE _ hm]
    exact ⟨P.sub_mem (hP _ hm) (P.smul_mem _ hm), goodP_conv_sub_smul w u Sub hS y k d _ _ _ hg⟩

theorem ex_sub {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P} {F : LocFon l P AI H}
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (C : LocCmpT l P AI H F) (h : Good K s LL) (T : Lt K LL)
    (i : Let K) (ζ : ↥LL.1) (x x' : ↥((H.W K s LL h).N T)) :
    ex C h T i ζ (x - x') = ex C h T i ζ x - ex C h T i ζ x' :=
  ((C.C K s LL h).tie.levB T i ζ).map_sub x x'


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 20000000 in
theorem occ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → ∃ x ∈ invN W T (W.Q ^ y), x ∉ W.N T ∧ W.γ T x - (((uU W ^ (-(a + j)) : (↥(OL LL))ˣ) : ↥(OL LL))) • x ∈ W.N T := by
  intro D HW F Cm l _ K s LL h W T hT y hy a ha j hj1 hjy
  classical
  obtain ⟨τ, hτ⟩ := ha
  have hpts := GlobalTheory.NL.Points.points D HW l K s LL h
  obtain ⟨i, ζ, hPt⟩ := hpts.2.2.1 τ
  have hprim : IsPrimitiveRoot ζ (l ^ s) := (hpts.2.1 i ζ τ hPt).1
  obtain ⟨d, hdD, hdA, hdA1⟩ := GlobalTheory.NL.JumpVec.exists_letter_of_jump D HW l K s LL h T hT i ζ τ hPt a hτ
  have hQ := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
  simp only [pow_zero, AlgHom.one_apply] at hQ
  have hJ := GlobalTheory.NL.JumpsFinite.jumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU W ^ (-(p.1 + (p.2 : ℤ))))
  have hFs : ∀ a' ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j' : ℕ, 1 ≤ j' → j' ≤ y → uU W ^ (-(a' + j')) ∈ Fs := by
    intro a' ha' j' h1 h2
    simp only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc, Prod.exists]
    exact ⟨a', j', ⟨ha', h1, h2⟩, rfl⟩
  have hmemInv : ∀ x : W.DD T, x ∈ invN W T (W.Q ^ y) ↔ W.Q ^ y • x ∈ W.N T := by
    intro x
    simp [invN, smulA]
  have hγst := (GlobalTheory.NL.GamQ.gam_Q_pow D HW F Cm l K s LL h T hT y).1
  have hstab : ∀ (S : Finset (↥(OL LL))ˣ) (x : W.DD T), x ∈ invN W T (W.Q ^ y) →
      Polynomial.aeval (W.γ T) (∏ c ∈ S, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x
        ∈ invN W T (W.Q ^ y) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro x hx; simpa using hx
    | insert c S hc ih =>
      intro x hx
      rw [Finset.prod_insert hc, map_mul, Module.End.mul_apply]
      have h1 := ih x hx
      set v := Polynomial.aeval (W.γ T) (∏ c ∈ S, ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x
      simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
      refine Submodule.sub_mem _ ?_ (Submodule.smul_of_tower_mem _ _ h1)
      exact (hmemInv _).2 (hγst v ((hmemInv v).1 h1))
  have hFA : ∀ b : ℤ, FilAt ((D.loc l).PD K) T τ (b + 1) ≤ FilAt ((D.loc l).PD K) T τ b := by
    intro b
    apply sup_le_sup_right
    apply inf_le_inf_left
    rintro _ ⟨x, rfl⟩
    have hle : (((D.loc l).PD K).Fil (b + 1)).restrictScalars ℚ_[l] ≤
        (((D.loc l).PD K).Fil b).restrictScalars ℚ_[l] := ((D.loc l).PD K).Fil_anti b
    refine ⟨AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[↥LL.1] T.V) (Submodule.inclusion hle) x, ?_⟩
    rw [← LinearMap.comp_apply, ← AlgebraTensorModule.map_comp]
    rfl
  have hFAnti : Antitone (FilAt ((D.loc l).PD K) T τ) := antitone_int_of_succ_le hFA
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = (y : ℤ) - a - j := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B, g = Pi.single k d := ⟨_, rfl⟩
  have hlat := GlobalTheory.NL.LatFil.lat_eq_fil D HW F Cm l K s LL h T hT i ζ τ hPt
  have hg : g ∈ Lat (Cm l) h T i ζ := by
    refine (hlat g).2 ⟨⟨k, fun j' hj' => by rw [hgdef]; exact Pi.single_eq_of_ne hj'.ne _⟩, fun j' => ?_⟩
    by_cases hj' : j' = k
    · rw [hj', hgdef, Pi.single_eq_same]
      exact ⟨hdD, hFAnti (show -k ≤ a by omega) hdA⟩
    · simp only [hgdef, Pi.single_eq_of_ne hj', map_zero]
      exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  obtain ⟨n, c, hc, f, hf, hfe⟩ := GlobalTheory.NL.Approx.approx D HW F Cm l K s LL h T hT i ζ hprim g hg y
  obtain ⟨e, he⟩ : ∃ e : W.EE, algebraMap (AA K LL) W.EE (W.Q ^ y) * e = 1 := by
    rw [map_pow]; exact (hQ.pow y).exists_right_inv
  obtain ⟨x₀, hx₀def⟩ : ∃ x₀ : W.DD T, x₀ = e • (n : W.DD T) := ⟨_, rfl⟩
  have hx₀Q : W.Q ^ y • x₀ = (n : W.DD T) := by
    rw [hx₀def, ← smul_assoc, Algebra.smul_def, he, one_smul]
  have hx₀ : x₀ ∈ invN W T (W.Q ^ y) := by rw [hmemInv, hx₀Q]; exact n.2
  have hc₀ : uU W ^ (-(a + j)) ∈ Fs := hFs a ⟨τ, hτ⟩ j hj1 hjy
  obtain ⟨z, hzdef⟩ : ∃ z, z = Polynomial.aeval (W.γ T) (∏ c ∈ Fs.erase (uU W ^ (-(a + j))), ((Polynomial.X : Polynomial ↥(OL LL)) - Polynomial.C (Units.val c))) x₀ := ⟨_, rfl⟩
  have hz : z ∈ invN W T (W.Q ^ y) := hzdef ▸ hstab _ x₀ hx₀
  refine ⟨z, hz, ?_, ?_⟩
  swap
  · have := GlobalTheory.NL.KillLevels.annihilate D HW F Cm l K s LL h T hT y hy Fs hFs x₀ hx₀
    rw [← Finset.mul_prod_erase Fs _ hc₀, map_mul, Module.End.mul_apply, ← hzdef] at this
    simpa only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply] using this
  intro hzN
  have hzQ : W.Q ^ y • z ∈ W.N T := (hmemInv _).1 hz
  obtain ⟨w, hw0, hwE⟩ := (GlobalTheory.NL.GamQ.gam_Q_pow D HW F Cm l K s LL h T hT y).2 i ζ hprim
  have hexsmul := ex_smul_O D HW F Cm l K s LL h T hT i ζ hprim
  obtain ⟨Sub, hSub⟩ : ∃ Sub : ℤ → Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] (D.loc l).R.B),
      Sub = fun m => Di (HW l) h T i ⊓
        (FilAt ((D.loc l).PD K) T τ (-m)).comap (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := ⟨_, rfl⟩
  have hSubMono : Monotone Sub := by
    intro m m' hmm
    rw [hSub]
    exact inf_le_inf_left _ (Submodule.comap_mono (hFAnti (neg_le_neg hmm)))
  have hLatSub : ∀ f ∈ Lat (Cm l) h T i ζ, (∃ m : ℤ, ∀ j < m, f j = 0) ∧ ∀ j, f j ∈ Sub j := by
    intro f hf
    obtain ⟨hb, hj⟩ := (hlat f).1 hf
    refine ⟨hb, fun j => ?_⟩
    rw [hSub]
    exact ⟨(hj j).1, (hj j).2⟩
  have hn := hLatSub _ (Submodule.subset_span ⟨1, n, (GlobalTheory.NL.LatFil.conv_one _).symm⟩)
  have hfS := hLatSub f hf
  have hbase_below : ∀ j' < k, ex (Cm l) h T i ζ n j' ∈ Sub (j' - y) := by
    intro j' hj'
    have e := hfe j'
    rw [hgdef, Pi.single_eq_of_ne hj'.ne, smul_zero, sub_zero] at e
    rw [e]
    exact hfS.2 _
  have hbase_k : ex (Cm l) h T i ζ n k - c • d ∈ Sub (k - y) := by
    have e := hfe k
    rw [hgdef, Pi.single_eq_same] at e
    rw [e]
    exact hfS.2 _
  obtain ⟨E, hEdef⟩ : ∃ E : W.DD T → ℤ → T.V ⊗[ℚ_[l]] (D.loc l).R.B,
      E = fun x => if hx : W.Q ^ y • x ∈ W.N T then ex (Cm l) h T i ζ ⟨_, hx⟩ else 0 := ⟨_, rfl⟩
  have hEval : ∀ (x : W.DD T) (hx : W.Q ^ y • x ∈ W.N T), E x = ex (Cm l) h T i ζ ⟨_, hx⟩ := by
    intro x hx
    rw [hEdef]
    exact dif_pos hx
  have hE : ∀ x ∈ (invN W T (W.Q ^ y)).restrictScalars ↥(OL LL), ∀ c' : ↥(OL LL),
      E (W.γ T x - c' • x) = conv w (fun m => (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ m • E x m) -
        algebraMap ↥(OL LL) ↥LL.1 c' • E x := by
    intro x hx c'
    have hx' : W.Q ^ y • x ∈ W.N T := (hmemInv x).1 hx
    have hγ := hγst x hx'
    have h3 : W.Q ^ y • (W.γ T x - c' • x) ∈ W.N T :=
      (hmemInv _).1 (Submodule.sub_mem _ ((hmemInv _).2 hγ) (Submodule.smul_of_tower_mem _ c' hx))
    have e1 : (⟨_, h3⟩ : ↥(W.N T)) = ⟨_, hγ⟩ - c' • ⟨_, hx'⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, smul_sub]
      rw [smul_comm]
    rw [hEval _ h3, hEval _ hx']
    refine (congrArg (ex (Cm l) h T i ζ) e1).trans ((ex_sub (Cm l) h T i ζ _ _).trans ?_)
    exact congrArg₂ (· - ·) (funext fun m => hwE _ hx' hγ m) (hexsmul c' ⟨_, hx'⟩)
  have hP : ∀ x ∈ (invN W T (W.Q ^ y)).restrictScalars ↥(OL LL), W.γ T x ∈ (invN W T (W.Q ^ y)).restrictScalars ↥(OL LL) :=
    fun x hx => (hmemInv _).2 (hγst x ((hmemInv x).1 hx))
  have hbase : GoodP Sub y k d (E x₀) c := by
    rw [hEval x₀ ((hmemInv _).1 hx₀)]
    have e : (⟨_, (hmemInv _).1 hx₀⟩ : ↥(W.N T)) = n := Subtype.ext hx₀Q
    rw [e]
    exact ⟨hn.1, hn.2, hbase_below, hbase_k⟩
  obtain ⟨-, hzG⟩ := goodP_prod (W.γ T) ((invN W T (W.Q ^ y)).restrictScalars ↥(OL LL)) hP E w
    (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) hE Sub hSubMono y k d x₀ hx₀ c hbase
    (Fs.erase (uU W ^ (-(a + j))))
  rw [← hzdef, hEval z hzQ] at hzG
  obtain ⟨f2, hf2, hf2e⟩ := (GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion D HW F Cm l K s LL h T hT y z hzQ).1 hzN i ζ hprim
  have hkmem : ex (Cm l) h T i ζ ⟨_, hzQ⟩ k ∈ Sub (k - y) := by
    rw [hf2e k]
    exact (hLatSub f2 hf2).2 _
  have hune := algebraMap_units_ne_zero (O := ↥(OL LL)) (LL := ↥LL.1) (W.χΓ W.gam)
  have hu0 : PowerSeries.constantCoeff w * (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ k =
      algebraMap ↥(OL LL) ↥LL.1 ((uU W ^ (-(a + j)) : (↥(OL LL))ˣ) : ↥(OL LL)) := by
    rw [hw0, algebraMap_units_zpow, ← zpow_add₀ hune]
    show _ = (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ (-(a + (j : ℤ)))
    congr 1
    omega
  have hlam : (c * ∏ c' ∈ Fs.erase (uU W ^ (-(a + j))), (PowerSeries.constantCoeff w *
          (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ k -
          algebraMap ↥(OL LL) ↥LL.1 (c' : ↥(OL LL)))) ≠ 0 := by
    refine mul_ne_zero hc (Finset.prod_ne_zero_iff.2 fun c' hc' => ?_)
    rw [hu0, sub_ne_zero]
    intro he
    exact (Finset.ne_of_mem_erase hc') (Units.ext (Subtype.val_injective he)).symm
  have hlamd := Submodule.sub_mem _ hkmem hzG.2.2.2
  rw [sub_sub_cancel] at hlamd
  have hdS := Submodule.smul_mem _ (c * ∏ c' ∈ Fs.erase (uU W ^ (-(a + j))), (PowerSeries.constantCoeff w *
          (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL))) ^ k -
          algebraMap ↥(OL LL) ↥LL.1 (c' : ↥(OL LL))))⁻¹ hlamd
  rw [inv_smul_smul₀ hlam, hSub] at hdS
  exact hdA1 (hFAnti (show a + 1 ≤ -(k - (y : ℤ)) by omega) (Submodule.mem_inf.1 hdS).2)

end GlobalTheory.NL.IntegralScalarUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaEigenvalueOnWachLatticeQPowerQuotientStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, 1 ≤ y → ∀ a ∈ Jumps (PD := (D.loc l).PD K) T, ∀ j : ℕ, 1 ≤ j → j ≤ y → ∃ x ∈ invN W T (W.Q ^ y), x ∉ W.N T ∧ W.γ T x - (((uU W ^ (-(a + j)) : (↥(OL LL))ˣ) : ↥(OL LL))) • x ∈ W.N T := by
  first | exact @GlobalTheory.NL.IntegralScalarUnits.occ | exact GlobalTheory.NL.IntegralScalarUnits.occ | (intros; apply GlobalTheory.NL.IntegralScalarUnits.occ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystalline
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystalline
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.QuoFree

theorem finite_of_killed {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
    [Module A M] [Module R M] [IsScalarTower R A M] [hM : Module.Finite A M] (q : A)
    (hq : ∀ m : M, q • m = 0) (F : Finset A)
    (hF : ∀ a : A, ∃ c, a - q * c ∈ Submodule.span R (F : Set A)) : Module.Finite R M := by
  obtain ⟨Gs, hG⟩ := hM.fg_top
  set P := Submodule.span R (Set.image2 (· • ·) (F : Set A) (Gs : Set M)) with hPdef
  have key : ∀ b ∈ Submodule.span R (F : Set A), ∀ g ∈ Gs, b • g ∈ P := by
    intro b hb g hg
    induction hb using Submodule.span_induction with
    | mem f hf => exact Submodule.subset_span ⟨f, hf, g, hg, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
    | smul r x _ hx => rw [smul_assoc]; exact Submodule.smul_mem _ r hx
  have hsplit : ∀ (a : A) (g : M), g ∈ Gs → a • g ∈ P := by
    intro a g hg
    obtain ⟨c, hc⟩ := hF a
    have : a • g = (a - q * c) • g := by
      rw [sub_smul, mul_comm, mul_smul, hq, smul_zero, sub_zero]
    rw [this]
    exact key _ hc g hg
  let P' : Submodule A M :=
    { carrier := P
      add_mem' := fun ha hb => P.add_mem ha hb
      zero_mem' := P.zero_mem
      smul_mem' := by
        intro a m hm
        induction hm using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨f, hf, g, hg, rfl⟩ := hx
          change a • (f • g) ∈ P
          rw [← mul_smul]
          exact hsplit _ g hg
        | zero => simp
        | add x y _ _ hx hy => rw [smul_add]; exact P.add_mem hx hy
        | smul r x _ hx => rw [smul_comm]; exact P.smul_mem r hx }
  have htop : P = ⊤ := by
    refine eq_top_iff.2 fun m _ => ?_
    have hm : m ∈ Submodule.span A (Gs : Set M) := by rw [hG]; trivial
    have hle : Submodule.span A (Gs : Set M) ≤ P' := Submodule.span_le.2 fun g hg => by
      have := hsplit 1 g hg
      rwa [one_smul] at this
    exact hle hm
  refine ⟨?_⟩
  rw [← htop]
  exact Submodule.fg_span (Set.Finite.image2 _ F.finite_toSet Gs.finite_toSet)

theorem coe_poly_eq_sum {O : Type} [CommRing O] (D : ℕ) (r : Polynomial O) (hr : r.degree < D) :
    (r : PowerSeries O) = ∑ k ∈ Finset.range D, r.coeff k • (PowerSeries.X : PowerSeries O) ^ k := by
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.coeff_coe, map_sum, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with hm
  · rfl
  · exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr (by exact_mod_cast not_lt.1 hm))

theorem div_letters {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (n : ℕ) [NeZero n] (g : PowerSeries O)
    (hg : g.map (IsLocalRing.residue O) ≠ 0) :
    ∃ F : Finset (LetA O n), ∀ a : LetA O n, ∃ c,
      a - (fun _ => g) * c ∈ Submodule.span O (F : Set (LetA O n)) := by
  classical
  have H : g.IsWeierstrassDivisor := PowerSeries.IsWeierstrassDivisor.of_map_ne_zero hg
  set D := (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat
  refine ⟨(Finset.univ ×ˢ Finset.range D).image
    (fun p : ZMod n × ℕ => (Pi.single p.1 ((PowerSeries.X : PowerSeries O) ^ p.2) : LetA O n)), ?_⟩
  intro a
  refine ⟨fun i => H.div (a i), ?_⟩
  have hdecomp : a - (fun _ => g) * (fun i => H.div (a i)) =
      ∑ i : ZMod n, ∑ k ∈ Finset.range D,
        (H.mod (a i)).coeff k • (Pi.single i ((PowerSeries.X : PowerSeries O) ^ k) : LetA O n) := by
    funext j
    have hd := H.isWeierstrassDivisionAt_div_mod (a j)
    rw [Pi.sub_apply, Pi.mul_apply]
    rw [show a j - g * H.div (a j) = ((H.mod (a j) : Polynomial O) : PowerSeries O) from
      sub_eq_iff_eq_add'.2 hd.eq_mul_add]
    rw [coe_poly_eq_sum D _ hd.degree_lt, Finset.sum_apply,
      Finset.sum_eq_single j]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_same]
    · intro b _ hb
      rw [Finset.sum_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
    · simp
  rw [hdecomp]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k hk =>
    Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image, Finset.coe_product, Finset.coe_univ, Set.mem_image, Set.mem_prod,
    Set.mem_univ, true_and, Finset.mem_coe, Finset.mem_range]
  exact ⟨(i, k), Finset.mem_range.1 hk, rfl⟩

theorem dvd_pow_of_nonunit {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {c p : O} (hc : c ≠ 0) (hp : ¬ IsUnit p) : ∃ k : ℕ, c ∣ p ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : ϖ ∣ p := by
    have : p ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hp
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  exact ⟨k, (Units.mul_left_dvd).2 (pow_dvd_pow_of_dvd h1 k)⟩

theorem QQ_pow_map_ne {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (hl : ¬ IsUnit ((l : ℕ) : O)) (s : ℕ) (hs : 1 ≤ s) (y : ℕ) :
    (GlobalTheory.Cyc.QQ l O s ^ y).map (IsLocalRing.residue O) ≠ 0 := by
  obtain ⟨b, hb⟩ := (GlobalTheory.Cyc.XX_QQ_properties l O s hs).2.2.2.1
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 hl)
  have hl1 : ((l : ℕ) : PowerSeries (IsLocalRing.ResidueField O)) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), hl0, map_zero]
  rw [map_pow, hb, map_add (f := _), map_mul, map_natCast, map_pow, PowerSeries.map_X, hl1, zero_mul, add_zero,
    ← pow_mul]
  exact pow_ne_zero _ PowerSeries.X_ne_zero

end GlobalTheory.NL.QuoFree

namespace GlobalTheory.NL.QuoFree

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem torsionFree_quo [IsDomain O] [IsDiscreteValuationRing O] (hp : ¬ IsUnit ((PD.p : ℕ) : O))
    (T : LocLat G Qp LL O) (hsat : wachSaturated W T) (S : Submodule (LetA O n) (W.DD T)) :
    Module.IsTorsionFree O (quo W T S (W.N T)) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c z hz => ?_
  rcases eq_or_ne c 0 with hc | hc
  · exact Or.inl hc
  right
  induction z using Submodule.Quotient.induction_on with
  | H x =>
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul_of_tower] at hz ⊢
  obtain ⟨k, d, hd⟩ := dvd_pow_of_nonunit hc hp
  refine hsat (x : W.DD T) ⟨k, ?_⟩
  rw [GlobalTheory.NL.Isog.pow_smul_eq, hd, mul_comm, mul_smul, ← algebraMap_smul (LetA O n) d]
  exact (W.N T).smul_mem _ hz

theorem finite_quo (T : LocLat G Qp LL O) (q : LetA O n)
    (hq : IsUnit (algebraMap (LetA O n) W.EE q)) (F : Finset (LetA O n))
    (hF : ∀ a : LetA O n, ∃ c, a - q * c ∈ Submodule.span O (F : Set (LetA O n))) :
    Module.Finite O (quo W T (invN W T q) (W.N T)) := by
  set u : W.EE := ↑(hq.unit⁻¹)
  have hinv : ∀ x : W.DD T, q • (u • x) = x := by
    intro x
    rw [← algebraMap_smul W.EE q (u • x), smul_smul]
    have : algebraMap (LetA O n) W.EE q * u = 1 := hq.mul_val_inv
    rw [this, one_smul]
  let φu : W.DD T →ₗ[LetA O n] W.DD T := (LinearMap.lsmul W.EE (W.DD T) u).restrictScalars (LetA O n)
  have hS : invN W T q = (W.N T).map φu := by
    ext z
    constructor
    · intro hz
      refine ⟨q • z, hz, ?_⟩
      change u • (q • z) = z
      rw [← algebraMap_smul W.EE q z, smul_smul, mul_comm, hq.mul_val_inv, one_smul]
    · rintro ⟨x, hx, rfl⟩
      change q • (u • x) ∈ W.N T
      rw [hinv]
      exact hx
  haveI : Module.Finite (LetA O n) ↥(invN W T q) := by
    rw [hS]
    exact Module.Finite.iff_fg.2 ((W.N_fg T).map φu)
  haveI : Module.Finite (LetA O n) (quo W T (invN W T q) (W.N T)) :=
    Module.Finite.quotient (LetA O n) _
  refine finite_of_killed q (fun m => ?_) F hF
  induction m using Submodule.Quotient.induction_on with
  | H x =>
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul_of_tower]
  exact x.2

end Generic


set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 4000000 in
theorem quo_free_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, Module.Free ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) ∧ Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) := by
  intro D HW F l _ K s LL h W T hT y
  obtain ⟨hdvr, hcomp, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  have := hdvr
  have := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hQ : ∀ i, W.Q i = GlobalTheory.Cyc.QQ l ↥(OL LL) s := by
    obtain ⟨_, _, _, _, _, hQ, _⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
    exact hQ
  have hQy : W.Q ^ y = fun _ => GlobalTheory.Cyc.QQ l ↥(OL LL) s ^ y := by
    funext i
    rw [Pi.pow_apply, hQ]
  have hunit : IsUnit (algebraMap (AA K LL) W.EE (W.Q ^ y)) := by
    have := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    rw [pow_zero, AlgHom.one_apply] at this
    rw [map_pow]
    exact this.pow y
  have hp : ¬ IsUnit ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) := by
    rw [(D.loc l).PD_p K]
    exact hl
  have hsat := (GlobalTheory.NL.Isog.saturated_and_isogeny_invariant D HW F l K s LL h).1 T hT
  have := hcomp
  obtain ⟨Fs, hFs⟩ := div_letters (Module.finrank ℚ_[l] ↥(K0 K)) (GlobalTheory.Cyc.QQ l ↥(OL LL) s ^ y)
    (QQ_pow_map_ne hl s h.1 y)
  have hfin : Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) :=
    finite_quo W T (W.Q ^ y) hunit Fs (by rw [hQy]; exact hFs)
  have := torsionFree_quo W hp T hsat (invN W T (W.Q ^ y))
  exact ⟨Module.free_of_finite_type_torsion_free', hfin⟩

end GlobalTheory.NL.QuoFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleInverseQuotientFreeFiniteCrystallineStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ y : ℕ, Module.Free ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) ∧ Module.Finite ↥(OL LL) (quo W T (invN W T (W.Q ^ y)) (W.N T)) := by
  first | exact @GlobalTheory.NL.QuoFree.quo_free_finite | exact GlobalTheory.NL.QuoFree.quo_free_finite | (intros; apply GlobalTheory.NL.QuoFree.quo_free_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotient
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem wachModule_consequences_poleQuotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  intro D HW F Cm
  unfold gammaSemisimpleQuotientGlobal gammaSemisimpleLocal GammaSemisimpleQuotient
  intro l _ K s LL h T hT y hy
  classical
  have hfr := GlobalTheory.T.wachModule_inverseQuotient_free_finite_crystalline D HW F l K s LL h T hT y
  have hJ := GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite D HW l K s LL h T hT
  let Fs : Finset (↥(OL LL))ˣ := (hJ.toFinset ×ˢ Finset.Icc 1 y).image
    (fun p : ℤ × ℕ => uU ((HW l).W K s LL h) ^ (-(p.1 + (p.2 : ℤ))))
  have hmem : ∀ c, c ∈ Fs ↔ ∃ a ∈ Jumps (PD := (D.loc l).PD K) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧
      c = uU ((HW l).W K s LL h) ^ (-(a + j)) := by
    intro c
    simp only [Fs, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset, Finset.mem_Icc,
      Prod.exists]
    constructor
    · rintro ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
      exact ⟨a, ha, j, h1, h2, rfl⟩
    · rintro ⟨a, ha, j, h1, h2, rfl⟩
      exact ⟨a, j, ⟨ha, h1, h2⟩, rfl⟩
  refine ⟨hfr.1, hfr.2, Fs, ?_, ?_, ?_⟩
  · ext c
    exact hmem c
  · intro x hx
    exact GlobalTheory.T.prod_gamma_sub_jump_units_annihilates_quotient D HW F Cm l K s LL h T hT y hy Fs
      (fun a ha j h1 h2 => (hmem _).2 ⟨a, ha, j, h1, h2, rfl⟩) x hx
  · intro c hc
    obtain ⟨a, ha, j, h1, h2, rfl⟩ := (hmem c).1 hc
    obtain ⟨x, hx, hxN, hγ⟩ := GlobalTheory.T.gamma_eigenvalue_on_wachLattice_qPower_quotient D HW F Cm l K s LL h T hT y hy a ha j h1 h2
    exact ⟨x, hx, hxN, hγ⟩

end GlobalTheory.NL.WachModulePoleQuotient
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotientStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gammaSemisimpleQuotientD_statement : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), gammaSemisimpleQuotientGlobal D HW F := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | exact GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient <;> assumption)
end
