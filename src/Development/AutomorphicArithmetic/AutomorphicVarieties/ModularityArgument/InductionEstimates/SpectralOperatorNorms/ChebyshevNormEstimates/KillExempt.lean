module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.KillCore
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Langlands
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.RhoLe
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.KillComp
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearBlo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.CtZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.UnfZero

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.BloAt
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.bloAt :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Set (BW.Pl E)) (r : ℕ) (b : Blo S r) (V : Submodule ℂ (LL (mu1 E r))),
      IsSummand (mu1 E r) V → ((cuspToL2 (mu1 E r) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E r)) : LL (mu1 E r)) ∈ V →
      At (mu1 E r) S V (fun τ => Finset.univ.val.map (b.Λ τ)) fun w => (b.sat w).map fun x : ℂˣ => (x : ℂ) := by
  intro E _ _ _ S r b V hV hf
  obtain ⟨π, hπ⟩ := (Dp.exCusp E r (mu1 E r) V hV).exists
  have hc : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ AutomorphicForm.centralCuspForms E r := by
    intro s x
    have hs : (⟨Real.exp (Real.log s.1), Real.exp_pos _⟩ : {t : ℝ // 0 < t}) = s :=
      Subtype.ext (Real.exp_log s.2)
    have h := b.cen (Real.log s.1) x
    unfold BW.zt at h
    rw [hs] at h
    exact h
  have hm : b.f ∈ π.V := by
    have : (⟨b.f.1, b.cusp⟩ : AutomorphicForm.cuspForms E r) ∈ UpperTheory.V.Cm.carrier π := by
      rw [hπ.carrier_eq]; exact ⟨hc, hf⟩
    exact this
  refine ⟨fun τ => ?_, fun w hw => ?_⟩
  · obtain ⟨m, h1⟩ := (Dp.sInfEx E r (mu1 E r) V hV τ).exists
    have h2 : GlobalTheory.UnitaryBC.HasInfCharGL π.V τ m := (Dp.sInfIff E r (mu1 E r) π V hπ τ m).1 h1
    have hs : Submodule.span ℂ {b.f} ≠ ⊥ := by simpa using b.ne
    have e : m = Finset.univ.val.map (b.Λ τ) := by
      refine GlobalTheory.BcSpehProof.hasInfCharGL_unique hs (τ := τ) ⟨h2.1, fun u φ hφ => h2.2 u φ ?_⟩ ⟨by simp, fun u φ hφ => ?_⟩
      · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 hm) hφ
      · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
        rw [map_smul, b.inf, smul_comm, Multiset.map_map]
        rfl
    rw [e] at h1
    exact h1
  · have h0 := b.isSat w hw
    have hx : (⟨b.f, hm⟩ : π.V) ∈ GlobalTheory.PRep.fixed (π.locRep w) (GlobalTheory.LFun.KGL w (n := r)) :=
      GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 h0.2.1 k hk)
    have hne : (⟨b.f, hm⟩ : π.V) ≠ 0 := fun e => b.ne (congrArg Subtype.val e)
    obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.SatAe.exists_hasSatGL_locRep π w ((Submodule.ne_bot_iff _).2 ⟨_, hx, hne⟩)
    have h1 : GlobalTheory.LFun.IsSatVecGL w (BW.rw r w) b.f B := (hB.2 _ hx hne).map π.V.subtype (fun _ _ => rfl) b.ne
    have e := h1.unique h0
    subst e
    exact (Dp.sSatIff E r (mu1 E r) π V hπ w _).2 ⟨_, rfl, hB⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.Blo
noncomputable section

open NumberField

namespace UpperTheory.ConvolutionTheory.BW.Dat

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {S : Set (Pl E)} {n : ℕ}

def On (d : Dat S n) (Λ : (E →+* ℂ) → Multiset ℂ) (t : Pl E → Multiset ℂ) : Prop :=
  ∃ z, Λ = msOf (d.ptL z) ∧ ∀ w ∉ S, t w = d.ptS z w

def blo : {n : ℕ} → (d : Dat S n) → Fin d.len → Σ r, Blo S r
  | _, nil => fun j => j.elim0
  | _, cons b d => fun j => Fin.cases (motive := fun _ => Σ r, Blo S r) ⟨_, b⟩ d.blo (j : Fin (d.len + 1))

end UpperTheory.ConvolutionTheory.BW.Dat
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.BloVSummand
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (BW.Pl E)}

noncomputable def bloV {r : ℕ} (b : Blo S r) : Submodule ℂ (LL (mu1 E r)) := b.summand.choose

theorem bloV_summand {r : ℕ} (b : Blo S r) : IsSummand (mu1 E r) (bloV b) := b.summand.choose_spec.1

theorem bloV_mem {r : ℕ} (b : Blo S r) :
    ((cuspToL2 (mu1 E r) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E r)) : LL (mu1 E r)) ∈ bloV b := b.summand.choose_spec.2

private theorem blo_sum : ∀ {n : ℕ} (d : Dat S n), ∑ j, (d.blo j).1 = n
  | _, .nil => rfl
  | _, .cons b d => by
    have := blo_sum d
    exact (Fin.sum_univ_succ (n := d.len) _).trans (congrArg (_ + ·) this)

theorem blo_sat : ∀ {n : ℕ} (d : Dat S n) (j : Fin d.len), d.sat j = (d.blo j).2.sat
  | _, .nil, j => j.elim0
  | _, .cons b d, j => by
    refine Fin.cases (motive := fun j : Fin (d.len + 1) => (Dat.cons b d).sat j = (Dat.blo (.cons b d) j).2.sat) rfl
      (fun i => blo_sat d i) j

private theorem map_addCases {r s : ℕ} (f : Fin (r + s) → ℂ) :
    Finset.univ.val.map f = (Finset.univ.val.map fun i => f (Fin.castAdd s i)) + Finset.univ.val.map fun i => f (Fin.natAdd r i) := by
  simp only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]
  rfl

theorem blo_ms (τ : E →+* ℂ) : ∀ {n : ℕ} (d : Dat S n) (z : Fin d.len → ℂ),
    msOf (d.ptL z) τ = ∑ j, (Finset.univ.val.map ((d.blo j).2.Λ τ)).map (· + z j)
  | _, .nil, _ => rfl
  | _, .cons b d, z => by
    have ih := blo_ms τ d fun j => z (j.succ : Fin (d.len + 1))
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := d.len) _).symm
    unfold msOf at ih ⊢
    rw [map_addCases]
    congr 1
    · rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.castAdd _ i) = (0 : Fin (d.len + 1)) :=
        Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.castAdd _ i) = b.Λ τ i :=
        Fin.addCases_left (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)
    · refine Eq.trans ?_ ih
      refine Multiset.map_congr rfl fun i _ => ?_
      have h1 : (Dat.cons b d).idx (Fin.natAdd _ i) = ((d.idx i).succ : Fin (d.len + 1)) :=
        Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      have h2 : (Dat.cons b d).lam τ (Fin.natAdd _ i) = d.lam τ i :=
        Fin.addCases_right (motive := fun _ => ℂ) (left := b.Λ τ) (right := d.lam τ) i
      exact congrArg₂ (· + ·) h2 (congrArg z h1)

noncomputable def datB {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) : Datum E n where
  r := d.len
  two := h2
  d := fun j => (d.blo j).1
  pos := fun j => (d.blo j).2.pos
  sum := by exact blo_sum d
  μ := fun j => mu1 E (d.blo j).1
  haar := fun _ => inferInstance
  V := fun j => bloV (d.blo j).2
  summand := fun j => bloV_summand (d.blo j).2

theorem datB_at {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) (j : Fin d.len) :
    At (mu1 E (d.blo j).1) S (bloV (d.blo j).2) (fun τ => Finset.univ.val.map ((d.blo j).2.Λ τ))
      fun w => ((d.blo j).2.sat w).map fun x : ℂˣ => (x : ℂ) :=
  bloAt E S _ _ _ (bloV_summand _) (bloV_mem _)

theorem bloV_unique {r : ℕ} (b : Blo S r) {m : (E →+* ℂ) → Multiset ℂ} {B : BW.Pl E → Multiset ℂ}
    (h : At (mu1 E r) S (bloV b) m B) :
    (∀ τ, m τ = Finset.univ.val.map (b.Λ τ)) ∧ ∀ w ∉ S, B w = (b.sat w).map fun x : ℂˣ => (x : ℂ) := by
  have hb := bloAt E S r b (bloV b) (bloV_summand b) (bloV_mem b)
  have hp := Dp.parEx E r b.pos (mu1 E r) (bloV b) (bloV_summand b)
  exact ⟨fun τ => (hp.1 τ).unique (h.1 τ) (hb.1 τ), fun w hw => (hp.2.1 w (h.2 w hw).2.1).unique (h.2 w hw) (hb.2 w hw)⟩

private theorem on_of {n : ℕ} (d : Dat S n) {Λ : (E →+* ℂ) → Multiset ℂ} {t : BW.Pl E → Multiset ℂ} (lam : Fin d.len → ℂ)
    (m : Fin d.len → (E →+* ℂ) → Multiset ℂ) (B : Fin d.len → BW.Pl E → Multiset ℂ)
    (hA : ∀ j, At (mu1 E (d.blo j).1) S (bloV (d.blo j).2) (m j) (B j))
    (hΛ : ∀ τ, Λ τ = ∑ j, (m j τ).map (· + lam j))
    (ht : ∀ w ∉ S, t w = ∑ j, (B j w).map (· * (Ideal.absNorm w.asIdeal : ℂ) ^ (-lam j))) : d.On Λ t := by
  have hu := fun j => bloV_unique (d.blo j).2 (hA j)
  refine ⟨lam, funext fun τ => ?_, fun w hw => ?_⟩
  · rw [hΛ τ, blo_ms]
    exact Finset.sum_congr rfl fun j _ => by rw [(hu j).1 τ]
  · rw [ht w hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hu j).2 w hw, blo_sat, Multiset.map_map]
    rfl

theorem datB_pt {n : ℕ} (d : Dat S n) (h2 : 2 ≤ d.len) (Λ : (E →+* ℂ) → Multiset ℂ) (t : BW.Pl E → Multiset ℂ) :
    (datB d h2).Pt S Λ t ↔ d.On Λ t := by
  constructor
  · rintro ⟨lam, m, B, hA, hΛ, ht⟩
    exact on_of d lam m B hA hΛ ht
  · rintro ⟨z, rfl, ht⟩
    refine ⟨z, _, _, fun j => datB_at d h2 j, fun τ => blo_ms τ d z, fun w hw => ?_⟩
    rw [ht w hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [blo_sat, Multiset.map_map]
    rfl

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datOn :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) (d : Dat S n), 2 ≤ d.len →
      ∃ b : Datum E n, ∀ Λ t, b.Pt S Λ t ↔ d.On Λ t := by
  intro E _ _ _ S n d h2
  exact ⟨UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datB d h2, UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.datB_pt d h2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.Exempt
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW
open PositivityTheory.Rg.Tf.Core

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (BW.Pl E)}

private noncomputable def bV {r : ℕ} (b : Blo S r) : Submodule ℂ (LL (mu1 E r)) := b.summand.choose

private theorem bV_summand {r : ℕ} (b : Blo S r) : IsSummand (mu1 E r) (bV b) := b.summand.choose_spec.1

private theorem bV_mem {r : ℕ} (b : Blo S r) :
    ((cuspToL2 (mu1 E r) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E r)) : LL (mu1 E r)) ∈ bV b :=
  b.summand.choose_spec.2

private theorem sum_blo {n : ℕ} (d : Dat S n) : ∑ i, (d.blo i).1 = n := by
  induction d with
  | nil =>
    change ∑ i : Fin 0, _ = 0
    simp
  | @cons r s b d ih =>
    change ∑ i : Fin (d.len + 1), _ = r + s
    rw [Fin.sum_univ_succ]
    exact congrArg (r + ·) ih

private noncomputable def datOf {n : ℕ} (d : Dat S n) (h : 2 ≤ d.len) : Datum E n where
  r := d.len
  two := h
  d := fun i => (d.blo i).1
  pos := fun i => (d.blo i).2.pos
  sum := sum_blo d
  μ := fun i => mu1 E (d.blo i).1
  V := fun i => bV (d.blo i).2
  summand := fun i => bV_summand _

private theorem map_split {r s : ℕ} (f : Fin (r + s) → ℂ) :
    (Finset.univ.val.map f) = (Finset.univ.val.map fun i : Fin r => f (Fin.castAdd s i)) +
      (Finset.univ.val.map fun i : Fin s => f (Fin.natAdd r i)) := by
  simp only [Fin.univ_val_map, List.ofFn_add, Multiset.coe_add]
  rfl

private theorem lam_ms {n : ℕ} (d : Dat S n) (τ : E →+* ℂ) : ∀ z : Fin d.len → ℂ,
    (Finset.univ.val.map fun i : Fin n => d.lam τ i + z (d.idx i)) =
      ∑ j, (Finset.univ.val.map ((d.blo j).2.Λ τ)).map (· + z j) := by
  induction d with
  | nil =>
    intro z
    change _ = ∑ j : Fin 0, _
    simp
  | @cons r s b d ih =>
    intro (z : Fin (d.len + 1) → ℂ)
    change _ = ∑ j : Fin (d.len + 1), (Finset.univ.val.map (((Dat.cons b d).blo j).2.Λ τ)).map (· + z j)
    rw [map_split, Fin.sum_univ_succ]
    have h1 : (fun i : Fin r => (Dat.cons b d).lam τ (Fin.castAdd s i) + z ((Dat.cons b d).idx (Fin.castAdd s i))) =
        fun i => b.Λ τ i + z 0 := by
      funext i
      simp [Dat.lam, Dat.idx]
      exact congrArg z (Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _)
    have h2 : (fun i : Fin s => (Dat.cons b d).lam τ (Fin.natAdd r i) + z ((Dat.cons b d).idx (Fin.natAdd r i))) =
        fun i => d.lam τ i + z (d.idx i).succ := by
      funext i
      simp [Dat.lam, Dat.idx]
      exact congrArg z (Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) _)
    rw [h1, h2, ih fun j => z j.succ, Multiset.map_map]
    rfl

private theorem sat_blo {n : ℕ} (d : Dat S n) (j : Fin d.len) : d.sat j = (d.blo j).2.sat := by
  induction d with
  | nil => exact (j : Fin 0).elim0
  | @cons r s b d ih =>
    revert j
    change ∀ j : Fin (d.len + 1), _
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · exact ih i

private theorem pt_on {n : ℕ} (d : Dat S n) (h : 2 ≤ d.len) {Λ : (E →+* ℂ) → Multiset ℂ} {t : BW.Pl E → Multiset ℂ}
    (ho : d.On Λ t) : (datOf d h).Pt S Λ t := by
  obtain ⟨z, hΛ, ht⟩ := ho
  refine ⟨z, fun i τ => Finset.univ.val.map ((d.blo i).2.Λ τ), fun i w => ((d.blo i).2.sat w).map fun x : ℂˣ => (x : ℂ),
    fun i => UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.bloAt E S _ _ _ (bV_summand _) (bV_mem _), fun τ => ?_, fun w hw => ?_⟩
  · rw [hΛ]
    exact lam_ms d τ z
  · rw [ht w hw]
    unfold Dat.ptS
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sat_blo, Multiset.map_map]
    rfl

private theorem two_blocks {n : ℕ} (d : Dat S n) (h : d.len = 2) (hs : ∀ i, (d.blo i).1 = 2) :
    ∃ b₁ b₂ : Blo S 2, HEq d (Dat.cons b₁ (Dat.cons b₂ (Dat.nil : Dat S 0))) := by
  cases d with
  | nil => exact absurd h (by simp [Dat.len])
  | @cons r s b d =>
    cases d with
    | nil => exact absurd h (by simp [Dat.len])
    | @cons r' s' b' d =>
      cases d with
      | nil =>
        obtain rfl : r = 2 := hs (0 : Fin 2)
        obtain rfl : r' = 2 := hs (1 : Fin 2)
        exact ⟨b, b', HEq.rfl⟩
      | cons _ _ => exact absurd h (by simp [Dat.len])

private theorem form_mem {m : (E →+* ℂ) → Multiset ℂ} {B : BW.Pl E → Multiset ℂ} {τ : Submodule ℂ (LL (mu1 E 2))}
    (b : Blo S 2) (hA : At (mu1 E 2) S (bV b) m B)
    (hs : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m B → V = τ) :
    ((cuspToL2 (mu1 E 2) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ := by
  rw [← hs _ (bV_summand b) hA]
  exact bV_mem b

private theorem fin_two_ne : ∀ i j : Fin 2, i ≠ j → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by decide

set_option maxHeartbeats 2000000 in
private theorem core (τ₁ τ₂ : Submodule ℂ (LL (mu1 E 2))) (m₁ m₂ : (E →+* ℂ) → Multiset ℂ) (B₁ B₂ : BW.Pl E → Multiset ℂ)
    (smo₁ : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m₁ B₁ → V = τ₁)
    (smo₂ : ∀ V, IsSummand (mu1 E 2) V → At (mu1 E 2) S V m₂ B₂ → V = τ₂)
    (rigid : ∀ b : Datum E (2 + 2), b.Pt S (fun τ => m₁ τ + m₂ τ) (fun w => B₁ w + B₂ w) →
      b.r = 2 ∧ (∀ i, b.d i = 2) ∧ ∃ i j, i ≠ j ∧ At (b.μ i) S (b.V i) m₁ B₁ ∧ At (b.μ j) S (b.V j) m₂ B₂)
    (d : Dat S (2 + 2)) (h : 2 ≤ d.len) (ho : d.On (fun τ => m₁ τ + m₂ τ) (fun w => B₁ w + B₂ w)) :
    ∃ b₁ b₂ : Blo S 2, d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) ∧
      ((((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₁ ∧
          ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₂) ∨
        (((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₂ ∧
          ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ τ₁)) := by
  have hP := pt_on d h ho
  have key := rigid (datOf d h) hP
  have hr := key.1
  have hd := key.2.1
  obtain ⟨b₁, b₂, he⟩ := two_blocks d hr hd
  obtain ⟨i, j, hij, hi, hj⟩ := key.2.2
  have he' : d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) := eq_of_heq he
  subst he'
  refine ⟨b₁, b₂, rfl, ?_⟩
  revert i j
  change ∀ i j : Fin 2, _
  intro i j hij hi hj
  rcases fin_two_ne i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨form_mem b₁ hi smo₁, form_mem b₂ hj smo₂⟩
  · exact Or.inr ⟨form_mem b₁ hj smo₂, form_mem b₂ hi smo₁⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.exempt :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (μ : Measure (normOneGL (K := E) (n := (2 + 2)))) [μ.IsHaarMeasure] (θ : Twist μ)
      (𝔢 : Side θ 2) (𝔵 : UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (d : Dat 𝔢.S (2 + 2)), 2 ≤ d.len → d.On 𝔵.Λ 𝔵.t →
      ∃ b₁ b₂ : Blo 𝔢.S 2, d = Dat.cons b₁ (Dat.cons b₂ Dat.nil) ∧
        ((((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₁ ∧ ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₂) ∨
          (((cuspToL2 (mu1 E 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₂ ∧ ((cuspToL2 (mu1 E 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 E 2)) : LL (mu1 E 2)) ∈ 𝔵.τ₁)) := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 d h ho
  exact core 𝔵.τ₁ 𝔵.τ₂ 𝔵.m₁ 𝔵.m₂ 𝔵.B₁ 𝔵.B₂ 𝔵.smo₁ 𝔵.smo₂ 𝔵.rigid d h ho
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.CompZero
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.FixRep
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ] [SFinite μ]

private theorem rconv_fix (ν : Measure G) [IsProbabilityMeasure ν] {U : Set G} (hU : IsCompact U)
    (hs : ∀ᵐ k ∂ν, k ∈ U) {e : G → ℂ} (he : Continuous e)
    (a : CompactlySupportedContinuousMap G ℂ) (hH : ∀ g, ∫ k, e k * a (k⁻¹ * g) ∂ν = a g)
    (y : Lp ℂ 2 (quotientMeasure Γ μ)) (g : G) :
    ∫ k, e k * rconv Γ μ a y (g * k) ∂ν = rconv Γ μ a y g := by
  set L : G → ℂ := fun h => y (mk Γ h) with hL
  set P : G × G → ℂ := fun p => e p.1 * a (p.1⁻¹ * (g⁻¹ * p.2)) with hP
  have hPc : Continuous P := by
    have h1 : Continuous fun p : G × G => a (p.1⁻¹ * (g⁻¹ * p.2)) :=
      a.continuous.comp (by fun_prop)
    exact (he.comp continuous_fst).mul h1
  obtain ⟨M, hM⟩ := hU.exists_bound_of_continuousOn he.continuousOn
  obtain ⟨A, hA⟩ := a.continuous.bounded_above_of_compact_support a.hasCompactSupport
  set C : Set G := (fun p : G × G => g * (p.1 * p.2)) '' (U ×ˢ tsupport (a : G → ℂ)) with hCdef
  have hC : IsCompact C := (hU.prod a.hasCompactSupport.isCompact).image (by fun_prop)
  have hint : Integrable (fun p : G × G => P p * L p.2) (ν.prod μ) := by
    have hB : Integrable (fun p : G × G => (M * A) * C.indicator (fun h => ‖L h‖) p.2)
        (ν.prod μ) := by
      have h0 : Integrable (C.indicator fun h => ‖L h‖) μ :=
        (integrable_indicator_iff hC.measurableSet).2 (integrableOn_lift Γ μ y hC).norm
      exact (h0.comp_snd ν).const_mul _
    refine hB.mono' (hPc.aestronglyMeasurable.mul
      ((stronglyMeasurable_lift Γ μ y).comp_measurable measurable_snd).aestronglyMeasurable) ?_
    have hk : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ U :=
      Measure.quasiMeasurePreserving_fst.ae hs
    filter_upwards [hk] with p hp
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p.1 hp)
    by_cases hz : p.1⁻¹ * (g⁻¹ * p.2) ∈ tsupport (a : G → ℂ)
    · have hmem : p.2 ∈ C := ⟨(p.1, p.1⁻¹ * (g⁻¹ * p.2)), ⟨hp, hz⟩, by simp⟩
      rw [indicator_of_mem hmem, norm_mul, norm_mul]
      have hA' := hA (p.1⁻¹ * (g⁻¹ * p.2))
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hM p.1 hp) hA' (norm_nonneg _) hM0) (norm_nonneg _)
    · have h0 : a (p.1⁻¹ * (g⁻¹ * p.2)) = 0 := image_eq_zero_of_notMem_tsupport hz
      have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
      simp only [hP, h0, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg hM0 hA0) (indicator_nonneg (fun _ _ => norm_nonneg _) _)
  calc ∫ k, e k * rconv Γ μ a y (g * k) ∂ν
      = ∫ k, ∫ h, P (k, h) * L h ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun k => ?_)
        simp only [rconv, hP, hL]
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        simp only [mul_inv_rev, mul_assoc]
    _ = ∫ h, ∫ k, P (k, h) * L h ∂ν ∂μ := integral_integral_swap (f := fun k h => P (k, h) * L h) hint
    _ = ∫ h, a (g⁻¹ * h) * L h ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        simp only [hP]
        rw [integral_mul_const, hH (g⁻¹ * h)]
    _ = rconv Γ μ a y g := rfl

end General

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.fixRep :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (D : TypeDat K n) (a : CC K n), D.Hecke a →
      ∀ (y : L2 μ) (Φ : G1 K n → ℂ), Continuous Φ → Reps μ (Rop μ a y) Φ → D.Fix Φ := by
  intro K _ _ n μ _ D a hH y Φ hΦ hrep g
  haveI := D.prob
  have hc : Continuous (rconv (Gam K n) μ a y) := continuous_rconv (Gam K n) μ a y
  have hae : (fun z => (Rop μ a y) (mk (Gam K n) z)) =ᵐ[μ]
      rconv (Gam K n) μ a y := by
    have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
    filter_upwards [QuasiMeasurePreserving.ae_eq_comp (quasiMeasurePreserving_mk (Gam K n) μ)
      (integrated_ae_eq_rconvQ (Gam K n) μ a y)] with z hz
    simpa only [Function.comp_apply, rconvQ_mk, Rop] using hz
  have hEq : Φ = rconv (Gam K n) μ a y := by
    refine (hΦ.ae_eq_iff_eq μ hc).1 ?_
    exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hrep) hae
  rw [hEq]
  set_option synthInstance.maxHeartbeats 200000 in
  exact rconv_fix (Gam K n) μ D.ν (typeFin D).1 D.supp D.cont a (fun g => (hH g).1) y g
end

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open GlobalTheory.CuspRep UpperTheory.ConvolutionTheory.BW

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

attribute [local instance 100000] MeasurableSpace.pi

variable {K : Type} [Field K] [NumberField K]

private theorem sfin {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] : SFinite ν := inferInstance

private theorem out_mk {n : ℕ} (h : G1 K n → ℂ) (hh : ∀ γ ∈ Gam K n, ∀ m, h (γ * m) = h m) (g : G1 K n) :
    h (Quotient.out (mk (Gam K n) g)) = h g := by
  obtain ⟨γ, e⟩ := RightCosetSpace.mk_eq_mk_iff.1 (show mk (Gam K n) (Quotient.out (mk (Gam K n) g)) = mk (Gam K n) g from Quotient.out_eq _)
  rw [← e]
  exact hh _ γ.2 _

private theorem int_out {n : ℕ} (μ : Measure (G1 K n)) (h : G1 K n → ℂ) (hh : ∀ γ ∈ Gam K n, ∀ m, h (γ * m) = h m) :
    ∫ y, h (Quotient.out y) ∂quotientMeasure (Gam K n) μ = ∫ g, h g ∂fd μ := by
  rw [integral_quotientMeasure]
  simp only [out_mk h hh]

private theorem left_gam {n : ℕ} {φ : AdelicGLn.AdelicGL K n → ℂ} (h : IsLeftInvariant φ) :
    ∀ γ ∈ Gam K n, ∀ m : G1 K n, φ ((γ * m : G1 K n) : AdelicGLn.AdelicGL K n) = φ m := by
  rintro γ ⟨δ, hδ⟩ m
  have : (γ : AdelicGLn.AdelicGL K n) = AdelicGLn.diagonal K n δ := hδ.symm
  rw [Subgroup.coe_mul, this, h]

private theorem lev_blk {R : Type} [CommRing R] {r s : ℕ} (x : GL (Fin r) R) (y : GL (Fin s) R) :
    GlobalTheory.CompanionTheory.CTFin.lev R r s (x, y) = blk x y := Units.ext (GlobalTheory.SmGL.val_emb₂ R _ _)

private theorem lev_zero {R : Type} [CommRing R] (x : GL (Fin 2) R) : GlobalTheory.CompanionTheory.CTFin.lev R 2 0 (x, 1) = x := by
  rw [lev_blk]
  ext i j
  have e : ∀ i : Fin 2, (finSumFinEquiv (m := 2) (n := 0)).symm i = Sum.inl i := fun i => finSumFinEquiv_symm_apply_castAdd i
  simp [blk, e]

private theorem ct_top (φ : AdelicGLn.AdelicGL K 2 → ℂ) (g : AdelicGLn.AdelicGL K 2) : constantTerm 2 φ g = φ g := by
  haveI : IsEmpty (UPos 2 2) := ⟨fun p => by have := p.1.2.2; have := p.2.2; omega⟩
  have e : ∀ X : UPos 2 2 → 𝔸[K], unipGL X = 1 := fun X => by rw [Subsingleton.elim X 0, unipGL_zero]
  have e2 : unipFundamentalDomain K 2 2 = univ := eq_univ_of_forall fun X p => isEmptyElim p
  simp [constantTerm, e, e2, Measure.real, Measure.pi_empty_univ]

private theorem zt_blk (a : ℝ) : blk (InvariantSubmoduleMonicPolynomial.zt K a) (InvariantSubmoduleMonicPolynomial.zt K a) = UpperTheory.ConvolutionTheory.BW.zt K (2 + 2) (a + a) := by
  have h1 : ∀ u, blk (scalarUnits K 2 u) (scalarUnits K 2 u) = scalarUnits K (2 + 2) u := by
    intro u
    refine Units.ext ?_
    simp only [blk, scalarUnits_apply, coe_diagUnits, Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext i
    change Sum.elim (fun _ => (u : 𝔸[K])) (fun _ => (u : 𝔸[K])) (finSumFinEquiv.symm i) = _
    cases finSumFinEquiv.symm i <;> rfl
  simp only [InvariantSubmoduleMonicPolynomial.zt, UpperTheory.ConvolutionTheory.BW.zt, centralSection, MonoidHom.comp_apply, h1]
  congr 2
  refine Subtype.ext ?_
  show Real.exp a ^ _ = Real.exp (a + a) ^ _
  have : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [← Real.exp_mul, ← Real.exp_mul]
  congr 1
  push_cast
  field_simp
  ring

private theorem zt_add (a b : ℝ) : InvariantSubmoduleMonicPolynomial.zt K (a + b) = InvariantSubmoduleMonicPolynomial.zt K a * InvariantSubmoduleMonicPolynomial.zt K b := by
  rw [InvariantSubmoduleMonicPolynomial.zt, InvariantSubmoduleMonicPolynomial.zt, InvariantSubmoduleMonicPolynomial.zt, ← map_mul]
  congr 1
  exact Subtype.ext (Real.exp_add a b)

private theorem lev_lv (a b : G1 K 2) (s t : ℝ) :
    blk (InvariantSubmoduleMonicPolynomial.zt K s * (a : AdelicGLn.AdelicGL K 2)) (InvariantSubmoduleMonicPolynomial.zt K t * (b : AdelicGLn.AdelicGL K 2)) =
      UpperTheory.ConvolutionTheory.BW.zt K (2 + 2) ((s + t) / 2 + (s + t) / 2) * ((lv a b ((s - t) / 2) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := by
  have hc : ∀ (x : ℝ) (g : AdelicGLn.AdelicGL K 2), g * InvariantSubmoduleMonicPolynomial.zt K x = InvariantSubmoduleMonicPolynomial.zt K x * g := fun x g => (centralSection_mul_comm _ g).symm
  rw [blkLaws.1, ← zt_blk, blkLaws.2.2.2.2.2.1, hc, hc, ← mul_assoc, ← mul_assoc, ← zt_add, ← zt_add]
  congr 3 <;> ring

variable [_root_.NumberField.IsTotallyComplex K]

private theorem blo_rd {S : Set (Pl K)} (b : Blo S 2) (τ : Submodule ℂ (L2 (mu1 K 2)))
    (h : ((cuspToL2 (mu1 K 2) ⟨b.f.1, b.cusp⟩ : cuspidalL2 (mu1 K 2)) : L2 (mu1 K 2)) ∈ τ) :
    Rd τ fun m : G1 K 2 => b.f.1 (m : AdelicGLn.AdelicGL K 2) := by
  obtain ⟨hu, hc⟩ := UpperTheory.ConvolutionTheory.BW.cuspUmg K 2 b.f b.cusp
  refine ⟨((umgOps K 2).2 _ hu).1.comp continuous_subtype_val, ⟨_, h, ?_⟩, left_gam hu.left, fun m => ?_, ?_⟩
  · filter_upwards [QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K 2) (mu1 K 2)) (coeFn_cuspToL2 (mu1 K 2) ⟨b.f.1, b.cusp⟩)] with y hy
    rw [hy]
    rfl
  · have := hc 1 one_pos one_lt_two (m : AdelicGLn.AdelicGL K 2)
    unfold constantTerm at this
    exact this
  · exact rapidDecay K 2 b.f hu hc

theorem compZero (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (τ₁ τ₂ : Submodule ℂ (L2 (mu1 K 2))) (D : TypeDat K (2 + 2)) {d : ℕ}
    (A : Line μ τ₁ τ₂ D d) (h₁ : CuspIrr (mu1 K 2) τ₁) (h₂ : CuspIrr (mu1 K 2) τ₂) (a : CC K (2 + 2)) (ha : D.Hecke a) (y : L2 μ)
    (w : Sm K (2 + 2)) (hw : Rep μ (Rop μ a y) w) (hJ : ∀ u, ⟪A.J u, Rop μ a y⟫_ℂ = 0) {S : Set (Pl K)} (b₁ b₂ : Blo S 2)
    (m₁ : ((cuspToL2 (mu1 K 2) ⟨b₁.f.1, b₁.cusp⟩ : cuspidalL2 (mu1 K 2)) : L2 (mu1 K 2)) ∈ τ₁)
    (m₂ : ((cuspToL2 (mu1 K 2) ⟨b₂.f.1, b₂.cusp⟩ : cuspidalL2 (mu1 K 2)) : L2 (mu1 K 2)) ∈ τ₂) (k : KA K (2 + 2)) :
    (Dat.cons b₁ (Dat.cons b₂ Dat.nil)).comp (rt K (2 + 2) k w).1 = 0 := by
  funext t
  have r₁ := blo_rd b₁ τ₁ m₁
  have r₂ := blo_rd b₂ τ₂ m₂
  have hc : Continuous fun g : G1 K (2 + 2) => w.1 (g : AdelicGLn.AdelicGL K (2 + 2)) :=
    ((umgOps K _).2 _ hw.umg).1.comp continuous_subtype_val
  have hΓ := left_gam hw.umg.left
  have hrep : Reps μ (Rop μ a y) fun g : G1 K (2 + 2) => w.1 (g : AdelicGLn.AdelicGL K (2 + 2)) :=
    (QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K (2 + 2)) μ) hw.ae).mono fun g hg => hg.trans (out_mk (fun g : G1 K (2 + 2) => w.1 (g : AdelicGLn.AdelicGL K (2 + 2))) hΓ g)
  obtain ⟨F, hF, hFu, hFr, -⟩ := ctOps K 2 2 w hw.umg
  have hrat : ∀ γ₁ ∈ Gam K 2, ∀ γ₂ ∈ Gam K 2, ∀ g : G1 K (2 + 2),
      constantTerm 2 w.1 ((lv γ₁ γ₂ 0 * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = constantTerm 2 w.1 (g : AdelicGLn.AdelicGL K (2 + 2)) := by
    rintro γ₁ ⟨δ₁, e₁⟩ γ₂ ⟨δ₂, e₂⟩ g
    have e₁' : (γ₁ : AdelicGLn.AdelicGL K 2) = ratGL K 2 δ₁ := e₁.symm
    have e₂' : (γ₂ : AdelicGLn.AdelicGL K 2) = ratGL K 2 δ₂ := e₂.symm
    have z0 : InvariantSubmoduleMonicPolynomial.zt K 0 = 1 := by
      have := zt_add (K := K) 0 0
      rwa [add_zero, left_eq_mul] at this
    rw [Subgroup.coe_mul, blkLaws.1, neg_zero, z0, mul_one, mul_one, e₁', e₂', ← lev_blk, ← hF]
    exact hFr (δ₁, δ₂) _
  let k' : G1 K (2 + 2) := ⟨k, (blkLaws.2.2.2.2.2.2.2.2.2.2.2 _).2 _ k.2⟩
  obtain ⟨hi, h0⟩ := unfZero μ (mu1 K 2) τ₁ τ₂ D A h₁ h₂ _ _ (fun g => constantTerm 2 w.1 (g : AdelicGLn.AdelicGL K (2 + 2))) _ _ hc hΓ hrep
    (by
      obtain ⟨N, hN⟩ := hw.umg.growth
      obtain ⟨B, hB⟩ := hN 1
      rw [map_one, Module.End.one_apply] at hB
      exact ⟨N, B, fun g => hB g⟩)
    (fixRep μ D a ha y _ hc hrep) hJ (fun g => rfl) hrat (fun X g => by
      have e : GlobalTheory.CuspRep.unip X = unipGL X := Units.ext rfl
      rw [← hF, Subgroup.coe_mul, ← hFu X g, e]
      rfl) r₁ r₂
    ((t (0 : Fin 2) - t (1 : Fin 2)) / 2) k' k.2
  haveI := finFd (mu1 K 2)
  haveI := sfin (fd (mu1 K 2))
  rw [integral_prod_symm _ hi] at h0
  have e : ∀ a b : G1 K 2, constantTerm 2 (rt K (2 + 2) k w).1 (GlobalTheory.CompanionTheory.CTFin.lev (Ad K) 2 2
      (UpperTheory.ConvolutionTheory.BW.zt K 2 (t (0 : Fin 2)) * a, UpperTheory.ConvolutionTheory.BW.zt K 2 (t (1 : Fin 2)) * b)) =
      constantTerm 2 w.1 ((lv a b ((t (0 : Fin 2) - t (1 : Fin 2)) / 2) * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := by
    intro a b
    rw [lev_blk]
    erw [lev_lv]
    refine integral_congr_ae (ae_of_all _ fun X => ?_)
    show w.1 (unipGL X * (_ * _) * _) = w.1 (unipGL X * (_ * _))
    rw [← mul_assoc, UpperTheory.ConvolutionTheory.BW.zt, ← centralSection_mul_comm, mul_assoc, mul_assoc]
    exact hw.cen _ _
  have hmul := (blkLaws (K := K)).2.1
  have hl : ∀ γ₁ ∈ Gam K 2, ∀ γ₂ ∈ Gam K 2, ∀ (a b : G1 K 2) s,
      constantTerm 2 w.1 ((lv (γ₁ * a) (γ₂ * b) s * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        constantTerm 2 w.1 ((lv a b s * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := fun γ₁ h1 γ₂ h2 a b s => by
    rw [← hrat γ₁ h1 γ₂ h2 (lv a b s * k'), ← mul_assoc, hmul, zero_add]
  show slice (r := 2) (s := 0) b₂.f.1 (t (1 : Fin 2)) (slice (r := 2) (s := 2) b₁.f.1 (t (0 : Fin 2)) (rt K (2 + 2) k w).1) 1 = 0
  rw [← h0, ← int_out (mu1 K 2) _ fun γ hγ b => by
    simp only [r₂.rat γ hγ b, fun a s => (by simpa only [one_mul] using hl 1 (one_mem _) γ hγ a b s :
      constantTerm 2 w.1 ((lv a (γ * b) s * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = _)]]
  refine integral_congr_ae (ae_of_all _ fun y₂ => ?_)
  simp only
  rw [← int_out (mu1 K 2) _ fun γ hγ a => by
    simp only [r₁.rat γ hγ a, fun b s => (by simpa only [one_mul] using hl γ hγ 1 (one_mem _) a b s :
      constantTerm 2 w.1 ((lv (γ * a) b s * k' : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = _)]]
  erw [lev_zero, ct_top]
  rw [slice, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun y₁ => ?_)
  simp only
  erw [e]
  rw [map_mul]
  ring

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.HeightTwoBlocks.MapUnivAdd
open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (BW.Pl E)}

private abbrev Pts (E : Type) [Field E] [NumberField E] : Type :=
  ((E →+* ℂ) → Multiset ℂ) → (BW.Pl E → Multiset ℂ) → Prop

private def key {n : ℕ} (d : Dat S n) : ℕ × Pts E := (d.len, d.On)

private def step (S : Set (BW.Pl E)) (r : ℕ) (p : ((E →+* ℂ) → Fin r → ℂ) × (BW.Pl E → Multiset ℂˣ))
    (q : ℕ × Pts E) : ℕ × Pts E :=
  (q.1 + 1, fun Λ t => ∃ (c : ℂ) (Λ' : (E →+* ℂ) → Multiset ℂ) (t' : BW.Pl E → Multiset ℂ), q.2 Λ' t' ∧
    (∀ τ, Λ τ = (Finset.univ.val.map fun i => p.1 τ i + c) + Λ' τ) ∧
    ∀ w ∉ S, t w = ((p.2 w).map fun x : ℂˣ => (x : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-c)) + t' w)


open Classical in
private noncomputable def par {r : ℕ} (b : Blo S r) : ((E →+* ℂ) → Fin r → ℂ) × (BW.Pl E → Multiset ℂˣ) :=
  (b.Λ, fun w => if w ∈ S then 0 else b.sat w)

private theorem map_univ_add {α : Type} {r s : ℕ} (f : Fin (r + s) → α) :
    (Finset.univ.val.map f) =
      (Finset.univ.val.map fun i => f (Fin.castAdd s i)) + Finset.univ.val.map fun i => f (Fin.natAdd r i) := by
  have key : ∀ {m : ℕ} (g : Fin m → α), Finset.univ.val.map g = ∑ i, ({g i} : Multiset α) := by
    intro m g
    have e : (Finset.univ.val.map fun i => ({g i} : Multiset α)) =
        (Finset.univ.val.map g).map fun a => ({a} : Multiset α) := by
      rw [Multiset.map_map]
      rfl
    rw [Finset.sum_eq_multiset_sum, e, Multiset.sum_map_singleton]
  rw [key, key, key, Fin.sum_univ_add]

private theorem msOf_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) (z : Fin (d.len + 1) → ℂ) (τ : E →+* ℂ) :
    msOf ((Dat.cons b d).ptL z) τ =
      (Finset.univ.val.map fun i => b.Λ τ i + z 0) + msOf (d.ptL fun j => z j.succ) τ := by
  simp only [msOf]
  rw [map_univ_add]
  congr 1
  · refine Multiset.map_congr rfl fun i _ => ?_
    simp [Dat.ptL, Dat.lam, Dat.idx]
    exact congrArg z (Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) _)
  · refine Multiset.map_congr rfl fun i _ => ?_
    simp [Dat.ptL, Dat.lam, Dat.idx]
    exact congrArg z (Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) _)

private theorem ptS_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) (z : Fin (d.len + 1) → ℂ) (w : BW.Pl E) :
    (Dat.cons b d).ptS z w =
      ((b.sat w).map fun x : ℂˣ => (x : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-z 0)) + d.ptS (fun j => z j.succ) w := by
  change (∑ j : Fin (d.len + 1), _) = _
  rw [Fin.sum_univ_succ]
  rfl

private theorem step_key {r s : ℕ} (b : Blo S r) (d : Dat S s) :
    step S r (par b) (key d) = key (Dat.cons b d) := by
  refine Prod.ext rfl (funext fun Λ => funext fun t => propext ⟨?_, ?_⟩)
  · rintro ⟨c, Λ', t', ⟨z, rfl, ht'⟩, hΛ, ht⟩
    refine ⟨(Fin.cons c z : Fin (d.len + 1) → ℂ), funext fun τ => ?_, fun w hw => ?_⟩
    · rw [msOf_cons]
      simpa [par] using hΛ τ
    · rw [ptS_cons]
      have := ht w hw
      simp only [par, key, if_neg hw] at this
      rw [this, ht' w hw]
      simp
  · rintro ⟨(z : Fin (d.len + 1) → ℂ), rfl, ht⟩
    refine ⟨z 0, msOf (d.ptL fun j => z j.succ), d.ptS fun j => z j.succ,
      ⟨fun j => z j.succ, rfl, fun _ _ => rfl⟩, fun τ => ?_, fun w hw => ?_⟩
    · rw [msOf_cons]
      rfl
    · rw [ht w hw, ptS_cons]
      simp [par, if_neg hw]

private def Fin' (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) : Prop :=
  ∀ (ρ : Typ E n) (B : ℝ),
    {q : ℕ × Pts E | ∃ d : Dat S n, d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d}.Finite

private theorem fin_cons (r s : ℕ) (hs : Fin' E S s) (ρ : Typ E (r + s)) (B : ℝ) :
    {q : ℕ × Pts E | ∃ (b : Blo S r) (d : Dat S s), (Dat.cons b d).HasTyp ρ.ρ ∧
      (∀ τ i, ‖(Dat.cons b d).lam τ i‖ ≤ B) ∧ q = key (Dat.cons b d)}.Finite := by
  obtain ⟨⟨ρ₁, c₁, e₁⟩, ⟨ρ₂, c₂, e₂⟩, -⟩ := UpperTheory.ConvolutionTheory.BW.resTyp E r s ρ
  have f₁ := UpperTheory.ConvolutionTheory.BW.nearBlo E S r ⟨ρ.d, ρ₁, c₁⟩ B
  have f₂ := hs ⟨ρ.d, ρ₂, c₂⟩ B
  refine (f₁.image2 (step S r) f₂).subset ?_
  rintro q ⟨b, d, ⟨hK, hT⟩, hB, rfl⟩
  refine ⟨par b, ⟨b, ?_, fun τ i => ?_, rfl, fun w => rfl⟩, key d, ⟨d, ?_, fun τ i => ?_, rfl⟩, step_key b d⟩
  · change Killed (⇑ρ₁) b.f.1
    rw [e₁]
    exact hK
  · simpa [Dat.lam] using hB τ (Fin.castAdd s i)
  · change d.HasTyp (⇑ρ₂)
    rw [e₂]
    exact hT
  · simpa [Dat.lam] using hB τ (Fin.natAdd r i)

private theorem dat_cases {n : ℕ} (d : Dat S n) :
    (n = 0 ∧ HEq d (Dat.nil : Dat S 0)) ∨
      ∃ (r s : ℕ) (b : Blo S r) (d' : Dat S s), r + s = n ∧ 0 < r ∧ HEq d (Dat.cons b d') := by
  cases d with
  | nil => exact Or.inl ⟨rfl, HEq.rfl⟩
  | cons b d' => exact Or.inr ⟨_, _, b, d', rfl, b.pos, HEq.rfl⟩

private theorem fin_all (n : ℕ) : Fin' E S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ρ B
    have A : ∀ r s : ℕ, {q : ℕ × Pts E | r + s = n ∧ 0 < r ∧ ∃ (d : Dat S n) (b : Blo S r) (d' : Dat S s),
        HEq d (Dat.cons b d') ∧ d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d}.Finite := by
      intro r s
      by_cases h : r + s = n ∧ 0 < r
      · obtain ⟨h, hr⟩ := h
        subst h
        refine (fin_cons r s (ih s (by omega)) ρ B).subset ?_
        rintro q ⟨-, -, d, b, d', he, h₁, h₂, rfl⟩
        obtain rfl := eq_of_heq he
        exact ⟨b, d', h₁, h₂, rfl⟩
      · exact Set.finite_empty.subset fun q hq => h ⟨hq.1, hq.2.1⟩
    have A₀ : {q : ℕ × Pts E | n = 0 ∧ ∃ d : Dat S n, HEq d (Dat.nil : Dat S 0) ∧ q = key d}.Finite := by
      by_cases h : n = 0
      · subst h
        refine (Set.finite_singleton (key (Dat.nil : Dat S 0))).subset ?_
        rintro q ⟨-, d, he, rfl⟩
        obtain rfl := eq_of_heq he
        rfl
      · exact Set.finite_empty.subset fun q hq => h hq.1
    refine (A₀.union (Set.finite_iUnion fun p : Fin (n + 1) × Fin (n + 1) => A p.1 p.2)).subset ?_
    rintro q ⟨d, h₁, h₂, rfl⟩
    rcases dat_cases d with ⟨h, he⟩ | ⟨r, s, b, d', h, hr, he⟩
    · exact Or.inl ⟨h, d, he, rfl⟩
    · refine Or.inr (Set.mem_iUnion.2 ⟨(⟨r, by omega⟩, ⟨s, by omega⟩), h, hr, d, b, d', he, h₁, h₂, rfl⟩)

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.near2 :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Set (BW.Pl E)) (n : ℕ) (ρ : Typ E n) (B : ℝ), ∃ D : Set (Dat S n), D.Finite ∧
      ∀ d : Dat S n, d.HasTyp ρ.ρ → (∀ τ i, ‖d.lam τ i‖ ≤ B) → ∃ d' ∈ D, d'.len = d.len ∧ ∀ Λ t, d'.On Λ t ↔ d.On Λ t := by
  intro E _ _ _ S n ρ B
  have f := fin_all (E := E) (S := S) n ρ B
  have := f.to_subtype
  choose g hg using fun q : {q : ℕ × Pts E | ∃ d : Dat S n, d.HasTyp ρ.ρ ∧ (∀ τ i, ‖d.lam τ i‖ ≤ B) ∧ q = key d} => q.2
  refine ⟨Set.range g, Set.finite_range g, fun d h₁ h₂ => ?_⟩
  have e : key d = key (g ⟨key d, d, h₁, h₂, rfl⟩) := (hg ⟨key d, d, h₁, h₂, rfl⟩).2.2
  refine ⟨_, ⟨_, rfl⟩, (congrArg Prod.fst e).symm, fun Λ t => ?_⟩
  have e₂ : d.On = (g ⟨key d, d, h₁, h₂, rfl⟩).On := congrArg Prod.snd e
  rw [← e₂]
end

open MeasureTheory NumberField MvPolynomial GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped InnerProductSpace

private theorem qz {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (A B C D : H →L[ℂ] H) {X Y : H →L[ℂ] H} (h1 : A ∘L B = X)
    (h2 : A ∘L C = Y) (h3 : A - X = D) (h4 : D - Y = 0) : A ∘L (1 - B - C) = 0 := by
  rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub, h1, h2, ← h4, ← h3]
  rfl

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.killExempt :
    UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KillExempt := by
  intro K _ _ _ μ _ θ 𝔢 𝔵 η hη
  obtain ⟨ρ, Cb, hCb, hcore⟩ := killCore (n := 2 + 2) (by norm_num) 𝔢.toAmp η hη
  obtain ⟨B, hB⟩ := far K (2 + 2) Cb hCb
  obtain ⟨D₀, hfin, hD₀⟩ := KX.near2 K 𝔢.S (2 + 2) ρ B
  let D : Set (Dat 𝔢.S (2 + 2)) := {d ∈ D₀ | 2 ≤ d.len ∧ ¬ d.On 𝔵.Λ 𝔵.t}
  have hD : D.Finite := hfin.subset (Set.sep_subset _ _)
  choose b hb using fun d : D => KX.datOn K 𝔢.S (2 + 2) d.1 d.2.2.1
  refine ⟨D, hD.fintype, b, fun d => ⟨_, _, (hb d _ _).2 ⟨0, rfl, fun _ _ => rfl⟩⟩, fun d h => d.2.2.2 ((hb d _ _).1 h),
    fun ev hev hP χ hχ hχ0 _ F G hF hFb hG => ?_⟩
  obtain ⟨sa, idem, hker⟩ := 𝔵.isP
  have hc : ∀ y, Pc μ y ∈ cuspidalL2 μ := fun y => Submodule.starProjection_apply_mem _ y
  have saC : IsSelfAdjoint (Pc μ) := isSelfAdjoint_starProjection _
  have sy : ∀ a b, ⟪a, Pc μ b⟫_ℂ = ⟪Pc μ a, b⟫_ℂ := fun a b => (saC.isSymmetric a b).symm
  have PPc : 𝔵.P ∘L Pc μ = 0 := by
    ext1 y
    show 𝔵.P (Pc μ y) = 0
    refine (hker _).2 ⟨fun u => ?_, fun v => ?_⟩
    · rw [sy, (ctZero K μ _ _ _ 𝔵.pair _ _ _ 𝔵.A 𝔵.A' u).1, inner_zero_left]
    · rw [sy,
        (ctZero K μ _ _ _ ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩ _ _ _ 𝔵.A' 𝔵.A v).1, inner_zero_left]
  have PcP : Pc μ ∘L 𝔵.P = 0 := by
    have := congrArg star (show 𝔵.P * Pc μ = 0 from PPc)
    rwa [star_mul, sa.star_eq, saC.star_eq, star_zero] at this
  have PcPc : Pc μ ∘L Pc μ = Pc μ := (Submodule.isIdempotentElem_starProjection _).eq
  refine hcore ev hev 𝔵.P (1 - Pc μ - 𝔵.P) hP ?_ ?_ χ hχ hχ0 F G hF hG fun y φ w hy hw hφ hs hkw hsw hsum => ?_
  · exact qz _ _ _ _ PcPc PcP (sub_self _) (sub_zero _)
  · exact qz _ _ _ _ PPc idem (sub_zero _) (sub_self _)
  refine (langlands K 𝔢.S _ ρ w hw.umg hkw hsw).2 fun k d hd hlen => ?_
  by_cases hon : d.On 𝔵.Λ 𝔵.t
  · have hA : 𝔵.P (Rop μ 𝔢.a y) = 0 := by
      have := DFunLike.congr_fun (hP (C (X none)) (by simp)) y
      rw [hev.amp] at this
      simp only [ContinuousLinearMap.comp_apply, hy, map_zero] at this
      rw [𝔢.a_op]; exact this.symm
    obtain ⟨o1, o2⟩ := (hker _).1 hA
    rw [← 𝔢.a_op] at hw
    obtain ⟨b₁, b₂, rfl, h | h⟩ := KX.exempt K μ θ 𝔢 𝔵 d hlen hon
    · exact KX.compZero μ _ _ 𝔵.D 𝔵.A 𝔵.pair.irr₁ 𝔵.pair.irr₂ 𝔢.a 𝔵.a_hecke y w hw o1 b₁ b₂ h.1 h.2 k
    · exact KX.compZero μ _ _ 𝔵.D 𝔵.A' 𝔵.pair.irr₂ 𝔵.pair.irr₁ 𝔢.a 𝔵.a_hecke y w hw o2 b₁ b₂ h.1 h.2 k
  refine killComp K 𝔢.S _ Cb φ w F G hCb hφ hs hw.umg hF.2 hG hsum k d ?_
  by_cases hfar : ∃ τ i, B < ‖d.lam τ i‖
  · exact Or.inr fun ψ hψ hSψ => hB 𝔢.S d ψ hψ hSψ hfar
  · push Not at hfar
    obtain ⟨d', hd', hl, hk⟩ := hD₀ d hd hfar
    exact Or.inl fun z => hFb ⟨d', hd', hl ▸ hlen, fun h => hon ((hk _ _).1 h)⟩ _ _
      ((hb _ _ _).2 ((hk _ _).2 ⟨z, rfl, fun _ _ => rfl⟩))
