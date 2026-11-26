module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegrees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLe

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompression
open Finset

namespace GlobalTheory.CompanionTheory.LevelCompress

open PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def lowCount (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

theorem lowCount_lt (lev : Fin n → ℕ) (a : Fin n) : lowCount lev a < n := by
  have h : (univ.filter fun b => lev b < lev a).card < (univ : Finset (Fin n)).card :=
    Finset.card_lt_card (Finset.filter_ssubset.2 ⟨a, Finset.mem_univ a, lt_irrefl (lev a)⟩)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem lowCount_le_of_le {lev : Fin n → ℕ} {a b : Fin n} (h : lev a ≤ lev b) :
    lowCount lev a ≤ lowCount lev b := by
  unfold lowCount
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_lt_of_le hc.2 h⟩

theorem lowCount_lt_of_lt {lev : Fin n → ℕ} {a b : Fin n} (h : lev a < lev b) :
    lowCount lev a < lowCount lev b := by
  unfold lowCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨a, ?_, ?_⟩
    · simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ a, h⟩
    · simp only [Finset.mem_filter, lt_irrefl, and_false, not_false_eq_true]
  · intro c hc
    simp only [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.trans h⟩

theorem lowCount_lt_iff {lev : Fin n → ℕ} {a b : Fin n} :
    lowCount lev a < lowCount lev b ↔ lev a < lev b := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.2 (lowCount_le_of_le (not_lt.1 h')))
  · exact lowCount_lt_of_lt

theorem rhoU_lowCount (lev : Fin n → ℕ) : rhoU (lowCount lev) = rhoU lev := by
  funext a
  simp only [rhoU, lowCount_lt_iff]

theorem muQ_lowCount (lam : Fin n → ℤ) (lev : Fin n → ℕ) : muQ lam (lowCount lev) = muQ lam lev := by
  unfold muQ
  rw [rhoU_lowCount]

theorem isLev_lowCount {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    IsLev lam (lowCount lev) := by
  refine ⟨fun a b hab => lowCount_le_of_le (h.1 hab), fun a b hab => h.2 a b ?_⟩
  rcases lt_trichotomy (lev a) (lev b) with h1 | h1 | h1
  · exact absurd hab (ne_of_lt (lowCount_lt_of_lt h1))
  · exact h1
  · exact absurd hab (ne_of_gt (lowCount_lt_of_lt h1))

theorem exists_compress (lam : Fin n → ℤ) (lev : Fin n → ℕ) (h : IsLev lam lev) :
    ∃ l : Fin n → Fin n, (IsLev lam fun a => (l a : ℕ)) ∧ (muQ lam fun a => (l a : ℕ)) = muQ lam lev := by
  exact ⟨fun a => ⟨lowCount lev a, lowCount_lt lev a⟩, isLev_lowCount h, muQ_lowCount lam lev⟩

theorem muQ_mem_harmSet {lam : Fin n → ℤ} {lev : Fin n → ℕ} (h : IsLev lam lev) :
    muQ lam lev ∈ harmSet lam := by
  obtain ⟨l, hl, he⟩ := exists_compress lam lev h
  unfold harmSet
  rw [Finset.mem_image]
  refine ⟨l, ?_, he⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hl

end GlobalTheory.CompanionTheory.LevelCompress
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolic
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZFun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lastCol {n : ℕ} (u : MirUin k n) : Fin n → k :=
  fun i => (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)

theorem continuous_lastCol (n : ℕ) : Continuous (lastCol k (n := n)) := by
  refine continuous_pi fun i => ?_
  have h : Continuous fun u : MirUin k n =>
      (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact h.matrix_elem _ _

theorem thetaA_apply (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (u : MirUin k n) :
    thetaA k ψ a u = Circle.toUnits (ψ (a ⬝ᵥ lastCol k u)) := by
  obtain ⟨w, hw⟩ : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n := Subgroup.mem_subgroupOf.1 u.2
  have key : (unipEquiv k n).symm ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u) = w := by
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    exact hw.symm
  have hcol : lastCol k u = w.toAdd := by
    funext i
    simp only [lastCol, ← hw]
    exact unip_apply_castSucc_last k n w i
  show Circle.toUnits (ψ (a ⬝ᵥ ((unipEquiv k n).symm
    ((Subgroup.subgroupOfEquivOfLe (MirU_le_Mir k n)) u)).toAdd)) = _
  rw [key, hcol]

theorem isOpen_addChar_eq_one (ψ : AddChar k Circle) (hψ : Continuous ψ) : IsOpen {x : k | ψ x = 1} := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ψ x = 1 := hx
  have ht : Filter.Tendsto (fun y : k => y - x) (𝓝 x) (𝓝 0) := by
    simpa using (continuous_sub_right x).tendsto x
  filter_upwards [ht (cball_mem_nhds s)] with y hy
  have h1 : ψ (y - x) = 1 := hs _ hy
  have h2 : ψ y = ψ (y - x) * ψ x := by rw [← AddChar.map_add_eq_mul, sub_add_cancel]
  show ψ y = 1
  rw [h2, h1, hx', one_mul]

theorem thetaOpen : ThetaOpen k := by
  intro ψ hψ n a
  have hc : Continuous fun u : MirUin k n => a ⬝ᵥ lastCol k u := by
    have h := continuous_lastCol k n
    simp only [dotProduct]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp h)
  have he : ((thetaA k ψ a).ker : Set (MirUin k n)) =
      (fun u : MirUin k n => a ⬝ᵥ lastCol k u) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, thetaA_apply, Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (isOpen_addChar_eq_one k ψ hψ).preimage hc

end GlobalTheory.CompanionTheory.BZFun

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaOpenMirabolicStatement
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_open_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ThetaOpen k := by
  first | exact @GlobalTheory.CompanionTheory.BZFun.thetaOpen | exact GlobalTheory.CompanionTheory.BZFun.thetaOpen | (intros; apply GlobalTheory.CompanionTheory.BZFun.thetaOpen <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantCoweightAntitonePairingSum
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.LamGap

theorem sum_lt_indicator (N m : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if (i : ℕ) < m then 1 else 0) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < m then 1 else 0) N, Finset.sum_boole]
  have hf : (Finset.range N).filter (fun i => i < m) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hf, Finset.card_range, Nat.cast_id]

theorem sum_ge_indicator (N m : ℕ) (h : m ≤ N) :
    (∑ i : Fin N, if m ≤ (i : ℕ) then 1 else 0) = N - m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if m ≤ i then 1 else 0) N, Finset.sum_boole]
  have hf : (Finset.range N).filter (fun i => m ≤ i) = Finset.Ico m N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Nat.card_Ico, Nat.cast_id]

theorem lamOf_sub {N : ℕ} (g : Fin (N - 1) → ℕ) (i i' : Fin N) (h : i < i') :
    (Zls.lamOf g i - Zls.lamOf g i').toNat
      = ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 := by
  have hii : (i : ℕ) < (i' : ℕ) := h
  have key : Zls.lamOf g i - Zls.lamOf g i'
      = ((∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 : ℕ) : ℤ) := by
    simp only [Zls.lamOf]
    rw [← Finset.sum_sub_distrib, Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp_all <;> omega
  rw [key, Int.toNat_natCast]

theorem gap_count (N : ℕ) (c j : ℕ) (hj : j + 1 ≤ N) :
    (∑ i : Fin N, ∑ i' : Fin N, if (i : ℕ) ≤ j ∧ j < (i' : ℕ) then c else 0)
      = c * ((j + 1) * (N - (j + 1))) := by
  calc (∑ i : Fin N, ∑ i' : Fin N, if (i : ℕ) ≤ j ∧ j < (i' : ℕ) then c else 0)
      = ∑ i : Fin N, ∑ i' : Fin N,
          c * ((if (i : ℕ) < j + 1 then 1 else 0) * (if j + 1 ≤ (i' : ℕ) then 1 else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
        have a1 : ((i : ℕ) < j + 1) ↔ (i : ℕ) ≤ j := by omega
        have a2 : (j + 1 ≤ (i' : ℕ)) ↔ j < (i' : ℕ) := by omega
        simp only [a1, a2]
        split_ifs <;> simp_all
    _ = c * ((∑ i : Fin N, if (i : ℕ) < j + 1 then 1 else 0) *
          (∑ i' : Fin N, if j + 1 ≤ (i' : ℕ) then 1 else 0)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = c * ((j + 1) * (N - (j + 1))) := by
        rw [sum_lt_indicator N (j + 1) hj, sum_ge_indicator N (j + 1) hj]

theorem lamOf_antitone_gap_sum (N : ℕ) (g : Fin (N - 1) → ℕ) :
    Antitone (Zls.lamOf g) ∧
      (∑ i : Fin N, ∑ i' : Fin N,
          if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
        = ∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · simp only [Zls.lamOf]
    refine Finset.sum_le_sum fun j _ => ?_
    have hab' : (a : ℕ) ≤ (b : ℕ) := hab
    split_ifs <;> omega
  · have step : ∀ i i' : Fin N,
        (if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
          = ∑ j : Fin (N - 1), if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 := by
      intro i i'
      split_ifs with hlt
      · exact lamOf_sub g i i' hlt
      · symm
        refine Finset.sum_eq_zero fun j _ => ?_
        have hn : ¬ ((i : ℕ) < (i' : ℕ)) := hlt
        rw [if_neg]
        rintro ⟨h1, h2⟩
        omega
    calc (∑ i : Fin N, ∑ i' : Fin N,
            if i < i' then (Zls.lamOf g i - Zls.lamOf g i').toNat else 0)
        = ∑ i : Fin N, ∑ i' : Fin N, ∑ j : Fin (N - 1),
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => step i i'
      _ = ∑ i : Fin N, ∑ j : Fin (N - 1), ∑ i' : Fin N,
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ j : Fin (N - 1), ∑ i : Fin N, ∑ i' : Fin N,
            if (i : ℕ) ≤ (j : ℕ) ∧ (j : ℕ) < (i' : ℕ) then g j else 0 :=
          Finset.sum_comm
      _ = ∑ j : Fin (N - 1), g j * (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          exact gap_count N (g j) j (by have := j.isLt; omega)

end GlobalTheory.CompanionTheory.LamGap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalar
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SchurCentre

theorem scalar_acts_by_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  intro k _ _ _ _ N V _ _ π hs hirr hadm t
  haveI := hirr

  have hz : ∀ g : GL (Fin N) k, g * Matrix.GeneralLinearGroup.scalar (Fin N) t =
      Matrix.GeneralLinearGroup.scalar (Fin N) t * g := by
    intro g
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]
  set z := Matrix.GeneralLinearGroup.scalar (Fin N) t with hzdef
  have hcomm : ∀ (g : GL (Fin N) k) (w : V), π g (π z w) = π z (π g w) := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]

  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    change (⊥ : Submodule ℂ V) = ⊤
    ext u
    simp [h u]

  let S : Subgroup (GL (Fin N) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  let K : Subgroup (GL (Fin N) k) := GlobalTheory.SplitWeil.KO k (Fin N) ⊓ S
  have hKo : IsOpen (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isOpen_KO (k := k) (n := Fin N)).inter (hs v)
  have hKc : IsCompact (K : Set (GL (Fin N) k)) :=
    (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin N)).of_isClosed_subset
      (Subgroup.isClosed_of_isOpen K hKo) (fun _ h => h.1)
  haveI hfd : FiniteDimensional ℂ (fixed π K) := hadm.2 K hKo hKc
  have hmem : ∀ w : V, w ∈ fixed π K ↔ ∀ h : K, π (h : GL (Fin N) k) w = w := by
    intro w
    show (∀ h : K, _ = _) ↔ _
    simp
  have hvK : v ∈ fixed π K := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (fixed π K) :=
    ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hst : ∀ w ∈ fixed π K, π z w ∈ fixed π K := by
    intro w hw
    refine (hmem _).2 fun h => ?_
    rw [hcomm, (hmem w).1 hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((π z).restrict hst)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : V) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hwc : π z (w : V) = c • (w : V) := by
    have := congrArg Subtype.val hw.apply_eq_smul
    simpa using this

  let f : Representation.IntertwiningMap π π :=
    { toLinearMap := π z - c • LinearMap.id
      isIntertwining' := by
        intro g
        ext u
        simp [hcomm] }
  refine ⟨c, fun u => ?_⟩
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · exfalso
    apply hw0
    apply hb.1
    show π z (w : V) - c • (w : V) = f 0
    rw [hwc, sub_self, map_zero]
  · have := congrArg (fun F : Representation.IntertwiningMap π π => F u) h0
    have h1 : π z u - c • u = 0 := this
    exact sub_eq_zero.1 h1

end GlobalTheory.CompanionTheory.SchurCentre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleIrreducibleCentralScalarStatement
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_irreducible_central_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  first | exact @GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar | exact GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar | (intros; apply GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFacts
noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.HbBasis

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.LfSt

variable {n : ℕ}

theorem sum_single_one : ∑ a : Fin n, (Matrix.single a a (1 : ℂ) : Mat n) = 1 := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    refine Finset.sum_eq_zero fun x _ => if_neg fun hx => h (hx.1.symm.trans hx.2)

theorem sqrt_two_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
  GlobalTheory.CompanionTheory.TopClass.sqrt_two_inv_sq

theorem hb_mul_self (a b : Fin n) :
    (hb (a, b) : Mat n) * hb (a, b) = (1 / 2 : ℂ) • (Matrix.single a a 1 + Matrix.single b b 1) := by
  have hs := sqrt_two_inv_sq
  by_cases h : a = b
  · subst h
    have : (hb (a, a) : Mat n) = Matrix.single a a 1 := by simp [hb]
    rw [this, Matrix.single_mul_single_same, ← two_smul ℂ, smul_smul]
    norm_num
  · have hne : b ≠ a := fun e => h e.symm
    by_cases h' : a < b
    · have : (hb (a, b) : Mat n) = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (Matrix.single a b 1 + Matrix.single b a 1) := by
        simp [hb, h, h']
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp [add_comm]
    · have : (hb (a, b) : Mat n) =
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) • (Matrix.single a b 1 - Matrix.single b a 1) := by
        simp [hb, h, h']
      have hc : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) = -(1 / 2) := by
        calc _ = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (Complex.I * Complex.I) := by ring
          _ = _ := by rw [hs, Complex.I_mul_I]; ring
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp only [mul_one, sub_zero, zero_sub, neg_smul, smul_neg, smul_sub, smul_add]
      abel

theorem sum_hb_mul_self : ∑ p, (hb p : Mat n) * hb p = (n : ℂ) • 1 := by
  rw [Fintype.sum_prod_type]
  simp only [hb_mul_self, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, sum_single_one]
  rw [← Nat.cast_smul_eq_nsmul ℂ n (1 : Mat n), ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

theorem coords_one (p : Fin n × Fin n) : ((coords (1 : Mat n) p : ℝ) : ℂ) = (hb p : Mat n).trace := by
  have := GlobalTheory.CompanionTheory.ConeLin.re_trace (1 : Mat n) (by simp) p
  simpa [coords] using this

theorem hOf_coords {H : Mat n} (hH : H.IsHermitian) : hOf (coords H) = H :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_re H hH

theorem coords_hOf (v : Fin n × Fin n → ℝ) : coords (hOf v) = v := by
  funext q
  have : (hOf v * hb q).trace = (v q : ℂ) := by
    classical
    simp [hOf, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
      GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb]
  simp [coords, this]

theorem hOf_isHermitian (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_herm v

theorem sum_trace_smul_hb : ∑ p, (hb p : Mat n).trace • hb p = 1 := by
  have h := hOf_coords (H := (1 : Mat n)) Matrix.isHermitian_one
  simpa only [hOf, coords_one] using h

theorem oPt_mem_cone : oPt n ∈ cone n := by
  show (hOf (coords (1 : Mat n))).PosDef
  rw [hOf_coords Matrix.isHermitian_one]
  exact Matrix.PosDef.one

theorem hbFacts : HbFacts := fun _ =>
  ⟨GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose, GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb, fun _ hH => hOf_coords hH,
    coords_hOf, hOf_isHermitian, sum_hb_mul_self, sum_trace_smul_hb, oPt_mem_cone⟩

end GlobalTheory.CompanionTheory.HbBasis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_facts : PositivityTheory.RgBcC.LfSt.HbFacts := by
  first | exact @GlobalTheory.CompanionTheory.HbBasis.hbFacts | exact GlobalTheory.CompanionTheory.HbBasis.hbFacts | (intros; apply GlobalTheory.CompanionTheory.HbBasis.hbFacts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorExists
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeKm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_span_unif_pow_iff (m : ℕ) (a : 𝒪[k]) :
    a ∈ Ideal.span {Zls.unif k ^ m} ↔ (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (a : k) ∈ 𝒪[k] := by
  have hc : (((Zls.unifU k ^ m : kˣ)) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k) := by
    simp [Zls.unifU]
    rfl
  have hne : ((Zls.unif k ^ m : 𝒪[k]) : k) ≠ 0 := by
    rw [← hc]; exact Units.ne_zero _
  have hinv : (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hc]
  rw [Ideal.mem_span_singleton', hinv]
  constructor
  · rintro ⟨b, rfl⟩
    have : ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * ((b * Zls.unif k ^ m : 𝒪[k]) : k) = (b : k) := by
      rw [MulMemClass.coe_mul]
      field_simp
    rw [this]
    exact b.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul]
    change ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * (a : k) * _ = _
    field_simp

theorem mem_Km_iff {N m : ℕ} (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j ∈ 𝒪[k] := by
  have key : ∀ (u : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val - 1) i j =
        ((u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j : 𝒪[k]) : k) := by
    intro u i j
    by_cases h : i = j
    · subst h
      simp [Matrix.GeneralLinearGroup.map_apply]
      rfl
    · simp [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply_ne h]
      rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq]
    have h := congrArg (fun x : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => x.val i j)
      (MonoidHom.mem_ker.1 hu)
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 (Units.ext (Matrix.ext fun i j => ?_)), rfl⟩
    have h' := h i j
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq] at h'
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h'

theorem continuous_entry_Km (N : ℕ) (c : k) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k => c * (g.val - 1) i j :=
  continuous_const.mul
    (((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).sub continuous_const).matrix_elem i j)

theorem coe_Km_eq (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) = (KO k (Fin N) : Set (GL (Fin N) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin N) k => (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j) ⁻¹'
        (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (show IsOpen (𝒪[k] : Set k) from Valuation.isOpen_integer).preimage (continuous_entry_Km N _ i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
    (show IsCompact (𝒪[k] : Set k) from IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed.preimage
      (continuous_entry_Km N _ i j))

theorem totallyDisconnected_GL (N : ℕ) : TotallyDisconnectedSpace (GL (Fin N) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  exact ⟨(GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem exists_isHeckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    ∀ (m : ℕ) (g : GL (Fin N) k), ∃ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m g T := by
  intro k _ _ _ _ N V _ _ π hπ m g
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI := totallyDisconnected_GL (k := k) N
  have hKc := isCompact_Km (k := k) N m
  have hKo := isOpen_Km (k := k) N m
  have hπ' : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hfix : ∀ w : GroundTheory.Automorphic.fixedVectors π (Zls.Km k N m),
      (w : V) ∈ fixed π (Zls.Km k N m) := fun w h => by
    simpa using w.2 h h.2
  refine ⟨LinearMap.codRestrict (fixed π (Zls.Km k N m))
    ((Submodule.subtype _) ∘ₗ GroundTheory.Automorphic.fixedProj π hπ' hKc hKo ∘ₗ π g ∘ₗ
      (fixed π (Zls.Km k N m)).subtype) fun v => hfix _, ?_⟩
  intro v l hl
  have hs := GroundTheory.Automorphic.sub_fixedProj_mem hπ' hKc hKo (π g (v : V))
  have h0 := GroundTheory.Automorphic.coinvariantsKer_le_ker_of_invariant (ρ := π) (K := Zls.Km k N m) (f := l)
    (fun x hx w => LinearMap.congr_fun (hl x hx) w) hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.HeckeKm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductDropZeroFactors
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductDropZeroFactors
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FineProd.TensorLine

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) : Nonempty (V ≃ₗ[ℂ] ℂ) := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ := ⟨Submodule.span ℂ {v}, fun g w hw => by
    rw [Subsingleton.elim g 1, map_one]; exact hw⟩
  have hvS : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
  have hS : S = ⊤ := by
    rcases hi.eq_bot_or_eq_top S with h | h
    · exfalso
      rw [h] at hvS
      exact hv ((Submodule.mem_bot ℂ).1 hvS)
    · exact h
  have htop : ∀ w : V, w ∈ Submodule.span ℂ {v} := fun w => by
    have : w ∈ S.toSubmodule := by
      rw [hS]
      exact (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ V))
    exact this
  refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℂ V v) ⟨?_, ?_⟩).symm⟩
  · exact LinearMap.ker_eq_bot.1 (LinearMap.ker_toSpanSingleton ℂ hv)
  · intro w
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (htop w)
    exact ⟨c, by simpa using hc⟩

theorem subsingleton_GL {k : Type} [Field k] {n : ℕ} (h : n = 0) : Subsingleton (GL (Fin n) k) := by
  subst h
  exact ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩

variable {r r' : ℕ}

abbrev Off (o : Fin r' → Fin r) : Type := {j : Fin r // j ∉ Set.range o}

def blockEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) : Fin r' ⊕ Off o ≃ Fin r :=
  Equiv.ofBijective (Sum.elim o Subtype.val) (by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (ho h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro j
      by_cases hj : j ∈ Set.range o
      · obtain ⟨a, rfl⟩ := hj
        exact ⟨Sum.inl a, rfl⟩
      · exact ⟨Sum.inr ⟨j, hj⟩, rfl⟩)

variable {X : Fin r → Type} [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)]


open scoped Classical in
def dropEquiv (o : Fin r' → Fin r) (ho : Function.Injective o) (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) :
    (⨂[ℂ] j, X j) ≃ₗ[ℂ] ⨂[ℂ] a, X (o a) :=
  (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm).trans <|
    ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm).trans <|
      (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv)).trans
        (TensorProduct.rid ℂ _)


open scoped Classical in
theorem dropEquiv_tprod (o : Fin r' → Fin r) (ho : Function.Injective o)
    (φ : ∀ c : Off o, X c ≃ₗ[ℂ] ℂ) (x : ∀ j, X j) :
    dropEquiv o ho φ (PiTensorProduct.tprod ℂ x) =
      (∏ c : Off o, φ c (x c)) • PiTensorProduct.tprod ℂ fun a => x (o a) := by
  have h1 : PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x) =
      PiTensorProduct.tprod ℂ fun i => x (blockEquiv o ho i) :=
    PiTensorProduct.reindex_tprod _ _
  have h2 := PiTensorProduct.tmulEquivDep_symm_apply ℂ (fun i => X (blockEquiv o ho i))
    (fun i => x (blockEquiv o ho i))
  have h3 : (PiTensorProduct.congr fun c : Off o => φ c)
      (PiTensorProduct.tprod ℂ fun c : Off o => x c) = PiTensorProduct.tprod ℂ fun c : Off o => φ c (x c) :=
    PiTensorProduct.congr_tprod _ _
  have ht : ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
      (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c)) =
      (PiTensorProduct.tprod ℂ fun a => x (o a)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun c : Off o => x c) :=
    (congrArg _ h1).trans h2
  show (TensorProduct.rid ℂ _) ((TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] a, X (o a)))
        ((PiTensorProduct.congr fun c : Off o => φ c).trans
          (PiTensorProduct.constantBaseRingEquiv (Off o) ℂ).toLinearEquiv))
      ((PiTensorProduct.tmulEquivDep ℂ fun i => X (blockEquiv o ho i)).symm
        (PiTensorProduct.reindex ℂ X (blockEquiv o ho).symm (PiTensorProduct.tprod ℂ x)) :
        TensorProduct ℂ (⨂[ℂ] a, X (o a)) (⨂[ℂ] c : Off o, X c))) = _
  rw [ht, TensorProduct.congr_tmul, LinearEquiv.trans_apply, h3, TensorProduct.rid_tmul]
  congr 1
  exact PiTensorProduct.constantBaseRingEquiv_tprod _

theorem piTensor_drop_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' : ℕ} (y : Fin r → IrrGL (k := k)) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → Nonempty ((piTensor fun j => (y j).rep).Equiv ((piTensor fun a => (y (o a)).rep).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) (fun j => (y j).1) o) : Representation ℂ (Levi k fun j => Fin (y j).1) _)) := by
  intro k _ _ _ _ r r' y o ho hy
  have hz : ∀ c : Off o, (y c).1 = 0 := fun c => by
    by_contra h
    exact c.2 (hy c h)
  have hφ : ∀ c : Off o, Nonempty ((y c).2.rep.V ≃ₗ[ℂ] ℂ) := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    exact exists_line (y c).2.rep.irr
  let φ : ∀ c : Off o, (y c).2.rep.V ≃ₗ[ℂ] ℂ := fun c => (hφ c).some
  refine ⟨Representation.Equiv.mk (dropEquiv o ho.injective φ) fun g => ?_⟩
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  have hc : ∀ c : Off o, (y c).rep (g c) (x c) = x c := fun c => by
    haveI := subsingleton_GL (k := k) (hz c)
    rw [Subsingleton.elim (g c) 1, map_one]
    rfl
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    piTensor_tprod, dropEquiv_tprod, hc, map_smul]
  congr 1
  exact (piTensor_tprod (fun a => (y (o a)).rep) (fun a => g (o a)) (fun a => x (o a))).symm

end GlobalTheory.CompanionTheory.FineProd.TensorLine

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductDropZeroFactorsStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_drop_zero_factors : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' : ℕ} (y : Fin r → IrrGL (k := k)) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → Nonempty ((piTensor fun j => (y j).rep).Equiv ((piTensor fun a => (y (o a)).rep).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) (fun j => (y j).1) o) : Representation ℂ (Levi k fun j => Fin (y j).1) _)) := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv | exact GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv | (intros; apply GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive
noncomputable section

open Matrix ValuativeRel GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZMirExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' {a b} ha hb := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    have hb' : valuation k b ≤ valuation k (s : k) := hb
    exact (Valuation.map_add _ a b).trans (max_le ha' hb')
  neg_mem' {a} ha := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    show valuation k (-a) ≤ valuation k (s : k)
    rwa [Valuation.map_neg]

theorem exists_ball_of_finset (T : Finset k) : ∃ s : kˣ, ∀ x ∈ T, x ∈ cball s := by
  classical
  refine Finset.induction_on T ?_ ?_
  · exact ⟨1, by simp⟩
  · intro a T _ ih
    obtain ⟨s, hs⟩ := ih
    by_cases h : valuation k a ≤ valuation k (s : k)
    · refine ⟨s, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hs x hx
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact h (by simp)
      refine ⟨Units.mk0 a ha0, fun x hx => ?_⟩
      show valuation k x ≤ valuation k a
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · have hx' : valuation k x ≤ valuation k (s : k) := hs x hx
        exact le_trans hx' (le_of_lt (not_le.1 h))

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

theorem continuous_colMat (n : ℕ) : Continuous (colMat k n) := by
  refine continuous_matrix fun i j => ?_
  unfold GlobalTheory.BZMir.colMat
  by_cases hj : j = Fin.last n
  · simp only [if_pos hj]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simp only [Fin.lastCases_castSucc]
      exact continuous_apply i
    · simp only [Fin.lastCases_last]
      exact continuous_const
  · simp only [if_neg hj]
    exact continuous_const

theorem continuous_unipMir (n : ℕ) :
    Continuous (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) := by
  have hval : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n v :=
    continuous_const.add (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hinv : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - GlobalTheory.BZMir.colMat k n v :=
    continuous_const.sub (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hGL : Continuous fun v : Fin n → k =>
      GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

def ballGroup (n : ℕ) (s : kˣ) : Subgroup (Mir k n) :=
  (AddSubgroup.toSubgroup (AddSubgroup.pi Set.univ fun _ : Fin n => ballSub s)).map (unipMir n)

theorem ballGroup_le (n : ℕ) (s : kˣ) : ballGroup (k := k) n s ≤ MirUin k n := by
  rintro _ ⟨v, -, rfl⟩
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

theorem coe_ballGroup (n : ℕ) (s : kˣ) : (ballGroup (k := k) n s : Set (Mir k n)) =
    (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) '' Set.univ.pi fun _ => cball s := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.coe_map]
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.toAdd v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

theorem isCompact_ballGroup (n : ℕ) (s : kˣ) : IsCompact (ballGroup (k := k) n s : Set (Mir k n)) := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.coe_ballGroup]
  exact (isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s).image
    (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_unipMir n)

theorem exhaust (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.Exhaust k := by
  classical
  intro n S hS
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.BZMirExhaust.exists_ball_of_finset
    ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p =>
      ((p.1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc p.2) (Fin.last n))
  refine ⟨GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup n s, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup_le n s, ?_,
    GlobalTheory.CompanionTheory.BZMirExhaust.isCompact_ballGroup n s⟩
  intro g hg
  have hgU := hS hg
  rw [SetLike.mem_coe, GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hgU
  obtain ⟨v, hv⟩ := hgU
  rw [Finset.mem_coe] at hg
  rw [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.mem_map]
  refine ⟨v, ?_, Subtype.ext hv⟩
  show ∀ i ∈ Set.univ, Multiplicative.toAdd v i ∈ GlobalTheory.CompanionTheory.BZMirExhaust.ballSub s
  intro i _
  have hvi := GlobalTheory.BZMir.unip_apply_castSucc_last k n v i
  rw [hv] at hvi
  show Multiplicative.toAdd v i ∈ GlobalTheory.SplitWeil.cball s
  rw [← hvi]
  exact hs _ (Finset.mem_image.2 ⟨(g, i), Finset.mem_product.2 ⟨hg, Finset.mem_univ i⟩, rfl⟩)

end GlobalTheory.CompanionTheory.BZMirExhaust

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustiveStatement
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_filtration_exhaustive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.Exhaust k := by
  first | exact @GlobalTheory.CompanionTheory.BZMirExhaust.exhaust | exact GlobalTheory.CompanionTheory.BZMirExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.BZMirExhaust.exhaust <;> assumption)
end
end
