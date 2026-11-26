module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfEigencharacter
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegrees
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegrees
open GlobalTheory.DiscSpec

namespace GlobalTheory.CompanionTheory.Rigid


open Classical in
theorem card_spehExp_eq (d m : ℕ) (hm : 1 ≤ m) :
    ((Finset.univ : Finset (Fin d)).filter (fun k => ((m : ℝ) - 1) / 2 = spehExp d k)).card =
      if m ≤ d ∧ Even (d - m) then 1 else 0 := by
  split_ifs with h
  · obtain ⟨hle, t, ht⟩ := h
    have hd : d = m + 2 * t := by omega
    have hdR : (d : ℝ) = m + 2 * t := by exact_mod_cast hd
    have htd : t < d := by omega
    rw [Finset.card_eq_one]
    refine ⟨⟨t, htd⟩, ?_⟩
    ext k
    rw [Finset.mem_filter, Finset.mem_singleton]
    simp only [Finset.mem_univ, true_and, spehExp]
    constructor
    · intro hk
      apply Fin.ext
      have : ((k : ℕ) : ℝ) = t := by linarith
      exact_mod_cast this
    · rintro rfl
      show ((m : ℝ) - 1) / 2 = ((d : ℝ) - 1) / 2 - (t : ℝ)
      linarith
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _ hk
    apply h
    simp only [spehExp] at hk
    have h1 : (d : ℝ) = m + 2 * ((k : ℕ) : ℝ) := by linarith
    have h2 : d = m + 2 * (k : ℕ) := by exact_mod_cast h1
    exact ⟨by omega, (k : ℕ), by omega⟩


open Classical in
theorem count_strings {X ι : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) (x : X) (m : ℕ) (hm : 1 ≤ m) :
    (GlobalTheory.Rigid.strings p d).count (x, ((m : ℝ) - 1) / 2) =
      (Finset.univ.filter fun i => p i = x ∧ m ≤ d i ∧ Even (d i - m)).card := by
  unfold GlobalTheory.Rigid.strings
  rw [Multiset.count_sum', Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.count_map]
  by_cases hx : p i = x
  · have h := card_spehExp_eq (d i) m hm
    simp only [hx, true_and, Prod.mk.injEq]
    rw [← h]
    rfl
  · have hx' : ¬ x = p i := fun e => hx e.symm
    simp [hx, hx']


open Classical in
theorem card_fibre_add {ι : Type} {X : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) (x : X) (m : ℕ) :
    (Finset.univ.filter fun i => p i = x ∧ d i = m).card +
        (Finset.univ.filter fun i => p i = x ∧ m + 2 ≤ d i ∧ Even (d i - (m + 2))).card =
      (Finset.univ.filter fun i => p i = x ∧ m ≤ d i ∧ Even (d i - m)).card := by
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : p i = x
  · simp only [hx, true_and, Nat.even_iff]
    split_ifs <;> omega
  · simp [hx]


open Classical in
theorem card_fibre_eq {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X)
    (d' : κ → ℕ) (hd : ∀ i, 1 ≤ d i) (hd' : ∀ j, 1 ≤ d' j)
    (h : GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d') (x : X) (m : ℕ) :
    (Finset.univ.filter fun i => p i = x ∧ d i = m).card =
      (Finset.univ.filter fun j => p' j = x ∧ d' j = m).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : (Finset.univ.filter fun i => p i = x ∧ d i = 0) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun i _ hi => by have := hd i; omega
    have h2 : (Finset.univ.filter fun j => p' j = x ∧ d' j = 0) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun j _ hj => by have := hd' j; omega
    rw [h1, h2, Finset.card_empty, Finset.card_empty]
  · have a1 := card_fibre_add p d x m
    have a2 := card_fibre_add p' d' x m
    have c1 := count_strings p d x m hm
    have c2 := count_strings p' d' x m hm
    have e1 := count_strings p d x (m + 2) (by omega)
    have e2 := count_strings p' d' x (m + 2) (by omega)
    rw [h] at c1 e1
    omega

theorem strings_rigid {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X)
    (d' : κ → ℕ) (hd : ∀ i, 1 ≤ d i) (hd' : ∀ j, 1 ≤ d' j)
    (h : GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d') :
    ∃ s : ι ≃ κ, ∀ i, p i = p' (s i) ∧ d i = d' (s i) := by
  classical
  have hc : ∀ c : X × ℕ, Fintype.card {i // (p i, d i) = c} = Fintype.card {j // (p' j, d' j) = c} := by
    rintro ⟨x, m⟩
    have := card_fibre_eq p d p' d' hd hd' h x m
    simp only [Fintype.card_subtype, Prod.mk.injEq]
    convert this
  let e : ∀ c : X × ℕ, {i // (p i, d i) = c} ≃ {j // (p' j, d' j) = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv e, fun i => ?_⟩
  have := Equiv.ofFiberEquiv_map e i
  exact ⟨(congrArg Prod.fst this).symm, (congrArg Prod.snd this).symm⟩

end GlobalTheory.CompanionTheory.Rigid
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegreesStatement
open GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiset_of_strings_determines_points_degrees : ∀ {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X) (d' : κ → ℕ), (∀ i, 1 ≤ d i) → (∀ j, 1 ≤ d' j) → GlobalTheory.Rigid.strings p d = GlobalTheory.Rigid.strings p' d' → ∃ s : ι ≃ κ, ∀ i, p i = p' (s i) ∧ d i = d' (s i) := by
  first | exact @GlobalTheory.CompanionTheory.Rigid.strings_rigid | exact GlobalTheory.CompanionTheory.Rigid.strings_rigid | (intros; apply GlobalTheory.CompanionTheory.Rigid.strings_rigid <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksExponent
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.StandardBlocks

theorem stdBlocks_one {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) (a : Fin n) (i : Fin 1) :
    stdBlocks (fun _ : Fin n => 1) hd ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [hi]

theorem blk_stdBlocks {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) (i : Fin n) :
    blk (stdBlocks (fun _ : Fin n => 1) hd) i = i := by
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective i
  rw [blk_apply]
  exact (stdBlocks_one hd a p).symm

theorem unipRad_stdBlocks (k : Type) [Field k] {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) :
    unipRad k (stdBlocks (fun _ : Fin n => 1) hd) = unipB k (Fin n) := by
  have hb2 : ∀ i : Fin n, blk (points (Fin n)) i = i := fun i => by
    have h := blk_apply (points (Fin n)) i ()
    rwa [points_apply] at h
  ext g
  rw [unipB, mem_unipRad, mem_unipRad, mem_parab, mem_parab]
  simp only [blk_stdBlocks, hb2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a i j => ?_⟩
    have h := h2 a (0 : Fin 1) (0 : Fin 1)
    simp only [stdBlocks_one] at h
    simp only [points_apply]
    rw [h]
    simp [Matrix.one_apply]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a i j => ?_⟩
    have h := h2 a () ()
    simp only [points_apply] at h
    simp only [stdBlocks_one]
    obtain rfl : i = j := Subsingleton.elim i j
    rw [h]
    simp [Matrix.one_apply]

theorem leviEmb_stdBlocks (k : Type) [Field k] {n : ℕ} (hd : ∑ _a : Fin n, 1 = n)
    (t : Levi k fun _ : Fin n => Fin 1) :
    leviEmb k (stdBlocks (fun _ : Fin n => 1) hd) t =
      diagT k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective j
  rw [val_diagT]
  by_cases hab : a = b
  · subst hab
    have hpq : p = q := Subsingleton.elim _ _
    subst hpq
    rw [leviEmb_apply_same, stdBlocks_one]
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, Subsingleton.elim p 0]
  · rw [leviEmb_apply_ne k _ t hab, stdBlocks_one, stdBlocks_one, Matrix.diagonal_apply_ne _ hab]

theorem deltaHalf_stdBlocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Levi k fun _ : Fin n => Fin 1) :
    deltaHalf k (fun _ : Fin n => Fin 1) t =
      deltaHalf k (fun _ : Fin n => Unit)
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp_fin (fun _ : Fin n => Fin 1) (fun _ => Fintype.card_fin 1) a,
    modExp_fin (fun _ : Fin n => Unit) (fun _ => Fintype.card_unit) a]
  congr 1
  exact (congrFun ((leviTorus k (Fin n)).symm_apply_apply
    fun a => Matrix.GeneralLinearGroup.det (t a)) a).symm

theorem twKer_one_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (h : N = N') : twKer π N 1 = twKer π N' 1 := by
  subst h
  rfl

theorem torusChar_stdBlocks {k : Type} [Field k] {n : ℕ} (χ : Fin n → kˣ →* ℂˣ)
    (t : ∀ _ : Fin n, GL (Fin 1) k) :
    PositivityTheory.Lbc.torusChar χ t =
      (GlobalTheory.SmGL.torusChar χ (fun a => Matrix.GeneralLinearGroup.det (t a)) : ℂ) := by
  rw [PositivityTheory.Lbc.torusChar, GlobalTheory.SmGL.torusChar, MonoidHom.finsetProd_apply, Units.coe_prod]
  rfl

private theorem smul_mk_eq_smul_mk_of_submodule_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    {p q : Submodule ℂ V} (h : p = q) (a b : ℂ) (u w : V)
    (hk : a • (Submodule.Quotient.mk u : V ⧸ p) = b • Submodule.Quotient.mk w) :
    a • (Submodule.Quotient.mk u : V ⧸ q) = b • Submodule.Quotient.mk w := by
  subst h
  exact hk

theorem stdBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.StdBridge := by
  intro k _ _ _ _ n hd V _ _ π χ y hy heig
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 =
      twKer π (unipRad k (points (Fin n))) 1 :=
    twKer_one_congr π (unipRad_stdBlocks k hd)
  obtain ⟨w, rfl⟩ :=
    Submodule.Quotient.mk_surjective (twKer π (unipRad k (points (Fin n))) 1) y
  refine ⟨(Submodule.Quotient.mk w :
    V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1), ?_, ?_⟩
  · intro h
    apply hy
    have h' : w ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    rw [hK] at h'
    exact (Submodule.Quotient.mk_eq_zero _).mpr h'
  · intro t
    have key : (SmGL.jac (points (Fin n)) π
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)))
          (Submodule.Quotient.mk w) =
        ((GlobalTheory.SmGL.torusChar χ fun a => Matrix.GeneralLinearGroup.det (t a) : ℂˣ) : ℂ) •
          Submodule.Quotient.mk w :=
      heig (fun a => Matrix.GeneralLinearGroup.det (t a))
    have hD : leviEmb k (points (Fin n))
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) =
        diagT k (Fin n) (fun a => Matrix.GeneralLinearGroup.det (t a)) := rfl
    rw [jac_mk, hD] at key
    have heq : (SmGL.jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (Submodule.Quotient.mk w) =
        PositivityTheory.Lbc.torusChar χ t • (Submodule.Quotient.mk w :
          V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1) := by
      rw [jac_mk, leviEmb_stdBlocks, deltaHalf_stdBlocks, torusChar_stdBlocks]
      exact smul_mk_eq_smul_mk_of_submodule_eq hK.symm _ _ _ _ key
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact heq

end GlobalTheory.CompanionTheory.StandardBlocks

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFinite
namespace GlobalTheory.CompanionTheory.HeckeEnd

open PositivityTheory.Rg.BcB.F.Tail.PExp

theorem hkE_fin : HkEFin := by
  intro G V _ _ _ ρ K f hf v
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  rw [finsum_eq_sum_of_support_subset (s := hf.toFinset),
    finsum_eq_sum_of_support_subset (s := hf.toFinset), LinearMap.sum_apply]
  · rfl
  all_goals
    intro q hq
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    rw [Function.mem_support] at hq
    exact hq (by simp [h])

end GlobalTheory.CompanionTheory.HeckeEnd
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeEigenFiniteStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_eigen_finite : PositivityTheory.Rg.BcB.F.Tail.PExp.HkEFin := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | exact GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin | (intros; apply GlobalTheory.CompanionTheory.HeckeEnd.hkE_fin <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatom
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatom
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FiniteLengthQuot

theorem exists_isCoatom_subrepresentation :
    ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  intro G V _ _ _ ρ hfl hnt
  have : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hfl).1
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨M, hM, -⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  exact ⟨M, hM⟩

end GlobalTheory.CompanionTheory.FiniteLengthQuot
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatomStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_exists_coatom : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  first | exact @GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation | exact GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation | (intros; apply GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixed
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepTensor

theorem extTensor_left {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (k : G) :
    extTensor ρ σ (k, 1) = TensorProduct.map (ρ k) LinearMap.id :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem extTensor_right {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (h : H) :
    extTensor ρ σ (1, h) = TensorProduct.map LinearMap.id (σ h) :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem contr_left {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Module.End ℂ V) (l : Module.Dual ℂ W) (v : V ⊗[ℂ] W) :
    A (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
      TensorProduct.rid ℂ V (LinearMap.lTensor V l (TensorProduct.map A LinearMap.id v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem contr_right {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (B : Module.End ℂ W) (l : Module.Dual ℂ V) (v : V ⊗[ℂ] W) :
    B (TensorProduct.lid ℂ W (LinearMap.rTensor W l v)) =
      TensorProduct.lid ℂ W (LinearMap.rTensor W l (TensorProduct.map LinearMap.id B v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    have := h k k.2
    show ρ (k : G) v = ((1 : K →* ℂˣ) k : ℂ) • v
    simpa using this

theorem contrFix : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  intro G H V W _ _ _ _ _ _ ρ σ K L v hv
  have hv' := mem_fixed_iff'.1 hv
  refine ⟨fun l => mem_fixed_iff'.2 fun k hk => ?_, fun l => mem_fixed_iff'.2 fun h hh => ?_⟩
  · have h1 := hv' (k, 1) ⟨hk, L.one_mem⟩
    rw [extTensor_left] at h1
    rw [contr_left, h1]
  · have h1 := hv' (1, h) ⟨K.one_mem, hh⟩
    rw [extTensor_right] at h1
    rw [contr_right, h1]

end GlobalTheory.CompanionTheory.RepTensor
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixedStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contraction_fixed : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  first | exact @GlobalTheory.CompanionTheory.RepTensor.contrFix | exact GlobalTheory.CompanionTheory.RepTensor.contrFix | (intros; apply GlobalTheory.CompanionTheory.RepTensor.contrFix <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubEigenTailHecke
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubEigenTailHecke
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep PositivityTheory.Rg.BcB.F.Tail.PExp GlobalTheory.CompanionTheory.SubEig

namespace GlobalTheory.CompanionTheory.SubEigIrr

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    simpa using h k.1 k.2

theorem hkS_eq_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (f : G → ℂ) (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v : V) :
    hkS ρ K f v = ∑ q ∈ hf.toFinset, f q.out • ρ q.out v := by
  unfold hkS
  refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
  simp only [Set.Finite.coe_toFinset]
  intro h0
  exact hq (by simp [h0])

theorem hkS_map {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : Representation.IntertwiningMap ρ σ)
    (K : Subgroup G) (f : G → ℂ) (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v : V) :
    φ (hkS ρ K f v) = hkS σ K f (φ v) := by
  rw [hkS_eq_sum ρ K f hf, hkS_eq_sum σ K f hf]
  show φ.toLinearMap _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul]
  congr 1
  exact φ.isIntertwining _ _ q.out v

theorem subEig : SubEig := by
  intro G _ _ _ V _ _ ρ hρ K X f e hfin u hu hu0 heig
  let S := cyc ρ u
  let u' : S.toSubmodule := ⟨u, mem_cyc ρ u⟩
  have hu' : u' ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  obtain ⟨T, huT, hmax⟩ := exists_max_avoid S.toRepresentation hu'
  have hst : ∀ g, T.toSubmodule ≤ T.toSubmodule.comap (S.toRepresentation g) :=
    fun g _ hv => T.apply_mem_toSubmodule g hv
  let τ := S.toRepresentation.quotient T.toSubmodule hst
  have hirr : τ.IsIrreducible := quot_irred S.toRepresentation T huT hmax (cyc_gen ρ u) hst
  have hsm : IsSmooth τ := smooth_quot (smooth_sub hρ S) _ hst
  let p := mkI S.toRepresentation T.toSubmodule hst
  let w : S.toSubmodule ⧸ T.toSubmodule := p u'
  have hw0 : w ≠ 0 := by
    show (Submodule.Quotient.mk u' : S.toSubmodule ⧸ T.toSubmodule) ≠ 0
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hsub : IsSubquotient τ ρ := by
    refine ⟨S, p, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨x, rfl⟩
  refine ⟨⟨_, τ, hsm, hirr⟩, hsub, w, ?_, hw0, fun x => ?_⟩
  · refine mem_fixed_iff.2 fun k hk => ?_
    have hh' : S.toRepresentation k u' = u' := Subtype.ext (mem_fixed_iff.1 hu k hk)
    have := p.isIntertwining _ _ k u'
    rw [hh'] at this
    exact this.symm
  · have h1 : hkS S.toRepresentation K (f x) u' = e x • u' := by
      apply Subtype.ext
      have := hkS_map (inclI S) K (f x) (hfin x) u'
      exact this.trans (heig x)
    have := hkS_map p K (f x) (hfin x) u'
    rw [h1, map_smul] at this
    exact this.symm

end GlobalTheory.CompanionTheory.SubEigIrr

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubEigenTailHeckeStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_eigen_tail_hecke : PositivityTheory.Rg.BcB.F.Tail.PExp.SubEig := by
  first | exact @GlobalTheory.CompanionTheory.SubEigIrr.subEig | exact GlobalTheory.CompanionTheory.SubEigIrr.subEig | (intros; apply GlobalTheory.CompanionTheory.SubEigIrr.subEig <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicInductionCentralCharacterProd
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.ZCentre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem scalar_apply {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) (i j : n) :
    ((Matrix.GeneralLinearGroup.scalar n t : GL n R) : Matrix n n R) i j = if i = j then (t : R) else 0 := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem det_scalar {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar n t : GL n R) = t ^ Fintype.card n := by
  ext; simp [Matrix.GeneralLinearGroup.scalar]

theorem scalar_comm {R : Type} [Field R] {n : Type} [Fintype n] [DecidableEq n] (t : Rˣ) (g : GL n R) :
    g * Matrix.GeneralLinearGroup.scalar n t = Matrix.GeneralLinearGroup.scalar n t * g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, mul_comm]

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem sum_card_mul_modExp : ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp [mul_comm]


variable (k) in
theorem deltaHalf_scalar (t : kˣ) :
    deltaHalf k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
  have h1 : modulus k m (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) = 1 := by
    have h2 : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (m a) t : GL (m a) k)) ^ modExp m a =
        nabs k t ^ ((Fintype.card (m a) : ℤ) * modExp m a) := fun a => by
      rw [det_scalar, zpow_mul, zpow_natCast]
      congr 1
      simp [nabs]
    simp only [modulus, h2]
    have h3 : ∀ (s : Finset α) (f : α → ℤ), ∏ a ∈ s, nabs k t ^ f a = nabs k t ^ ∑ a ∈ s, f a := fun s f => by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ (nabs_pos' k t).ne', ih]
    rw [h3, sum_card_mul_modExp, zpow_zero]
  refine Units.ext ?_
  rw [val_deltaHalf, h1]
  simp

theorem piTensor_scalar {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (w : PiTensorProduct ℂ X) :
    piTensor ρ g w = (∏ a, c a) • w := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, piTensor_tprod, smul_comm]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ _ _ _
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]

theorem scalar_mem_parab (e : (Σ a, m a) ≃ n) (t : kˣ) :
    Matrix.GeneralLinearGroup.scalar n t ∈ parab k e := by
  refine mem_parab.2 fun i j hij => ?_
  rw [scalar_apply, if_neg]
  rintro rfl
  exact lt_irrefl _ hij

theorem leviProj_scalar (e : (Σ a, m a) ≃ n) (t : kˣ) :
    leviProj k e ⟨_, scalar_mem_parab e t⟩ = fun a => Matrix.GeneralLinearGroup.scalar (m a) t := by
  funext a
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [leviProj_apply, scalar_apply, scalar_apply]
  simp

theorem parInd_scalar {W : Type} [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n)
    (ρ : Representation ℂ (Levi k m) W) (t : kˣ) (c : ℂ)
    (h : ∀ w, ρ (fun a => Matrix.GeneralLinearGroup.scalar (m a) t) w = c • w) (f : IndSp e ρ) :
    parInd e ρ (Matrix.GeneralLinearGroup.scalar n t) f = c • f := by
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  have h1 := parInd_law e ρ f ⟨_, scalar_mem_parab e t⟩ g
  rw [leviProj_scalar, deltaHalf_scalar, h] at h1
  rw [parInd_apply, scalar_comm]
  simpa using h1

theorem prodIrr_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (t : kˣ) (c : Fin h → ℂ),
    (∀ a, Zl.ScalarBy (x a) t (c a)) →
      ∀ v, prodIrr x hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = (∏ a, c a) • v := by
  intro k _ _ _ _ h N x hd t c hc v
  exact parInd_scalar _ _ t _ (fun w => piTensor_scalar _ _ c (fun a v => hc a v) w) v

end GlobalTheory.CompanionTheory.ZCentre

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceActionDeterminant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceActionDeterminant
noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise Kronecker

namespace GlobalTheory.CompanionTheory.ConeLin

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hOf_add (v w : Fin n × Fin n → ℝ) : hOf (v + w) = hOf v + hOf w := by
  simp only [hOf, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem hOf_smul (c : ℝ) (v : Fin n × Fin n → ℝ) : hOf (c • v) = (c : ℂ) • hOf v := by
  simp only [hOf, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

theorem hOf_single (q : Fin n × Fin n) : hOf (Pi.single q (1 : ℝ)) = hb q := by
  classical
  simp [hOf, Pi.single_apply, ite_smul]

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v)ᴴ = hOf v := by
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem re_trace (P : Mat n) (hP : Pᴴ = P) (p : Fin n × Fin n) :
    (((P * hb p).trace).re : ℂ) = (P * hb p).trace := by
  apply Complex.conj_eq_iff_re.1
  have h1 : star (P * hb p).trace = (P * hb p).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hP, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose,
      Matrix.trace_mul_comm]
  exact h1

theorem hOf_re (P : Mat n) (hP : Pᴴ = P) : hOf (fun p => ((P * hb p).trace).re) = P := by
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr P
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, re_trace P hP]

theorem conj_herm (g P : Mat n) (hP : Pᴴ = P) : (g * P * gᴴ)ᴴ = g * P * gᴴ := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

def realMap (g : Mat n) : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) where
  toFun v p := ((g * hOf v * gᴴ * hb p).trace).re
  map_add' v w := by
    funext p
    simp [hOf_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' c v := by
    funext p
    simp [hOf_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

def cplxMap (g : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := g * X * gᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxMap_apply (g X : Mat n) : cplxMap g X = g * X * gᴴ := rfl

theorem hOf_realMap (g : Mat n) (v : Fin n × Fin n → ℝ) : hOf (realMap g v) = g * hOf v * gᴴ :=
  hOf_re _ (conj_herm g _ (hOf_herm v))

theorem det_realMap (g : Mat n) : ((LinearMap.det (realMap g) : ℝ) : ℂ) = LinearMap.det (cplxMap g) := by
  rw [← LinearMap.det_toMatrix' (realMap g), ← GlobalTheory.CompanionTheory.TopClass.det_of_trace (cplxMap g),
    ← Matrix.det_transpose (Matrix.of _)]
  have h : ((LinearMap.toMatrix' (realMap g)).det : ℂ) =
      Complex.ofRealHom (LinearMap.toMatrix' (realMap g)).det := rfl
  rw [h, RingHom.map_det]
  congr 1
  ext p q
  have hh : (g * hb q * gᴴ)ᴴ = g * hb q * gᴴ := conj_herm g _ (GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose q)
  have := re_trace _ hh p
  simpa [LinearMap.toMatrix'_apply, realMap, hOf_single, cplxMap_apply, Pi.single_apply] using this

theorem det_cplxMap (g : Mat n) : LinearMap.det (cplxMap g) = (g.det * star g.det) ^ n := by
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) (Matrix.stdBasis ℂ (Fin n) (Fin n)) (cplxMap g) =
      g ⊗ₖ g.map star := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have hr : ∀ X : Mat n, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr X (i, j) = X i j := by
      intro X
      simp [Matrix.stdBasis]
    rw [LinearMap.toMatrix_apply, hr]
    simp [cplxMap_apply, Matrix.stdBasis_eq_single, Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)), h, Matrix.det_kronecker]
  have h2 : (g.map star).det = star g.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
    rfl
  rw [h2, Fintype.card_fin, mul_pow]

theorem cone_lin (n : ℕ) (g : Mat n) (_hg : g.det ≠ 0) :
    ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ),
      (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := by
  refine ⟨realMap g, hOf_realMap g, ?_⟩
  apply Complex.ofReal_injective
  rw [det_realMap, det_cplxMap]
  have : g.det * star g.det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.mul_conj' g.det
  rw [this, pow_mul]
  simp

end GlobalTheory.CompanionTheory.ConeLin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceActionDeterminantStatement
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_action_determinant : ∀ (n : ℕ) (g : Mat n), g.det ≠ 0 → ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ), (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLin.cone_lin | exact GlobalTheory.CompanionTheory.ConeLin.cone_lin | (intros; apply GlobalTheory.CompanionTheory.ConeLin.cone_lin <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorHecke
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorHecke
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TensHkSum

open PositivityTheory.Rg.BcB.F.Tail.PExp

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem extTensor_apply_eq (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (m : G × H) :
    extTensor ρ σ m = TensorProduct.map (ρ m.1) (σ m.2) := by
  rfl

theorem hkE_eq_sum (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ)
    (hs : {q : G ⧸ K | f q.out ≠ 0}.Finite) :
    hkE ρ K f = ∑ q ∈ hs.toFinset, f q.out • ρ q.out := by
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkE
  apply finsum_eq_sum_of_support_subset
  intro q hq
  rw [Function.mem_support] at hq
  rw [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
  intro h0
  exact hq (by simp [h0])

theorem map_sum_sum_apply {A B : Type} (s : Finset A) (t : Finset B) (a : A → ℂ) (b : B → ℂ)
    (P : A → Module.End ℂ V) (Q : B → Module.End ℂ W) (v : V ⊗[ℂ] W) :
    TensorProduct.map (∑ i ∈ s, a i • P i) (∑ j ∈ t, b j • Q j) v =
      ∑ p ∈ s ×ˢ t, (a p.1 * b p.2) • TensorProduct.map (P p.1) (Q p.2) v := by
  have hB : ∀ (P' : Module.End ℂ V) (Q' : Module.End ℂ W),
      TensorProduct.map P' Q' v = TensorProduct.mapBilinear (RingHom.id ℂ) V W V W P' Q' v := fun P' Q' => by
    rw [TensorProduct.mapBilinear_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hB, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_product,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem bijective_mk_out_prod (K : Subgroup G) (L : Subgroup H) :
    Function.Bijective (fun p : (G ⧸ K) × (H ⧸ L) =>
      (QuotientGroup.mk (p.1.out, p.2.out) : (G × H) ⧸ K.prod L)) := by
  constructor
  · rintro ⟨q1, r1⟩ ⟨q2, r2⟩ h
    simp only at h
    rw [QuotientGroup.eq, Subgroup.mem_prod] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] at h1 h2
    have e1 : (QuotientGroup.mk q1.out : G ⧸ K) = QuotientGroup.mk q2.out := QuotientGroup.eq.mpr h1
    have e2 : (QuotientGroup.mk r1.out : H ⧸ L) = QuotientGroup.mk r2.out := QuotientGroup.eq.mpr h2
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at e1 e2
    rw [e1, e2]
  · intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨((QuotientGroup.mk x.1 : G ⧸ K), (QuotientGroup.mk x.2 : H ⧸ L)), ?_⟩
    simp only
    rw [QuotientGroup.eq, Subgroup.mem_prod]
    simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
    exact ⟨QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x.1 : G ⧸ K)),
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x.2 : H ⧸ L))⟩

theorem apply_out_mk {X : Type} (K : Subgroup G) (Φ : G → X) (hΦ : ∀ x, ∀ k ∈ K, Φ (x * k) = Φ x) (x : G) :
    Φ (QuotientGroup.mk x : G ⧸ K).out = Φ x := by
  have hk : x⁻¹ * (QuotientGroup.mk x : G ⧸ K).out ∈ K :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk x : G ⧸ K)).symm
  have e := hΦ x _ hk
  rw [mul_inv_cancel_left] at e
  exact e

theorem tensHk : TensHk := by
  intro G H V W _ _ _ _ _ _ ρ σ K L f e hf he hsf hse v hv
  have hfix : ∀ k ∈ K.prod L, extTensor ρ σ k v = v := by
    intro k hk
    have h1 := hv ⟨k, hk⟩
    simpa using h1
  have hinv : ∀ x : G × H, ∀ k ∈ K.prod L,
      (f (x * k).1 * e (x * k).2) • extTensor ρ σ (x * k) v = (f x.1 * e x.2) • extTensor ρ σ x v := by
    intro x k hk
    have hk' := Subgroup.mem_prod.mp hk
    rw [Prod.fst_mul, Prod.snd_mul, hf _ _ hk'.1, he _ _ hk'.2, map_mul, Module.End.mul_apply, hfix k hk]
  have key : (∑ᶠ q : (G × H) ⧸ K.prod L, (f q.out.1 * e q.out.2) • extTensor ρ σ q.out v)
      = ∑ᶠ p : (G ⧸ K) × (H ⧸ L), (f p.1.out * e p.2.out) • TensorProduct.map (ρ p.1.out) (σ p.2.out) v := by
    rw [← finsum_comp_equiv (Equiv.ofBijective _ (bijective_mk_out_prod K L))]
    apply finsum_congr
    intro p
    rw [Equiv.ofBijective_apply]
    have h2 := apply_out_mk (K.prod L) (fun m : G × H => (f m.1 * e m.2) • extTensor ρ σ m v) hinv
      (p.1.out, p.2.out)
    simp only at h2
    rw [extTensor_apply_eq] at h2
    exact h2
  unfold PositivityTheory.Rg.BcB.F.Tail.PExp.hkS
  show (∑ᶠ q : (G × H) ⧸ K.prod L, (f q.out.1 * e q.out.2) • extTensor ρ σ q.out v) = _
  rw [key, hkE_eq_sum ρ K f hsf, hkE_eq_sum σ L e hse, map_sum_sum_apply]
  apply finsum_eq_sum_of_support_subset
  intro p hp
  rw [Function.mem_support] at hp
  rw [Finset.coe_product, Set.mem_prod, Set.Finite.coe_toFinset, Set.Finite.coe_toFinset,
    Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  constructor
  · intro h0
    exact hp (by simp [h0])
  · intro h0
    exact hp (by simp [h0])

end GlobalTheory.CompanionTheory.TensHkSum

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorHeckeStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_hecke : PositivityTheory.Rg.BcB.F.Tail.PExp.TensHk := by
  first | exact @GlobalTheory.CompanionTheory.TensHkSum.tensHk | exact GlobalTheory.CompanionTheory.TensHkSum.tensHk | (intros; apply GlobalTheory.CompanionTheory.TensHkSum.tensHk <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end
