module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTwistTotalWeightZeroProof
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroPotentiallySemistableOfSenTheorem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallySemistableReducibleUnramifiedSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyIrreducibleElementaryWeightModification

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixForm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentCyclotomicEigenvectorsWeights
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentCyclotomicEigenvectorsWeights
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem actC_apply_eq_σC {l : ℕ} [Fact l.Prime] (g : GQ l) (y : ℂ_[l]) :
    GlobalTheory.Cyc.Model.actC g y = Formalism.Per.σC g y := by
  change GlobalTheory.Cyc.Model.extHom g y = Formalism.Per.σC g y
  have hc : Continuous (Formalism.Per.σC g) :=
    (AddMonoidHomClass.isometry_of_norm (Formalism.Per.σC g) (GlobalTheory.RingBasics.norm_σC g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (GlobalTheory.Cyc.Model.extHom_cont g) hc
  | ih x => exact (GlobalTheory.Cyc.Model.extHom_coe g x).trans (GlobalTheory.RingBasics.σC_coe g x).symm

theorem linIndep_of_eigen_weights : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n ℂ_[l]) (ι : Type) [Fintype ι] (v : ι → n → ℂ_[l]) (w : ι → ℤ), (∀ (g : ↥(GK K)) j, (A g).mulVec (fun i => Formalism.Per.σC (g : GQ l) (v j i)) = algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) • v j) → (∀ (a : ℤ) (c : ι → Om l), (∀ j, c j ∈ K.1) → (∀ j, w j ≠ a → c j = 0) → ∑ j, (c j : ℂ_[l]) • v j = 0 → c = 0) → LinearIndependent ℂ_[l] v := by
  intro l _ P n _ _ K A ι _ v w hA hK
  classical

  set e : GQ l → ℤ → ℂ_[l] := fun g k => algebraMap ℚ_[l] ℂ_[l] ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) with he
  have e_ne : ∀ g k, e g k ≠ 0 := fun g k => by
    simp only [he, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[l] ℂ_[l]).injective, Units.ne_zero,
      not_false_eq_true]
  have e_sub : ∀ g (a b : ℤ), e g (a - b) * e g b = e g a := fun g a b => by
    simp only [he, ← map_mul, ← Units.val_mul, ← zpow_add, sub_add_cancel]
  have hcyc : GlobalTheory.Cyc.IsCyc P.χQ := P.χQ_cyc
  rw [Fintype.linearIndependent_iff]
  suffices key : ∀ m : ℕ, ∀ a : ι → ℂ_[l], (Finset.univ.filter (fun j => a j ≠ 0)).card = m →
      ∑ j, a j • v j = 0 → a = 0 by
    intro a ha j
    exact congrFun (key _ a rfl ha) j
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a hcard hrel
  by_contra hne
  obtain ⟨j0, hj0⟩ : ∃ j0, a j0 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  set b : ι → ℂ_[l] := fun j => (a j0)⁻¹ * a j with hb
  have hbrel : ∑ j, b j • v j = 0 := by
    simp only [hb, mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  have hb0 : b j0 = 1 := by simp only [hb, inv_mul_cancel₀ hj0]
  have hsupp : ∀ j, b j ≠ 0 ↔ a j ≠ 0 := fun j => by
    simp only [hb, ne_eq, mul_eq_zero, inv_eq_zero, hj0, false_or]

  have htw : ∀ g : ↥(GK K), ∀ j, Formalism.Per.σC (g : GQ l) (b j) * e g (w j) = e g (w j0) * b j := by
    intro g
    have h1 : (∑ j, Formalism.Per.σC (g : GQ l) (b j) • (fun i => Formalism.Per.σC (g : GQ l) (v j i))) = 0 := by
      funext i
      have hi := congrFun hbrel i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_zero (Formalism.Per.σC (g : GQ l)), ← hi, map_sum]
      simp only [map_mul]
    have h2 : ∑ j, (Formalism.Per.σC (g : GQ l) (b j) * e g (w j)) • v j = 0 := by
      have := congrArg (fun u => (A g).mulVec u) h1
      simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hA, Matrix.mulVec_zero, smul_smul] at this
      exact this
    set d : ι → ℂ_[l] := fun j => Formalism.Per.σC (g : GQ l) (b j) * e g (w j) - e g (w j0) * b j with hd
    have hdrel : ∑ j, d j • v j = 0 := by
      simp only [hd, sub_smul, Finset.sum_sub_distrib]
      rw [h2]
      simp only [mul_smul, ← Finset.smul_sum, hbrel, smul_zero, sub_zero]
    have hdsub : Finset.univ.filter (fun j => d j ≠ 0) ⊆ (Finset.univ.filter (fun j => a j ≠ 0)).erase j0 := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
      refine ⟨?_, ?_⟩
      · rintro rfl
        apply hj
        simp only [hd, hb0, map_one, one_mul, mul_one, sub_self]
      · rw [← hsupp]
        intro hbj
        apply hj
        simp only [hd, hbj, map_zero, zero_mul, mul_zero, sub_self]
    have hlt : (Finset.univ.filter (fun j => d j ≠ 0)).card < m := by
      rw [← hcard]
      refine lt_of_le_of_lt (Finset.card_le_card hdsub) (Finset.card_erase_lt_of_mem ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj0
    have hd0 := ih _ hlt d rfl hdrel
    intro j
    exact sub_eq_zero.1 (congrFun hd0 j)

  have hin : ∀ j, ∃ x : Om l, x ∈ K.1 ∧ (x : ℂ_[l]) = b j ∧ (w j ≠ w j0 → x = 0) := by
    intro j
    have hfix : ∀ g ∈ GK K, GlobalTheory.Cyc.chiC P.χQ (w j - w j0) g * GlobalTheory.Cyc.Model.actC g (b j) = b j := by
      intro g hg
      rw [actC_apply_eq_σC]
      have h := htw ⟨g, hg⟩ j
      change Formalism.Per.σC g (b j) * e g (w j) = e g (w j0) * b j at h
      change e g (w j - w j0) * Formalism.Per.σC g (b j) = b j
      apply mul_left_cancel₀ (e_ne g (w j0))
      rw [← h, ← e_sub g (w j) (w j0)]
      ring
    have hT := GlobalTheory.Cyc.tate_invariants_twist l GlobalTheory.Cyc.Model.actC P.χQ GlobalTheory.Cyc.Model.isActC_actC hcyc K
      (w j - w j0) (b j) hfix
    by_cases hw : w j = w j0
    · obtain ⟨x, hxK, hx⟩ := hT.2 (sub_eq_zero.2 hw)
      exact ⟨x, hxK, hx, fun h => absurd hw h⟩
    · have hbj : b j = 0 := hT.1 (sub_ne_zero.2 hw)
      exact ⟨0, K.1.zero_mem, by rw [hbj]; exact UniformSpace.Completion.coe_zero, fun _ => rfl⟩
  choose c hcK hcb hc0 using hin
  have hc : c = 0 := hK (w j0) c hcK hc0 (by simp only [hcb]; exact hbrel)
  have : b j0 = 0 := by rw [← hcb j0, hc, Pi.zero_apply]; exact UniformSpace.Completion.coe_zero
  rw [hb0] at this
  exact one_ne_zero this

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentCyclotomicEigenvectorsWeightsStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_cyclotomicEigenvectors_weights : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n ℂ_[l]) (ι : Type) [Fintype ι] (v : ι → n → ℂ_[l]) (w : ι → ℤ), (∀ (g : ↥(GK K)) j, (A g).mulVec (fun i => Formalism.Per.σC (g : GQ l) (v j i)) = algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) • v j) → (∀ (a : ℤ) (c : ι → Om l), (∀ j, c j ∈ K.1) → (∀ j, w j ≠ a → c j = 0) → ∑ j, (c j : ℂ_[l]) • v j = 0 → c = 0) → LinearIndependent ℂ_[l] v := by
  first | exact @GlobalTheory.PMon.linIndep_of_eigen_weights | exact GlobalTheory.PMon.linIndep_of_eigen_weights | (intros; apply GlobalTheory.PMon.linIndep_of_eigen_weights <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrix
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.FrameOne

theorem adapted_basis_fin {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]
    (A : ℤ → Submodule L (n → L)) (hA : Antitone A) (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0)
    (a0 : ℤ) (htop : A a0 = ⊤) :
    ∃ (d : n → n → L) (k : n → ℤ), LinearIndependent L d ∧
      ∀ a, A a = Submodule.span L (d '' {j | a ≤ k j}) := by
  obtain ⟨m, d, k, hli, hsp⟩ := GlobalTheory.filtration_adapted_basis A hA inferInstance hsep
  have hspan : ⊤ ≤ Submodule.span L (Set.range d) := by
    rw [← htop, hsp a0]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  let b := Module.Basis.mk hli hspan
  have hcard : Fintype.card n = Fintype.card (Fin m) := by
    have h1 := Module.finrank_eq_card_basis b
    rw [Module.finrank_fintype_fun_eq_card] at h1
    exact h1
  let e : n ≃ Fin m := Fintype.equivOfCardEq hcard
  refine ⟨d ∘ e, k ∘ e, hli.comp e e.injective, fun a => ?_⟩
  rw [hsp a]
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e.symm i, by simpa using hi, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨e j, hj, rfl⟩

end GlobalTheory.PMon.FrameOne

namespace GlobalTheory.PMon.FrameOne

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem fil_zero (a : ℤ) : (0 : P.R.BdR) ∈ Fil P a := ((P.PD (botExt l)).Fil a).zero_mem

theorem fil_add {a : ℤ} {x y : P.R.BdR} (hx : x ∈ Fil P a) (hy : y ∈ Fil P a) : x + y ∈ Fil P a :=
  ((P.PD (botExt l)).Fil a).add_mem hx hy

theorem fil_sum {ι : Type} (s : Finset ι) {a : ℤ} (f : ι → P.R.BdR) (h : ∀ i ∈ s, f i ∈ Fil P a) :
    ∑ i ∈ s, f i ∈ Fil P a :=
  Submodule.sum_mem ((P.PD (botExt l)).Fil a) h

theorem fil_anti {a b : ℤ} (hab : a ≤ b) {x : P.R.BdR} (hx : x ∈ Fil P b) : x ∈ Fil P a := by
  induction b, hab using Int.leInduction with
  | base => exact hx
  | succ c _ ih => exact ih ((P.PD (botExt l)).Fil_anti c hx)

theorem fil_exh (x : P.R.BdR) : ∃ a, x ∈ Fil P a := (P.PD (botExt l)).Fil_exh x

theorem fil_sep (x : P.R.BdR) (h : ∀ a, x ∈ Fil P a) : x = 0 := (P.PD (botExt l)).Fil_sep x h

end GlobalTheory.PMon.FrameOne

namespace GlobalTheory.PMon.FrameOne

open Matrix

theorem frame_of_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n P.R.BdR) (Q : GL n P.R.BdR), (∀ g i j, A g i j ∈ Fil P 0) → (∀ g : ↥(GK K), A g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K), A g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := by
  intro l _ P AI T n _ _ K A Q hA0 hAQ
  obtain ⟨S, θ, hS, -, hθ0, hθOm, hθg⟩ := GlobalTheory.T.exists_theta_deRhamFilZero_surjective l P AI T
  obtain ⟨hfield, -, htz, hinv, -, hmul, -, htzact, -, -, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  haveI : Nontrivial P.R.BdR := ⟨hfield.exists_pair_ne⟩
  set Q' : Matrix n n P.R.BdR := (Q : Matrix n n P.R.BdR) with hQ'
  let eK : ↥K.1 →+* P.R.BdR := (algebraMap (Om l) P.R.BdR).comp (K.1.val : ↥K.1 →+* Om l)
  have hE0 : ∀ c, eK c ∈ Fil P 0 := fun c => (hS _).1 (hθOm (c : Om l)).1
  have hEg : ∀ (g : ↥(GK K)) c, P.actQdR (g : GQ l) (eK c) = eK c := by
    intro g c
    show P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR (c : Om l)) = algebraMap (Om l) P.R.BdR (c : Om l)
    rw [P.actQdR_Om, (IntermediateField.mem_fixingSubgroup_iff _ _).mp g.2 _ c.2]
  have hEinj : ∀ c, eK c = 0 → c = 0 := by
    intro c hc
    have : (c : Om l) = 0 := (map_eq_zero_iff _ (algebraMap (Om l) P.R.BdR).injective).1 hc
    exact Subtype.ext this
  have hEadd : ∀ c d, eK (c + d) = eK c + eK d := fun c d => map_add eK c d
  have hEmul : ∀ c d, eK (c * d) = eK c * eK d := fun c d => map_mul eK c d
  have hE00 : eK 0 = 0 := map_zero eK
  have hEsum : ∀ (f : n → ↥K.1), eK (∑ j, f j) = ∑ j, eK (f j) := fun f => map_sum eK f _
  let vec : (n → ↥K.1) → n → P.R.BdR := fun c => Q' *ᵥ fun j => eK (c j)
  let Af : ℤ → Submodule ↥K.1 (n → ↥K.1) := fun a =>
    { carrier := {c | ∀ i, vec c i ∈ Fil P a}
      add_mem' := by
        intro c d hc hd i
        have : vec (c + d) = vec c + vec d := by
          simp only [vec, Pi.add_apply, hEadd, ← Matrix.mulVec_add]; rfl
        rw [this]; exact fil_add P (hc i) (hd i)
      zero_mem' := by
        intro i
        have : vec 0 = 0 := by
          simp only [vec, Pi.zero_apply, hE00]; exact Matrix.mulVec_zero _
        rw [this]; exact fil_zero P a
      smul_mem' := by
        intro k c hc i
        have : vec (k • c) = eK k • vec c := by
          simp only [vec, Pi.smul_apply, smul_eq_mul, hEmul, ← Matrix.mulVec_smul]; rfl
        rw [this]
        simpa using hmul 0 a _ _ (hE0 k) (hc i) }

  have hAnti : Antitone Af := by
    intro a b hab c hc i
    exact fil_anti P hab (hc i)
  have hSep : ∀ c, (∀ a, c ∈ Af a) → c = 0 := by
    intro c hc
    have hv : vec c = 0 := funext fun i => fil_sep P _ fun a => hc a i
    have h2 : (fun j => eK (c j)) = 0 := by
      have h3 : ((Q⁻¹ : GL n P.R.BdR) : Matrix n n P.R.BdR) *ᵥ vec c = fun j => eK (c j) := by
        simp only [vec, Matrix.mulVec_mulVec, hQ']
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← h3, hv, Matrix.mulVec_zero]
    funext j
    exact hEinj _ (congrFun h2 j)
  choose f hf using fun p : n × n => fil_exh P (Q' p.1 p.2)
  let a0 : ℤ := -∑ p : n × n, |f p|
  have ha0 : ∀ p, a0 ≤ f p := by
    intro p
    have h1 : |f p| ≤ ∑ q : n × n, |f q| :=
      Finset.single_le_sum (f := fun q => |f q|) (fun q _ => abs_nonneg _) (Finset.mem_univ p)
    have h2 := neg_abs_le (f p)
    simp only [a0]; linarith
  have hTop : Af a0 = ⊤ := by
    rw [eq_top_iff]
    intro c _ i
    refine fil_sum P _ _ fun j _ => ?_
    have := hmul (f (i, j)) 0 _ _ (hf (i, j)) (hE0 (c j))
    rw [add_zero] at this
    exact fil_anti P (ha0 (i, j)) this
  obtain ⟨d, k, hli, hsp⟩ := adapted_basis_fin Af hAnti hSep a0 hTop
  have hdk : ∀ j i, vec (d j) i ∈ Fil P (k j) := by
    intro j
    have : d j ∈ Af (k j) := by
      rw [hsp]; exact Submodule.subset_span ⟨j, show k j ≤ k j from le_refl _, rfl⟩
    exact this
  let U0 : Matrix n n P.R.BdR := Matrix.of fun i j => tz P (-(k j)) * vec (d j) i
  have hU0 : ∀ i j, U0 i j ∈ Fil P 0 := by
    intro i j
    have := (htz (k j) (-(k j)) _).1 (hdk j i)
    rwa [add_neg_cancel] at this

  have hvg : ∀ (g : ↥(GK K)) j, (A g) *ᵥ (fun m => P.actQdR (g : GQ l) (vec (d j) m)) = vec (d j) := by
    intro g j
    have : (fun m => P.actQdR (g : GQ l) (vec (d j) m)) = (Q'.map (P.actQdR (g : GQ l))) *ᵥ (fun p => eK (d j p)) := by
      funext m
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [vec, Matrix.mulVec, dotProduct, map_sum, map_mul, hEg, Matrix.map_apply]
    rw [this, Matrix.mulVec_mulVec, hAQ]
  have hEig : ∀ g : ↥(GK K), A g * U0.map (P.actQdR (g : GQ l)) = U0 * Matrix.diagonal fun j =>
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-(k j)) : ℚ_[l]ˣ) : ℚ_[l]) := by
    intro g
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    have key : ∀ X : P.R.BdR, (∑ m, A g i m * (X * P.actQdR (g : GQ l) (vec (d j) m))) = X * vec (d j) i := by
      intro X
      rw [← congrFun (hvg g j) i, Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [U0, Matrix.map_apply, Matrix.of_apply, map_mul, htzact]
    rw [key]; ring

  have hq : ∀ q : ℚ_[l], ∃ h : algebraMap ℚ_[l] P.R.BdR q ∈ S, θ ⟨_, h⟩ = algebraMap ℚ_[l] ℂ_[l] q := by
    intro q
    obtain ⟨h, hh⟩ := hθOm (algebraMap ℚ_[l] (Om l) q)
    have e : algebraMap ℚ_[l] P.R.BdR q = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) q) :=
      IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR q
    refine ⟨e ▸ h, ?_⟩
    have e2 : (⟨algebraMap ℚ_[l] P.R.BdR q, e ▸ h⟩ : ↥S) = ⟨_, h⟩ := Subtype.ext e
    rw [e2, hh]
    show algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℚ_[l] (PadicAlgCl l) q) = _
    exact (IsScalarTower.algebraMap_apply ℚ_[l] (PadicAlgCl l) ℂ_[l] q).symm
  let U0S : Matrix n n ↥S := Matrix.of fun i j => ⟨U0 i j, (hS _).2 (hU0 i j)⟩
  let M : Matrix n n ℂ_[l] := U0S.map θ
  have hgS : ∀ (g : GQ l) i j, P.actQdR g (U0 i j) ∈ S := fun g i j => (hθg g (U0S i j)).1
  let Aθ : ↥(GK K) → Matrix n n ℂ_[l] := fun g =>
    (Matrix.of fun i j => (⟨A g i j, (hS _).2 (hA0 g i j)⟩ : ↥S)).map θ
  have hc1 : ∀ (g : ↥(GK K)) (j : n), (Aθ g) *ᵥ (fun i => Formalism.Per.σC (g : GQ l) (M i j)) =
      algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) ^ (-(k j)) : ℚ_[l]ˣ) : ℚ_[l]) • (fun i => M i j) := by
    intro g j
    funext i
    obtain ⟨hc, hcθ⟩ := hq ((P.χQ (g : GQ l) ^ (-(k j)) : ℚ_[l]ˣ) : ℚ_[l])
    have hE := congrFun (congrFun (hEig g) i) j
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at hE
    have hsum : (∑ m, (⟨A g i m, (hS _).2 (hA0 g i m)⟩ : ↥S) * ⟨P.actQdR (g : GQ l) (U0 m j), hgS g m j⟩) =
        U0S i j * ⟨_, hc⟩ := by
      apply Subtype.ext
      simpa [U0S] using hE
    have h3 := congrArg θ hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul, hcθ] at h3
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Aθ, M, Matrix.map_apply, Matrix.of_apply]
    rw [mul_comm, ← h3]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul]
    congr 1
    exact ((hθg _ (U0S m j)).2).symm
  have hvecx : ∀ (c' : n → ↥K.1) i, vec (∑ j, c' j • d j) i = ∑ j, eK (c' j) * vec (d j) i := by
    intro c' i
    simp only [vec, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hEsum, hEmul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hc2 : ∀ (a : ℤ) (c : n → Om l), (∀ j, c j ∈ K.1) → (∀ j, -(k j) ≠ a → c j = 0) →
      ∑ j, (c j : ℂ_[l]) • (fun i => M i j) = 0 → c = 0 := by
    intro a c hcK hcw hsum
    let c' : n → ↥K.1 := fun j => ⟨c j, hcK j⟩
    have hc'0 : ∀ j, -(k j) ≠ a → c' j = 0 := fun j hj => Subtype.ext (hcw j hj)
    have hmemc : ∀ j, eK (c' j) ∈ S := fun j => (hθOm (c j)).1
    have hθc : ∀ j, θ ⟨eK (c' j), hmemc j⟩ = (c j : ℂ_[l]) := fun j => (hθOm (c j)).2
    have hx1 : ∀ i, tz P a * vec (∑ j, c' j • d j) i ∈ Fil P 1 := by
      intro i
      have hi := congrFun hsum i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
      have h0 : θ (∑ j, (⟨eK (c' j), hmemc j⟩ : ↥S) * U0S i j) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_mul, hθc]
        simpa [M] using hi
      have h1 := (hθ0 _).1 h0
      have h2 : ((∑ j, (⟨eK (c' j), hmemc j⟩ : ↥S) * U0S i j : ↥S) : P.R.BdR) =
          tz P a * vec (∑ j, c' j • d j) i := by
        rw [hvecx, Finset.mul_sum]
        simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, U0S, U0, Matrix.of_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : -(k j) = a
        · rw [hj]; ring
        · rw [hc'0 j hj, hE00]; ring
      rw [← h2]; exact h1
    have hxA : (∑ j, c' j • d j) ∈ Af (1 - a) := by
      intro i
      have := (htz (1 - a) a (vec (∑ j, c' j • d j) i)).2 (by rw [sub_add_cancel]; exact hx1 i)
      exact this
    have hxB : (∑ j, c' j • d j) ∈ Submodule.span ↥K.1 (d '' {j | k j = -a}) := by
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : -(k j) = a
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, show k j = -a by omega, rfl⟩)
      · rw [hc'0 j hj, zero_smul]; exact Submodule.zero_mem _
    have hdisj := hli.disjoint_span_image (s := {j | 1 - a ≤ k j}) (t := {j | k j = -a})
      (Set.disjoint_left.2 fun j h1 h2 => by simp only [Set.mem_setOf_eq] at h1 h2; omega)
    rw [hsp] at hxA
    have hx0 : (∑ j, c' j • d j) = 0 := (Submodule.disjoint_def.1 hdisj) _ hxA hxB
    have := Fintype.linearIndependent_iff.1 hli c' hx0
    funext j
    exact congrArg Subtype.val (this j)
  have hliC : LinearIndependent ℂ_[l] (fun j i => M i j) :=
    GlobalTheory.T.linearIndependent_cyclotomicEigenvectors_weights l P n K Aθ n (fun j i => M i j) (fun j => -(k j)) hc1 hc2
  have hunit : IsUnit M := Matrix.linearIndependent_cols_iff_isUnit.1 hliC
  have hdet : θ U0S.det ≠ 0 := by
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
  have hdetU : U0.det = (U0S.det : P.R.BdR) := by
    have := RingHom.map_det S.subtype U0S
    rw [show S.subtype.mapMatrix U0S = U0 from by ext; rfl] at this
    exact this.symm
  have hnot1 : U0.det ∉ Fil P 1 := fun h => hdet ((hθ0 _).2 (hdetU ▸ h))
  have hdet0 : U0.det ∈ Fil P 0 := hdetU ▸ (hS _).1 (U0S.det).2
  obtain ⟨y, hy0, hy⟩ := hinv _ hdet0 hnot1
  have hadj : ∀ i j, U0.adjugate i j ∈ Fil P 0 := by
    have e : U0.adjugate = S.subtype.mapMatrix U0S.adjugate := by
      rw [RingHom.map_adjugate, show S.subtype.mapMatrix U0S = U0 from by ext; rfl]
    intro i j
    rw [e]
    exact (hS _).1 (U0S.adjugate i j).2
  let U : GL n P.R.BdR := ⟨U0, y • U0.adjugate,
    by rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm y, hy, one_smul],
    by rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm y, hy, one_smul]⟩
  refine ⟨U, fun j => -(k j), ⟨hU0, fun i j => ?_⟩, hEig⟩
  show (y • U0.adjugate) i j ∈ Fil P 0
  rw [Matrix.smul_apply, smul_eq_mul]
  simpa using hmul 0 0 _ _ hy0 (hadj i j)

end GlobalTheory.PMon.FrameOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n P.R.BdR) (Q : GL n P.R.BdR), (∀ g i j, A g i j ∈ Fil P 0) → (∀ g : ↥(GK K), A g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K), A g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := by
  first | exact @GlobalTheory.PMon.FrameOne.frame_of_period_matrix | exact GlobalTheory.PMon.FrameOne.frame_of_period_matrix | (intros; apply GlobalTheory.PMon.FrameOne.frame_of_period_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentation
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_algebraicClosure_mem_deRhamFil_zero (P : LocPrime l) (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ Fil P 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩,
    IntermediateField.mem_adjoin_simple_self _ _⟩
  have h2 := ((P.PD K).Fil 0).smul_mem (⟨x, hK⟩ : ↥K.1) (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h2
  show algebraMap (Om l) P.R.BdR x ∈ ((P.PD (botExt l)).Fil 0 : Set P.R.BdR)
  rw [P.PD_Fil (botExt l) K 0]
  exact h2

theorem fr_zero (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  show (frobUr l ^ 0) c = c
  rw [pow_zero]
  rfl

theorem fr_add (a b : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l (a + b) c = fr l a (fr l b c) := by
  show (frobUr l ^ (a + b)) c = (frobUr l ^ a) ((frobUr l ^ b) c)
  rw [pow_add]
  rfl

theorem fr_mul_self {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (q : ℕ) : fr l (r * q) c = c := by
  induction q with
  | zero => simpa using fr_zero c
  | succ q ih => rw [Nat.mul_succ, fr_add, hc, ih]

theorem fr_mod {r : ℕ} {c : ↥(MaximalUnramifiedExtension l)} (hc : fr l r c = c) (m : ℕ) : fr l m c = fr l (m % r) c := by
  conv_lhs => rw [← Nat.mod_add_div m r]
  rw [fr_add, fr_mul_self hc]

variable (P : LocPrime l) {K : FinExt l} {n : Type} [Fintype n] [DecidableEq n]

theorem matD_mod {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (h : IsRat r ρ) (m : ℕ) (g : ↥(GK K)) :
    matD P ρ m g = matD P ρ (m % r) g := by
  ext i j
  simp only [matD, Matrix.map_apply]
  rw [fr_mod (h.rat g i j) m]

theorem matD_mem (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (g : ↥(GK K)) (i j : n) :
    matD P ρ m g i j ∈ Fil P 0 := by
  simp only [matD, Matrix.map_apply, kd, RingHom.comp_apply]
  exact algebraMap_algebraicClosure_mem_deRhamFil_zero P _

end GlobalTheory.PMon.FrameEquiv

namespace GlobalTheory.PMon.FrameEquiv

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

theorem tz_facts {AI : LocAinf l P} (T : LocTied l P AI) :
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, hact, hadd, h0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P _ T
  exact ⟨hact, hadd, h0⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tDiag (h : ∀ a : ℤ, tz P a * tz P (-a) = 1) (a : n → ℤ) : GL n P.R.BdR where
  val := Matrix.diagonal fun j => tz P (a j)
  inv := Matrix.diagonal fun j => tz P (-a j)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    have : ∀ j, tz P (-a j) * tz P (a j) = 1 := fun j => by simpa using h (-a j)
    simp [this]

theorem frameEx : FrameEx := by
  intro l _ P AI T n _ _ K r ρ hρ
  constructor
  · intro hD
    have H : ∀ m : Fin r, ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K),
        matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
          (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
            algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := fun m => by
      obtain ⟨Q, hQ⟩ := hD m
      exact GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix l P AI T n K (matD P ρ m) Q (matD_mem P ρ m) hQ
    choose U w hU using H
    exact ⟨w, fun m => ⟨U m, (hU m).1, (hU m).2⟩⟩
  · rintro ⟨w, hw⟩ m
    obtain ⟨hact, hadd, h0⟩ := tz_facts P T
    have hinv : ∀ a : ℤ, tz P a * tz P (-a) = 1 := fun a => by rw [← hadd, add_neg_cancel, h0]
    let k : Fin r := ⟨m % r, Nat.mod_lt _ hρ.pos⟩
    obtain ⟨U, -, hU⟩ := hw k
    refine ⟨U * tDiag P hinv (fun j => -w k j), fun g => ?_⟩
    have hmap : ∀ (X Y : Matrix n n P.R.BdR), (X * Y).map (P.actQdR (g : GQ l)) =
        X.map (P.actQdR (g : GQ l)) * Y.map (P.actQdR (g : GQ l)) := fun X Y =>
      Matrix.map_mul (f := ((P.actQdR (g : GQ l) : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →+* P.R.BdR))
    have hm : matD P ρ m g = matD P ρ (k : ℕ) g := matD_mod P hρ m g
    rw [Units.val_mul, hmap, ← mul_assoc, hm, hU g, mul_assoc]
    congr 1
    show Matrix.diagonal _ * (Matrix.diagonal fun j => tz P (-w k j)).map (P.actQdR (g : GQ l)) =
      Matrix.diagonal fun j => tz P (-w k j)
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rw [hact, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, map_one, one_mul]

end GlobalTheory.PMon.FrameEquiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamIffFramedGaloisRepresentationStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_iff_framed_galois_representation : FrameEx := by
  first | exact @GlobalTheory.PMon.FrameEquiv.frameEx | exact GlobalTheory.PMon.FrameEquiv.frameEx | (intros; apply GlobalTheory.PMon.FrameEquiv.frameEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCases
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCases
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.PMon.arith {α : Type} [Fintype α] [DecidableEq α] (f : α → ℤ) (h0 : ∑ z, f z = 0) (hf : f ≠ 0) :
    ∃ x y, x ≠ y ∧ ∑ z, (f z + eps x y z) = 0 ∧ ∑ z, (f z + eps x y z) ^ 2 < ∑ z, f z ^ 2 := by
  have hx : ∃ x, 0 < f x := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonpos fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  have hy : ∃ y, f y < 0 := by
    by_contra hc
    push Not at hc
    exact hf (funext fun z => (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hc z).1 h0 z (Finset.mem_univ _))
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have hxy : x ≠ y := fun e => by rw [e] at hx; omega
  have e1 : ∀ (g : α → ℤ), ∑ z, g z * eps x y z = g y - g x := by
    intro g
    have : ∀ z, g z * eps x y z = (if z = y then g y else 0) - (if z = x then g x else 0) := by
      intro z
      unfold eps
      by_cases a : z = x
      · subst a; simp [hxy]
      · by_cases b : z = y
        · subst b; simp [a]
        · simp [a, b]
    simp [this, Finset.sum_sub_distrib]
  have ex : eps x y x = -1 := by simp [eps]
  have ey : eps x y y = 1 := by simp [eps, hxy.symm]
  refine ⟨x, y, hxy, ?_, ?_⟩
  · have := e1 fun _ => 1
    simp only [one_mul] at this
    rw [Finset.sum_add_distrib, h0, this]; simp
  · have a := e1 f
    have b := e1 (eps x y)
    have : ∑ z, (f z + eps x y z) ^ 2 = ∑ z, f z ^ 2 + 2 * ∑ z, f z * eps x y z + ∑ z, eps x y z * eps x y z := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this, a, b, ex, ey]
    omega

theorem GlobalTheory.PMon.matThm_of_steps : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  intro hF hT hS hR hM l _ P AI T
  suffices H : ∀ (N : ℕ) (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = N →
      ∀ (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → AdmDR P ρ → AdmSt P ρ from
    fun n _ _ K r ρ => H _ n rfl K r ρ
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro n _ _ hn K r ρ hρ hd
  obtain ⟨w, hw⟩ := (hF l P AI T n K r ρ hρ).1 hd
  obtain ⟨K', r', ρ', w', h1, h2, h3, h4⟩ := hT l P AI T n K r ρ w hρ hw
  apply h4
  suffices G : ∀ (S : ℕ) (σ : ↥(GK K') →* GL n ↥(MaximalUnramifiedExtension l)) (v : Fin r' → n → ℤ), IsRat r' σ → Framed P σ v →
      ∑ z : Fin r' × n, v z.1 z.2 = 0 → (∑ z : Fin r' × n, v z.1 z.2 ^ 2).toNat = S → AdmSt P σ from
    G _ ρ' w' h1 h2 (by rw [Fintype.sum_prod_type]; exact h3) rfl
  intro S
  induction S using Nat.strong_induction_on with
  | _ S IS =>
  intro σ v a1 a2 a3 a4
  by_cases hv : (fun z : Fin r' × n => v z.1 z.2) = 0
  · have : v = 0 := funext fun m => funext fun j => congrFun hv (m, j)
    subst this
    exact hS l P AI T n K' r' σ a1 a2
  by_cases hs : Splits r' σ
  · exact hR l P AI T n K' r' σ a1 ((hF l P AI T n K' r' σ a1).2 ⟨v, a2⟩) hs
      fun a _ _ ha τ b1 b2 => IH _ (hn ▸ ha) a rfl K' r' τ b1 b2
  obtain ⟨x, y, hxy, c1, c2⟩ := GlobalTheory.PMon.arith _ a3 hv
  obtain ⟨τ, b1, b2, b3⟩ := hM l P AI T n K' r' σ v x y hxy a1 a2 hs
  refine b3 (IS _ ?_ τ _ b1 b2 c1 rfl)
  have p : 0 ≤ ∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2 := Finset.sum_nonneg fun z _ => sq_nonneg _
  show (∑ z : Fin r' × n, (v z.1 z.2 + eps x y z) ^ 2).toNat < S
  omega
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicMonodromyMatrixFormOfInductionCasesStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases : FrameEx → TwistStep → SenStep → RedStep → ModStep → MatThm := by
  first | exact @GlobalTheory.PMon.matThm_of_steps | exact GlobalTheory.PMon.matThm_of_steps | (intros; apply GlobalTheory.PMon.matThm_of_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixForm
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem matThm_holds : MatThm :=
  GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases GlobalTheory.T.deRham_iff_framed_galois_representation GlobalTheory.T.lubinTateTwistTotalWeightZero_proof GlobalTheory.T.weightZero_potentiallySemistable_of_sen_theorem GlobalTheory.T.potentially_semistable_reducible_unramified_split GlobalTheory.T.monodromy_irreducible_elementary_weightModification

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicMonodromyTheorem_matrixForm : MatThm := by
  first | exact @GlobalTheory.PMon.matThm_holds | exact GlobalTheory.PMon.matThm_holds | (intros; apply GlobalTheory.PMon.matThm_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromy
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromy
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.FromMat

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
  {n : Type} [Fintype n] [DecidableEq n]

def matRep (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l) :=
  MonoidHom.toHomUnits
    ((((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)).mapMatrix : Matrix n n ℚ_[l] →+* Matrix n n ↥(MaximalUnramifiedExtension l)) :
        Matrix n n ℚ_[l] →* Matrix n n ↥(MaximalUnramifiedExtension l)).comp
      (((LinearMap.toMatrixAlgEquiv b : (V →ₗ[ℚ_[l]] V) ≃ₐ[ℚ_[l]] Matrix n n ℚ_[l]) :
        (V →ₗ[ℚ_[l]] V) →* Matrix n n ℚ_[l]).comp ρ))

theorem matRep_apply (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (i j : n) :
    (matRep b ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j = algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (b.repr (ρ g (b j)) i) := by
  simp [matRep, LinearMap.toMatrixAlgEquiv_apply]

theorem toMatrix_map_apply (b : Module.Basis n ℚ_[l] V) (f : V →ₗ[ℚ_[l]] V) {A : Type} [Semiring A] [Algebra ℚ_[l] A]
    (i j : n) : (LinearMap.toMatrix b b f).map (algebraMap ℚ_[l] A) i j = algebraMap ℚ_[l] A (b.repr (f (b j)) i) := by
  simp [LinearMap.toMatrix_apply]

end GlobalTheory.PMon.FromMat

namespace GlobalTheory.PMon.FromMat

open GlobalTheory.PMon.Inhab

theorem deRhamPotSemistable_of_matThm : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  intro hM l _ P AI hT K V _ _ _ _ _ ρ hc hDR
  obtain ⟨T⟩ := hT
  let b := Module.finBasis ℚ_[l] V
  have hR : IsRat 1 (matRep b ρ) := by
    refine ⟨one_pos, fun c hc' => ?_, fun g i j => ?_, fun i j => ?_⟩
    · obtain ⟨q, rfl⟩ := fixed_frob P c (by rwa [fr_one] at hc')
      exact K.1.algebraMap_mem q
    · rw [matRep_apply, fr_q]
    · simp only [matRep_apply]
      have h1 : Continuous fun g : ↥(GK K) => b.coord i (ρ g (b j)) :=
        (IsModuleTopology.continuous_of_linearMap (R := ℚ_[l]) (b.coord i)).comp (hc (b j))
      exact (continuous_algebraMap ℚ_[l] (Om l)).comp h1
  have hD : AdmDR P (matRep b ρ) := by
    intro m
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_invertible_deRhamPeriodMatrix_of_isDR l P AI T _ K V b ρ hDR
    refine ⟨Q, fun g => ?_⟩
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    rw [matD, Matrix.map_apply, matRep_apply, fr_q, kd_alg, toMatrix_map_apply]
  obtain ⟨K', hK, Q, hQ⟩ := hM l P AI T _ K 1 (matRep b ρ) hR hD
  have hS : IsSst P (resTo ρ hK) := by
    refine GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing l P AI T _ K' V b (resTo ρ hK) Q fun g => ?_
    convert hQ g using 2
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    rw [matRep_apply, LinearMap.toMatrix_apply, ks, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
      Polynomial.algebraMap_apply]
    rfl
  exact GlobalTheory.T.isPotentiallySemistable_of_semistable_restrict l P AI T K K' hK V ρ hS

end GlobalTheory.PMon.FromMat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotSemistableOfMatrixMonodromyStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_potSemistable_of_matrix_monodromy : MatThm → GlobalTheory.Published.DeRhamPotSemistable := by
  first | exact @GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | exact GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm | (intros; apply GlobalTheory.PMon.FromMat.deRhamPotSemistable_of_matThm <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory

theorem deRham_potentiallySemistable : GlobalTheory.Published.DeRhamPotSemistable :=
  GlobalTheory.T.deRham_potSemistable_of_matrix_monodromy GlobalTheory.T.pAdicMonodromyTheorem_matrixForm

end GlobalTheory
