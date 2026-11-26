module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPKerRepsPowFourMulStatement
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVector
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NatAtStd

theorem isSD_pi (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    IsSDLat E N (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → E, x ∈ (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) ↔
      ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈
      (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

theorem detId_std (D : D7) (N : ℕ) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) = 1 := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    have h : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = A i j := fun i j => by
      have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k _ => by
        by_cases e : k = j
        · subst e
          rw [Pi.single_eq_same]
          exact Submodule.one_le.1 le_rfl
        · rw [Pi.single_eq_of_ne e]
          exact Submodule.zero_mem _
      have h2 := Submodule.mem_one.1 (hA _ h1 i trivial)
      simpa using h2
    choose b hb using h
    have e : A = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix (Matrix.of b) :=
      Matrix.ext fun i j => (hb i j).symm
    rw [e, ← RingHom.map_det]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · exact Submodule.one_le.2 (Submodule.subset_span ⟨1, fun v hv => by simpa using hv, Matrix.det_one.symm⟩)

theorem chi_one (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) : χ 1 = 1 := by
  letI := D.host.cmStar
  have h1 := h.2 1
  rw [Submodule.one_eq_span]
  simpa using h1

theorem chiFac_std (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) (a b : ℕ) :
    Base.chiFac χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = 1 := by
  simp [Base.chiFac, detId_std, chi_one D χ h]

variable (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ}

theorem Iop_self (A : AddSubgroup (TaylorLogMetric.VC D N N')) :
    ∃ x ∈ A, ∀ G : TaylorLogMetric.VC D N N' → ℂ, TaylorLogMetric.Iop D T A A G = fun z => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G z := by
  have htop : A.addSubgroupOf A = ⊤ := AddSubgroup.addSubgroupOf_self A
  haveI hsub : Subsingleton (A ⧸ A.addSubgroupOf A) := by
    rw [htop]; exact QuotientAddGroup.subsingleton_quotient_top
  let q0 : A ⧸ A.addSubgroupOf A := QuotientAddGroup.mk 0
  refine ⟨((Quotient.out q0 : A) : TaylorLogMetric.VC D N N'), Subtype.property _, fun G => ?_⟩
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by rw [htop]; exact AddSubgroup.index_top
  unfold TaylorLogMetric.Iop
  rw [finsum_eq_single _ q0 (fun q hq => absurd (Subsingleton.elim q q0) hq), hi]
  simp

theorem Hf_neg_right (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T z (-x) = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_neg_left (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (-z) x = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_add_left (z w x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (z + w) x = TaylorLogMetric.Hf D T z x + TaylorLogMetric.Hf D T w x := by
  simp [TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, add_div]

theorem al_neg_mul (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x = 1 := by
  unfold TaylorLogMetric.al
  rw [Hf_neg_left, Hf_neg_right, neg_neg, ← mul_zpow]
  simp

theorem inv_op (x : TaylorLogMetric.VC D N N') (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D T (-x) * TaylorLogMetric.U D T (-x) (fun w => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G w) z = G z := by
  have h := al_neg_mul D T x
  unfold TaylorLogMetric.U
  simp only [Hf_add_left, Hf_neg_left, Hf_neg_right, neg_add_cancel_right]
  have he : Complex.exp (-(Real.pi : ℂ) * (TaylorLogMetric.Hf D T z x + -TaylorLogMetric.Hf D T x x) - (Real.pi : ℂ) * TaylorLogMetric.Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * -TaylorLogMetric.Hf D T z x - (Real.pi : ℂ) * - -TaylorLogMetric.Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination (G z) * he * (TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x) + G z * h

theorem eNat_std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → B.VecP χ → ∀ a b : ℕ, Even a → Even b → TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∧ B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = B.thZero a b := by
  intro D cc dl B χ hχ hV a b ha hb
  have hA : TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) := by
    letI := D.host.cmStar
    exact ⟨ha, hb, isSD_pi _ a, isSD_pi _ b⟩
  refine ⟨hA, ?_⟩
  obtain ⟨x, hx, hI⟩ := Iop_self D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b))
  have hTh : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) :=
    (hV a b _ _ hA).1
  have hfix := hTh.2 (-x) (neg_mem hx)
  have he : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = fun z => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x
      (fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w) z := by
    funext z
    unfold Base.eNat Base.thMoved Base.thHalf
    rw [chiFac_std D χ hχ, one_mul, hI, hI]
  have h1 : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) =
      fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w := by
    funext z
    rw [← hfix z]
    conv_lhs => rw [he]
    exact inv_op D B.tor x _ z
  funext z
  rw [← hfix z]
  conv_lhs => rw [h1]
  exact inv_op D B.tor x _ z

end GlobalTheory.NatAtStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGap
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

namespace GlobalTheory.ColumnNormCompare

theorem numRec_eq_ofRecord : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) →
    GlobalTheory.ColumnNormCompare.numDatumOfParameters D L = ofRecord D L Del h0 := by
  intro D L Del h0 hD hE
  have hm : (D.R.m : ℝ) ≠ 0 := by
    have := D.R.two_le_m
    exact_mod_cast (show D.R.m ≠ 0 by omega)
  have h1 : ⌊D.s.Del⌋₊ = Del := by rw [hD]; exact Nat.floor_natCast Del
  have h2 : ⌈LevelStarExponents.h0 L⌉₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [hE]; field_simp
    rw [this]; exact Nat.ceil_natCast h0
  simp only [numDatumOfParameters, ofRecord, h1, h2]

end GlobalTheory.ColumnNormCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnNormParameters_eq_natStepGap : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) → GlobalTheory.ColumnNormCompare.numDatumOfParameters D L = ofRecord D L Del h0 := by
  first | exact @GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord | exact GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord | (intros; apply GlobalTheory.ColumnNormCompare.numRec_eq_ofRecord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ErrorUnitExponentialEstimate
noncomputable section

namespace GlobalTheory.ColNorms.NumMean

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms

theorem log_le_of_le_exp {y X : ℝ} (hy : 0 ≤ y) (hX : 0 ≤ X) (h : y ≤ Real.exp X) : Real.log y ≤ X := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; exact hX
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem log_mul_le {h h' : ℕ} {X : ℝ} (hX : 0 ≤ X) (h1 : (h : ℝ) ≤ Real.exp X) (h2 : (h' : ℝ) ≤ Real.exp X) :
    Real.log ((h : ℝ) * h') ≤ 2 * X := by
  refine log_le_of_le_exp (by positivity) (by linarith) ?_
  rw [two_mul, Real.exp_add]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem one_le_rd (N : NumDatum) : 1 ≤ N.rd := by
  have h : (4 * N.R.ord : ℝ) ≤ N.rd ^ 2 := N.H.der.rd_sq_ge
  have h0 : (0 : ℝ) ≤ N.rd := by
    unfold NumDatum.rd Formalism.HC.HostRaw.rd
    positivity
  have ho : (1 : ℝ) ≤ N.R.ord := by exact_mod_cast N.R.ord_pos
  nlinarith

theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

theorem two_le_b (s : Scale) : 2 ≤ s.b := by
  have := Real.add_one_le_exp s.L
  have := one_le_L s
  unfold Scale.b; linarith

theorem card_RPl (R : Ranks) : (Fintype.card (RPl R) : ℝ) = R.f := by
  have h : Fintype.card R.A = R.ord := R.card_A
  simp [RPl, Ranks.f, Ranks.n, h]

theorem N_le (N : NumDatum) {j : ℕ} (hj : j ≤ N.R.m) : (N.R.N j : ℝ) ≤ N.Nm := by
  have : N.R.N j ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  exact_mod_cast this

theorem log_le_mul (s : Scale) {y : ℝ} (hy : 0 ≤ y) (k : ℕ) (h : y ≤ s.b ^ k) : Real.log y ≤ k * s.L := by
  have := one_le_L s
  refine log_le_of_le_exp hy (by positivity) ?_
  rw [Real.exp_nat_mul]; exact h

end GlobalTheory.ColNorms.NumMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictAntiOfStep
open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem strictAnti_of_step {N : ℕ} {α : Type} [Preorder α] (f : Fin N → α)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  cases N with
  | zero => intro a; exact a.elim0
  | succ n =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact h _ _ (by simp)

theorem divided_strictAnti : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ,
    StrictAnti (W.u1 τ) ∧ StrictAnti (W.u' τ) ∧ StrictAnti (fun i => (W.u1 τ i : ℝ)) := by
  intro ι _ N W H hD τ
  have hT : (4 : ℤ) ≤ W.T := by have := H.h1; omega
  have hh : (0 : ℤ) < W.h0 := by
    obtain ⟨k1, _⟩ := H.h2
    have := H.weightConst_nonneg
    omega
  have step : ∀ a b : Fin N, (b : ℕ) = a + 1 → W.u1 τ b < W.u1 τ a ∧ W.u' τ b < W.u' τ a := by
    intro a b hab
    obtain ⟨g1, g2, _⟩ := divided_gaps ι N W H hD τ a b hab
    by_cases hb : (b : ℕ) = W.p
    · obtain ⟨e1, e2⟩ := g2 hb
      have ha : ¬ ((b : ℕ) < W.p) := by omega
      have ha' : (a : ℕ) < W.p := by omega
      have p1 : 0 < W.u1 τ a - W.u1 τ b := by
        by_contra hc
        push_neg at hc
        nlinarith
      have p2 : 0 < W.u1 τ a - W.u1 τ b - 3 * N := by
        by_contra hc
        push_neg at hc
        nlinarith
      refine ⟨by omega, ?_⟩
      simp only [Wts.u', if_pos ha', if_neg ha]
      omega
    · have e := g1 hb
      have hN : (0 : ℤ) ≤ W.T + W.Dd + 2 + 2 * N := by positivity
      refine ⟨by omega, ?_⟩
      simp only [Wts.u']
      by_cases ha : (a : ℕ) < W.p
      · have hb' : (b : ℕ) < W.p := by omega
        rw [if_pos ha, if_pos hb']; omega
      · have hb' : ¬ (b : ℕ) < W.p := by omega
        rw [if_neg ha, if_neg hb']; omega
  have s1 : StrictAnti (W.u1 τ) := strictAnti_of_step _ fun a b h => (step a b h).1
  exact ⟨s1, strictAnti_of_step _ fun a b h => (step a b h).2,
    (Int.cast_strictMono (R := ℝ)).comp_strictAnti s1⟩

end GlobalTheory.MeanTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticePointsSymmetricMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticePointsSymmetricMem
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem stable_sym_mem (F : IntermediateField ℚ ℂ) (L : PeriodPair) (ι : Type) [Fintype ι] (T : ι → ℂ) :
    L.g₂ ∈ F → L.g₃ ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice) →
    (∑ i, L.weierstrassP (T i)) ∈ F ∧ (∑ i, L.derivWeierstrassP (T i) / 2) ∈ F ∧
    (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) ∈ F ∧
    ((∀ i, 2 * T i ∉ L.lattice) → (∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i))) ∈ F) := by
  intro h₂ h₃ hS hT
  have key : ∀ σ : ℂ ≃+* ℂ, (∀ x ∈ F, σ x = x) → ∃ e : ι ≃ ι,
      (∀ i, σ (L.weierstrassP (T i)) = L.weierstrassP (T (e i))) ∧
      (∀ i, σ (L.derivWeierstrassP (T i)) = L.derivWeierstrassP (T (e i))) ∧
      ((∀ i, 2 * T i ∉ L.lattice) → ∀ i, σ (L.weierstrassP (2 * T i)) = L.weierstrassP (2 * T (e i))) ∧
      σ L.g₂ = L.g₂ := by
    intro σ hσ
    obtain ⟨e, he⟩ := hS σ hσ
    have g₂e : L.g₂ = σ L.g₂ := (hσ _ h₂).symm
    have g₃e : L.g₃ = σ L.g₃ := (hσ _ h₃).symm
    refine ⟨e, fun i ↦ ?_, fun i ↦ ?_, fun h2 i ↦ ?_, hσ _ h₂⟩
    · exact (((he i).resolve_left fun h ↦ hT i h.1).2.2.1).symm
    · exact (((he i).resolve_left fun h ↦ hT i h.1).2.2.2).symm
    · have := GlobalTheory.ConjPoint.IsConj.add g₂e g₃e (he i) (he i)
      rw [← two_mul, ← two_mul] at this
      exact ((this.resolve_left fun h ↦ h2 i h.1).2.2.1).symm
  refine ⟨GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_, GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_,
    GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_, fun h2 ↦ GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F _ fun σ hσ ↦ ?_⟩
  · obtain ⟨e, a, -, -, -⟩ := key σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp only [a]; exact Equiv.sum_comp e (fun i ↦ L.weierstrassP (T i))
  · obtain ⟨e, -, b, -, -⟩ := key σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp only [map_div₀, map_ofNat, b]
    exact Equiv.sum_comp e (fun i ↦ L.derivWeierstrassP (T i) / 2)
  · obtain ⟨e, a, b, -, g⟩ := key σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_div₀, map_add (f := _), map_mul, map_pow, map_neg, map_ofNat, a, b, g]
    exact Equiv.sum_comp e (fun i ↦ (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2)))
  · obtain ⟨e, a, -, c, -⟩ := key σ hσ
    rw [map_prod]; simp only [map_sub, a, c h2]
    exact Equiv.prod_comp e (fun i ↦ L.weierstrassP (T i) - L.weierstrassP (2 * T i))

end GlobalTheory.CMModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisStableLatticePointsSymmetricMemStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisStable_lattice_points_symmetric_mem : ∀ (F : IntermediateField ℚ ℂ) (L : PeriodPair) (ι : Type) [Fintype ι] (T : ι → ℂ), L.g₂ ∈ F → L.g₃ ∈ F → Stable L F T → (∀ i, T i ∉ L.lattice) → (∑ i, L.weierstrassP (T i)) ∈ F ∧ (∑ i, L.derivWeierstrassP (T i) / 2) ∈ F ∧ (∑ i, (3 * L.weierstrassP (T i) ^ 2 + -L.g₂ / 4) / (2 * (L.derivWeierstrassP (T i) / 2))) ∈ F ∧ ((∀ i, 2 * T i ∉ L.lattice) → (∏ i, (L.weierstrassP (T i) - L.weierstrassP (2 * T i))) ∈ F) := by
  first | exact @GlobalTheory.CMModel.stable_sym_mem | exact GlobalTheory.CMModel.stable_sym_mem | (intros; apply GlobalTheory.CMModel.stable_sym_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteField
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

theorem exists_labelsChar_of_pos (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) :
    ∃ x : Fbar p, LabelsChar L θ x := by
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h0 : L.gen d ≠ 0 := hprim.ne_zero hp.ne'
  have hprimC : IsPrimitiveRoot (L.teich (L.gen d)) (p ^ d - 1) := by
    refine ⟨by rw [← map_pow, hprim.pow_eq_one, map_one], fun l hl => hprim.dvd_of_pow_eq_one l ?_⟩
    exact L.teich_inj _ _ (pow_ne_zero _ h0) one_ne_zero (by rw [map_pow, hl, map_one])
  let γ : Tor p d := ⟨Units.mk0 _ h0, by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hprim.pow_eq_one)⟩
  have hγ : γ ^ (p ^ d - 1) = 1 := Subtype.ext ((mem_rootsOfUnity _ _).1 γ.2)
  obtain ⟨k, -, hk⟩ := hprimC.eq_pow_of_pow_eq_one (ξ := ((θ γ : ℂˣ) : ℂ))
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, hγ, map_one, Units.val_one])
  refine ⟨L.gen d ^ k, by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow], fun u => ?_⟩
  have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
  have hex : ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n := ⟨n, hn.symm⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left hex]
  have e : u = γ ^ hex.choose := Subtype.ext (Units.ext (by simpa [γ] using hex.choose_spec))
  rw [map_pow, hk, ← Units.val_pow_eq_pow_val, ← map_pow, ← e]

theorem prod_frobenius_orbit_mem_lifts {d : ℕ} {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1) :
    (∏ i : Fin d, (X - C (x ^ p ^ (i : ℕ)))) ∈ Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
  have hxd : x ^ p ^ d = x := by
    have h1 : p ^ d = (p ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)).symm
    rw [h1, pow_succ, hx, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d]
  have hfix : (∏ i ∈ Finset.range d, (X - C (x ^ p ^ i) : (Fbar p)[X])).map (frobenius (Fbar p) p) =
      ∏ i ∈ Finset.range d, (X - C (x ^ p ^ i)) := by
    have h1 := Finset.prod_range_succ (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d
    rw [Finset.prod_range_succ', hxd, pow_zero, pow_one] at h1
    rw [Polynomial.map_prod, ← mul_right_cancel₀ (X_sub_C_ne_zero x) h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, frobenius_def, pow_succ, pow_mul]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  have h2 := congrArg (fun q => q.coeff n) hfix
  simp only [coeff_map, frobenius_def] at h2
  obtain ⟨m, hm⟩ := (mem_bot_iff_intCast p (Fbar p)).1 ((Subfield.mem_bot_iff_pow_eq_self (Fbar p) p).2 h2)
  exact ⟨(m : ZMod p), by rw [map_intCast, hm]⟩

theorem exists_labels (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r) :
    ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  choose x hx using fun c : Cyc s.1 => exists_labelsChar_of_pos L (cycLen_pos s.1 c) (s.2 c)
  have hl : (∏ y : Σ c : Cyc s.1, Fin (cycLen s.1 c), (X - C (rootElt x y))) ∈
      Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
    rw [Fintype.prod_sigma]
    refine Subsemiring.prod_mem _ fun c _ => ?_
    simp only [rootElt]
    exact prod_frobenius_orbit_mem_lifts (d := cycLen s.1 c) (x := x c) (hx c).1
  obtain ⟨f, hf, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (monic_prod_of_monic _ _ fun y _ => monic_X_sub_C _)
  refine ⟨x, f, hx, fun c => (hx c).1, hm, ?_⟩
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [hf, ← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map (rootElt x)), Multiset.map_map]
  rfl

end GlobalTheory.ParamLabel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteFieldStatement
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labels_semisimple_parameter_GL_finiteField : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r), ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  first | exact @GlobalTheory.ParamLabel.exists_labels | exact GlobalTheory.ParamLabel.exists_labels | (intros; apply GlobalTheory.ParamLabel.exists_labels <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDerivWeierstrassPOddTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDerivWeierstrassPOddTorsion
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem finset_prod_eq_one_of_le_one_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Γ) (hle : ∀ i ∈ s, f i ≤ 1)
    (hprod : ∏ i ∈ s, f i = 1) : ∀ i ∈ s, f i = 1 := by
  intro i hi
  refine le_antisymm (hle i hi) ?_
  rw [← Finset.mul_prod_erase s f hi] at hprod
  have h2 : ∏ j ∈ s.erase i, f j ≤ 1 :=
    Finset.prod_le_one' (fun j hj => hle j (Finset.mem_of_mem_erase hj))
  calc (1 : Γ) = f i * ∏ j ∈ s.erase i, f j := hprod.symm
    _ ≤ f i := mul_le_of_le_one_right' h2

theorem valuation_derivWeierstrassP_torsion_odd :
    ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 →
      V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N →
      ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice →
        V.valuation (L.derivWeierstrassP z) = V.valuation u ^ 3 := by
  intro L β u V N hβ hβim hu hN hodd z hz hNz
  classical
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
    exact_mod_cast this
  have hstab : MulStable L (N : ℂ) := by
    intro ω hω
    have := L.lattice.smul_mem (N : ℤ) hω
    simpa [zsmul_eq_mul] using this
  have hΔ := latticeCurve_Δ_ne_zero L
  have hvΔ : V.valuation (latticeCurve L).Δ ≠ 0 := by
    simpa using hΔ
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hvΔ
    rw [← hu]; simp
  have hvu : V.valuation u ≠ 0 := by simpa using hu0
  obtain ⟨S, hS⟩ := kerRepsExist L (N : ℂ) hN0 hstab
  have hcard := kerRepsCard L (N : ℂ) S hN0 hstab hS
  have hcardN : S.card + 1 = N * N := by
    have : ((S.card + 1 : ℕ) : ℝ) = ((N * N : ℕ) : ℝ) := by
      push_cast; rw [hcard]; simp [Complex.normSq_apply]
    exact_mod_cast this
  have heven : Even S.card := by
    have hodd2 : Odd (N * N) := hodd.mul hodd
    rw [← hcardN] at hodd2
    obtain ⟨k, hk⟩ := hodd2
    exact ⟨k, by omega⟩
  have hpf := GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (N : ℂ) S hN0 hstab hS heven
  have hmem : ∀ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ≤ 1 := by
    intro t ht
    rw [ValuationSubring.valuation_le_one_iff]
    exact (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN t t (hS.1 t ht).2 (hS.1 t ht).2 (hS.1 t ht).1
      (hS.1 t ht).1).1
  have hprod : ∏ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ^ 4 = 1 := by
    have hv := congrArg V.valuation hpf
    simp only [map_mul, map_pow, map_prod, hN, one_pow, mul_one] at hv
    simp only [map_div₀, map_pow, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
      Finset.prod_const, ← pow_mul]
    rw [hv, ← hu, ← pow_mul, div_eq_one_iff_eq (pow_ne_zero _ hvu)]
    ring_nf
  have hall := finset_prod_eq_one_of_le_one_eq_one S _ (fun t ht => pow_le_one' (hmem t ht) 4) hprod
  obtain ⟨t, ht, hzt⟩ := hS.2.2 z (by simpa [mul_comm] using hNz) hz
  have hper : L.derivWeierstrassP z = L.derivWeierstrassP t := by
    have := L.derivWeierstrassP_add_coe t ⟨z - t, hzt⟩
    simpa using this
  have h1 : V.valuation (L.derivWeierstrassP t / u ^ 3) = 1 := by
    have h4 := hall t ht
    by_contra hne
    have hlt : V.valuation (L.derivWeierstrassP t / u ^ 3) < 1 := lt_of_le_of_ne (hmem t ht) hne
    exact absurd h4 (ne_of_lt (pow_lt_one' hlt (by norm_num)))
  rw [hper]
  rw [map_div₀, map_pow, div_eq_one_iff_eq (pow_ne_zero _ hvu)] at h1
  exact h1
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDerivWeierstrassPOddTorsionStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_derivWeierstrassP_oddTorsion : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N → ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → V.valuation (L.derivWeierstrassP z) = V.valuation u ^ 3 := by
  first | exact @GlobalTheory.valuation_derivWeierstrassP_torsion_odd | exact GlobalTheory.valuation_derivWeierstrassP_torsion_odd | (intros; apply GlobalTheory.valuation_derivWeierstrassP_torsion_odd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEqui
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfForallExistsFix
universe u_1 u_2 u_3 u_4

namespace GlobalTheory.ContinuityFromFixedPoints

open Topology

theorem continuous_of_forall_exists_fix {k : Type u_1} {F : Type u_2} {k' : Type u_3}
    {F' : Type u_4} [Field k] [Field F] [Algebra k F] [Field k'] [Field F'] [Algebra k' F']
    [Algebra.IsIntegral k F] (φ : Gal(F/k) →* Gal(F'/k'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : Gal(F/k), σ x = x → φ σ y = y) :
    Continuous φ := by
  classical
  choose x hx using h
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E', hE', hs'⟩ := (krullTopology_mem_nhds_one_iff k' F' s).1 hs
  let b := Module.finBasis k' E'
  let S : Set F := Set.range fun i => x (b i : F')
  have hS : S.Finite := Set.finite_range _
  haveI : Finite S := hS.to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff k F _).2 ⟨IntermediateField.adjoin k S, hfin, ?_⟩
  intro σ hσ
  apply hs'
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  have hb : ∀ i, φ σ (b i : F') = b i := fun i =>
    hx _ σ (hσ _ (IntermediateField.subset_adjoin k S ⟨i, rfl⟩))
  intro y hy
  have hlin : ((φ σ).toLinearMap ∘ₗ E'.val.toLinearMap) = E'.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun hlin ⟨y, hy⟩

end GlobalTheory.ContinuityFromFixedPoints
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEqui
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeGal

theorem continuous_galHom_of_fix {k F k' F' : Type*} [Field k] [Field F] [Algebra k F] [Field k'] [Field F']
    [Algebra k' F'] [Algebra.IsIntegral k F] (φ : (F ≃ₐ[k] F) →* (F' ≃ₐ[k'] F'))
    (h : ∀ y : F', ∃ x : F, ∀ σ : F ≃ₐ[k] F, σ x = x → φ σ y = y) : Continuous φ := by
  first
  | exact @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix
  | (apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuityFromFixedPoints.continuous_of_forall_exists_fix ..)

theorem exists_topAbelianization_mulEquiv {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G ≃* H) (hφ : IsHomeomorph φ) :
    ∃ ψ : TopologicalAbelianization G ≃* TopologicalAbelianization H, IsHomeomorph ψ ∧
      ∀ g : G, ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := _root_.ReciprocityTheory.DiscreteGroups.LocalClassField.exists_topAb_iso (G := G) (H := H) φ hφ

theorem exists_abMap_of_algEquiv : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω]
    (e : Ω ≃ₐ[K] AlgebraicClosure K), ∃ φ : GlobalTheory.HeckeGal.Gab K Ω →* Field.absoluteGaloisGroupAbelianization K,
      Continuous φ ∧ Function.Bijective φ ∧
      ∀ σ : Formalism.ConjugateSelfDual.G K Ω, φ (GlobalTheory.HeckeGal.toAb K Ω σ) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  intro K _ _ Ω _ _ e
  haveI hint : Algebra.IsIntegral K Ω :=
    ⟨fun x => (isIntegral_algEquiv e).1 (Algebra.IsIntegral.isIntegral (e x))⟩
  let φ : (Ω ≃ₐ[K] Ω) ≃* Field.absoluteGaloisGroup K := AlgEquiv.autCongr e
  have h1 : Continuous φ.toMonoidHom :=
    continuous_galHom_of_fix φ.toMonoidHom fun y => ⟨e.symm y, fun σ hσ => by
      show e (σ (e.symm y)) = y
      rw [hσ, AlgEquiv.apply_symm_apply]⟩
  have h2 : Continuous φ.symm.toMonoidHom :=
    continuous_galHom_of_fix φ.symm.toMonoidHom fun y => ⟨e y, fun τ hτ => by
      show e.symm (τ (e y)) = y
      rw [hτ, AlgEquiv.symm_apply_apply]⟩
  have hφ : IsHomeomorph φ := (Homeomorph.mk φ.toEquiv h1 h2).isHomeomorph
  obtain ⟨ψ, hψ, hψg⟩ := exists_topAbelianization_mulEquiv φ hφ
  refine ⟨ψ.toMonoidHom, hψ.continuous, ψ.bijective, fun σ => ?_⟩
  exact hψg σ

end GlobalTheory.HeckeGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousBijectiveAbelianizationOfAlgEquiStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_bijective_abelianization_of_algEquiv : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K), ∃ φ : GlobalTheory.HeckeGal.Gab K Ω →* Field.absoluteGaloisGroupAbelianization K, Continuous φ ∧ Function.Bijective φ ∧ ∀ σ : Formalism.ConjugateSelfDual.G K Ω, φ (GlobalTheory.HeckeGal.toAb K Ω σ) = Neutral.B1.toAb K ((e.symm.trans σ).trans e) := by
  first | exact @GlobalTheory.HeckeGal.exists_abMap_of_algEquiv | exact GlobalTheory.HeckeGal.exists_abMap_of_algEquiv | (intros; apply GlobalTheory.HeckeGal.exists_abMap_of_algEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpread
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpread
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem Wts.node_lower_int {ι : Type} {N : ℕ} (W : Wts ι N) (H : W.Hyp) (hd : W.IsDiv) (τ : ι) :
    ∀ (n : ℕ) (i : Fin N), (i : ℕ) + 1 = W.kc + n →
      -W.u τ i - (if W.p ≤ (i : ℕ) then W.c0 + 2 * (N : ℤ) else 0) - n * ((W.T : ℤ) + W.Dd + 1) ≤
        ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) := by
  intro n
  have hkp := H.kc_lt
  induction n with
  | zero =>
    intro i hi
    have h1 := (hd τ).1 i (by simpa using hi)
    have h2 := H.anchor τ i (by simpa using hi)
    have h3 : ¬ W.p ≤ (i : ℕ) := by omega
    simp [h1, h2, h3]
  | succ n ih =>
    intro i hi
    have hk := H.kc_pos
    have hlt : (i : ℕ) - 1 < N := by omega
    have hab : (i : ℕ) = ((⟨(i : ℕ) - 1, hlt⟩ : Fin N) : ℕ) + 1 := by simp; omega
    have ha : ((⟨(i : ℕ) - 1, hlt⟩ : Fin N) : ℕ) + 1 = W.kc + n := by simp; omega
    generalize (⟨(i : ℕ) - 1, hlt⟩ : Fin N) = a at hab ha
    have h1 := ih a ha
    have h2 := (hd τ).2 a i hab
    have hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
    generalize (W.T : ℤ) + W.Dd + 1 = M at h1 h2 hM ⊢
    set x := (W.u τ a - W.u τ i + if (i : ℕ) = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) with hx
    have h3 := Int.mul_ediv_add_emod x M
    have h4 := Int.emod_lt_of_pos x hM
    rw [← h2] at h3
    have h5 : M * -W.u1 τ i = M * -W.u1 τ a + M * (W.u1 τ a - W.u1 τ i) := by ring
    have h6 : ((n + 1 : ℕ) : ℤ) * M = n * M + M := by push_cast; ring
    rw [h5, h6]
    by_cases hp : (i : ℕ) = W.p
    · have e1 : W.p ≤ (i : ℕ) := by omega
      have e2 : ¬ W.p ≤ (a : ℕ) := by omega
      rw [if_pos hp] at hx
      rw [if_neg e2] at h1
      rw [if_pos e1]
      linarith
    · rw [if_neg hp] at hx
      by_cases e1 : W.p ≤ (i : ℕ)
      · have e2 : W.p ≤ (a : ℕ) := by omega
        rw [if_pos e2] at h1
        rw [if_pos e1]
        linarith
      · have e2 : ¬ W.p ≤ (a : ℕ) := by omega
        rw [if_neg e2] at h1
        rw [if_neg e1]
        linarith

theorem nodes_far_and_spread : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ, (∀ i : Fin N, W.kc ≤ (i : ℕ) → W.w τ / (2 * W.T) ≤ -(W.u1 τ i : ℝ) ∧ W.w τ / (4 * W.T) ≤ |(W.u' τ i : ℝ)|) ∧ ∀ i l : Fin N, (W.u' τ i : ℝ) - W.u' τ l ≤ 3 / 2 * W.w τ / W.T := by
  intro ι _ N W H hd τ
  have hk := H.kc_pos
  have hkp := H.kc_lt
  have hpN := H.p_lt
  have hc0 : (0 : ℝ) ≤ W.c0 := by exact_mod_cast H.weightConst_nonneg
  have hT : 4 * (W.Dd : ℝ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hD : (0 : ℝ) ≤ W.Dd := by positivity
  have hN : (0 : ℝ) ≤ N := by positivity
  have hT0 : (0 : ℝ) < W.T := by linarith
  have hw := H.h3w τ
  have hS : 0 ≤ W.S := by
    have := H.h3cloud τ ⟨0, by omega⟩ (by simp; omega)
    have h0 : (0 : ℝ) ≤ W.u τ ⟨0, by omega⟩ := by exact_mod_cast this.1
    linarith [this.2]
  have hr : 0 ≤ W.eta + W.S + N := (abs_nonneg _).trans (H.h3node τ ⟨W.p, hpN⟩ hkp.le)
  have hNT : 4 * (N : ℝ) ≤ N * W.T := by nlinarith
  have hw0 : 0 ≤ W.w τ := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = W.w τ / W.T := ⟨_, rfl⟩
  have hqT : W.w τ = q * W.T := by rw [hq]; field_simp
  have e2 : W.w τ / (2 * W.T) = q / 2 := by rw [hq]; field_simp
  have e4 : W.w τ / (4 * W.T) = q / 4 := by rw [hq]; field_simp
  have e3 : 3 / 2 * W.w τ / W.T = 3 / 2 * q := by rw [hq]; field_simp
  rw [e2, e4, e3]
  have hq20 : 20 * (N : ℝ) ≤ q := by
    have : 20 * (N : ℝ) * W.T ≤ q * W.T := by linarith
    exact le_of_mul_le_mul_right this hT0
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by linarith
  have hM1 : M ≤ 5 / 4 * W.T := by linarith
  have hM2 : (W.T : ℝ) ≤ M := by linarith
  have hu' : ∀ i : Fin N, (W.u1 τ i : ℝ) ≤ W.u' τ i ∧ (W.u' τ i : ℝ) ≤ W.u1 τ i + 3 * N ∧
      ((i : ℕ) < W.kc → (W.u' τ i : ℝ) = W.u1 τ i) := by
    intro i
    unfold Wts.u'
    by_cases h : (i : ℕ) < W.p
    · simp [h]
    · simp only [h, if_false]
      push_cast
      exact ⟨by linarith, le_rfl, fun h' => by omega⟩
  have node : ∀ i : Fin N, W.kc ≤ (i : ℕ) → q / 2 ≤ -(W.u1 τ i : ℝ) := by
    intro i hi
    have h1 := W.node_lower_int H hd τ ((i : ℕ) + 1 - W.kc) i (by omega)
    have hn : (((i : ℕ) + 1 - W.kc : ℕ) : ℝ) ≤ N := by
      have : (i : ℕ) + 1 - W.kc ≤ N := by omega
      exact_mod_cast this
    generalize (i : ℕ) + 1 - W.kc = n at h1 hn
    have h2 : -W.u τ i - (W.c0 + 2 * (N : ℤ)) - n * ((W.T : ℤ) + W.Dd + 1) ≤
        ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) := by
      have := H.weightConst_nonneg
      split_ifs at h1
      · exact h1
      · have : (0 : ℤ) ≤ N := by positivity
        linarith
    have h3 : -(W.u τ i : ℝ) - (W.c0 + 2 * (N : ℝ)) - n * M ≤ M * (-(W.u1 τ i : ℝ)) := by
      rw [hM]; exact_mod_cast h2
    have h4 := (abs_le.1 (H.h3node τ i hi)).2
    have h5 : (n : ℝ) * M ≤ q / 10 * M := mul_le_mul_of_nonneg_right (by linarith) hM0.le
    have h6 : q * M ≤ q * (5 / 4 * W.T) := mul_le_mul_of_nonneg_left hM1 hq0
    have h7 : M * (q / 2) ≤ M * (-(W.u1 τ i : ℝ)) := by nlinarith
    exact le_of_mul_le_mul_left h7 hM0
  have ent : ∀ i : Fin N, M * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + W.c0 + 4 * N := by
    intro i
    rw [hM]
    exact_mod_cast (GlobalTheory.MeanTop.divided_entries ι N W H hd τ i).1
  refine ⟨fun i hi => ⟨node i hi, ?_⟩, fun i l => ?_⟩
  · have h1 := node i hi
    have h2 := (hu' i).2.1
    have h3 := neg_le_abs (W.u' τ i : ℝ)
    linarith
  · have up : M * (W.u' τ i : ℝ) ≤ W.S + W.c0 + 4 * N := by
      by_cases hi : (i : ℕ) < W.kc
      · rw [(hu' i).2.2 hi]
        have h1 := ent i
        have h2 := H.h3cloud τ i hi
        have h3 : (0 : ℝ) ≤ W.u τ i := by exact_mod_cast h2.1
        rw [abs_of_nonneg h3] at h1
        have h4 := mul_le_mul_of_nonneg_left (le_abs_self (W.u1 τ i : ℝ)) hM0.le
        linarith [h2.2]
      · have h1 := node i (by omega)
        have h2 := (hu' i).2.1
        have h3 : M * (W.u' τ i : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0.le (by linarith)
        linarith
    have lo : M * (-(W.u' τ l : ℝ)) ≤ W.w τ + (W.eta + W.S + N) + W.S + W.c0 + 4 * N := by
      have h1 := ent l
      have h2 : -(W.u' τ l : ℝ) ≤ |(W.u1 τ l : ℝ)| := by
        linarith [(hu' l).1, neg_le_abs (W.u1 τ l : ℝ)]
      have h3 := mul_le_mul_of_nonneg_left h2 hM0.le
      have h4 : |(W.u τ l : ℝ)| ≤ W.w τ + (W.eta + W.S + N) + W.S := by
        by_cases hl : (l : ℕ) < W.kc
        · have h2 := H.h3cloud τ l hl
          have h3 : (0 : ℝ) ≤ W.u τ l := by exact_mod_cast h2.1
          rw [abs_of_nonneg h3]
          linarith [h2.2]
        · have h5 := abs_le.1 (H.h3node τ l (by omega))
          rw [abs_le]
          constructor <;> linarith [h5.1, h5.2]
      linarith
    have h6 : q * W.T ≤ q * M := mul_le_mul_of_nonneg_left hM2 hq0
    have h7 : M * ((W.u' τ i : ℝ) - W.u' τ l) ≤ M * (3 / 2 * q) := by nlinarith
    exact le_of_mul_le_mul_left h7 hM0

end GlobalTheory.MeanTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpreadStatement
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedWeight_nodes_far_and_spread : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ, (∀ i : Fin N, W.kc ≤ (i : ℕ) → W.w τ / (2 * W.T) ≤ -(W.u1 τ i : ℝ) ∧ W.w τ / (4 * W.T) ≤ |(W.u' τ i : ℝ)|) ∧ ∀ i l : Fin N, (W.u' τ i : ℝ) - W.u' τ l ≤ 3 / 2 * W.w τ / W.T := by
  first | exact @GlobalTheory.MeanTop.nodes_far_and_spread | exact GlobalTheory.MeanTop.nodes_far_and_spread | (intros; apply GlobalTheory.MeanTop.nodes_far_and_spread <;> assumption)
end
end
