module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingCompatibleAddSecondSlotComplexStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisFix
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.HeisFix

theorem heis_fix : ∀ {D : D7}, Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
    ∀ (o : ℕ) {k : GA D P.a}, k ∈ intG D P.a → CongOne D 𝔪 k →
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 ∈
      TT D (tor0 D ⊤ δ) P.a P.d →
    P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 →
    P.W.Om k 1 (Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d))
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0)) =
      Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d))
        (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) := by
  intro D hD δ t0 Q P 𝔪 h𝔪 o k hk hc hIT hfix
  have h1 := hD.g1
  have he := P.vac.1
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) :=
    VacMove.klat _ (VacMove.moves_one D P.a) (VacMove.moves_one D P.d)
  have kB : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D P.a), GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d, rfl⟩
  have hHB := (hD.uni ⊤ δ P.crv P.a P.d _ _ k0 kB P.e0 he).2.1
  obtain ⟨m, hm, hl⟩ := P.W.lift k 1 (unitBlock D o P.a P.d) _ hIT
  have hx₀int : ∀ i j, ∃ b : 𝓞 D.host.E, unitBlock D o P.a P.d i j = (b : D.host.E) := by
    intro i j
    by_cases h : i.1 = o + j.1
    · exact ⟨1, by simp [unitBlock, h]⟩
    · exact ⟨0, by simp [unitBlock, h]⟩
  obtain ⟨w, hw, hclose⟩ := GlobalTheory.CongApprox.exists_closeTo_congOne D 𝔪 h𝔪 k hk hc _ hx₀int m hm
  have hmain := hl _ hclose
  rw [hfix] at hmain
  rw [hmain]
  obtain ⟨hw0, hwB⟩ := GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ 𝔪 w hw
  have hx0 := pt_unitBlock_mem (D := D) δ o P.a P.d
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (unitBlock D o P.a P.d)) (pt D (tor0 D ⊤ δ) δ w)
  have hφ1 : φ = 1 := by
    have h2 := hφ P.e0
    rw [VacMove.wd_fix h1 P.crv k0 he hw0, VacMove.wd_fix h1 P.crv k0 he hx0,
      VacMove.wd_fix h1 P.crv k0 he (add_mem hx0 hw0)] at h2
    by_contra hne
    apply P.W.nz
    have : (φ - 1) • P.e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h3 := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0)
  rw [VacMove.wd_fix h1 P.crv kB hHB hwB, hφ1, one_smul, ← VacMove.pt_add] at h3
  exact h3.symm

end GlobalTheory.HeisFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompDet
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.FunObj.NormUniq.SplitDet

theorem exists_splitComp_det : ∀ {D : D7} {N : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {k : GA D N}, k ∈ intG D N → CongOne D 𝔪 k →
    SuppSplit D (k : GL (Fin N) (AE D)) → ∃ x : (AE D)ˣ, IntU D x ∧
      (∀ q : ℕ, q.Prime → InertQ D q → ZeroAt D q ((x : AE D) - 1)) ∧
      x = Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) * sgU D x ∧
      (x : AE D) - 1 ∈ hatId D 𝔪 ∧ (x : AE D) - 1 ∈ hatId D (D.host.conj • 𝔪) := by
  intro D N 𝔪 k hk hc hs
  have hint := (mem_intG k).1 hk
  have huO : ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) ∈ OhE D :=
    VacMove.det_int D _ hint
  have hn := VacMove.det_norm D k
  have hm1 : ((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1 ∈ hatId D 𝔪 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem_hatId_of _ (fun i j => (hint i j).1) hc
  have hz : ∀ q : ℕ, q.Prime → InertQ D q →
      ZeroAt D q (((Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) : (AE D)ˣ) : AE D) - 1) :=
    fun q hq hi => GlobalTheory.VacuumScalar.zeroAt_det hq (hs q hq hi)
  set U := Matrix.GeneralLinearGroup.det (k : GL (Fin N) (AE D)) with hU
  set u : AE D := (U : AE D) with hu
  have hm2 : u - 1 ∈ hatId D (D.host.conj • 𝔪) := by
    have e : u - 1 = -(u * sgA D (u - 1)) := by
      rw [map_sub, map_one, mul_sub, hn]; ring
    rw [e]
    exact neg_mem (GlobalTheory.FunObj.StdDatum.mul_mem_hatId huO (GlobalTheory.FunObj.StdDatum.DetCong.sgA_mem_hatId hm1))
  obtain ⟨ε, hε, h1, h2, h3⟩ := VacMove.exists_half_idem D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  have hεε : sgA D (sgA D ε) = ε := VacMove.sgA_sgA D ε
  set η := sgA D ε with hη
  set v := sgA D u with hv
  have hx : ((1 - η) + η * u) * ((1 - η) + η * v) = 1 := by
    linear_combination (1 - u - v + u * v) * h1' + η * hn
  let x : (AE D)ˣ := ⟨_, _, hx, by rw [mul_comm, hx]⟩
  have hxv : (x : AE D) = (1 - η) + η * u := rfl
  have hx1 : (x : AE D) - 1 = η * (u - 1) := by rw [hxv]; ring
  have hηO : η ∈ OhE D := VacMove.sgA_mem D hε
  have h0 : (1 - u) * (1 - (ε + η)) = 0 := by
    refine GlobalTheory.VacuumScalar.eq_zero_of_zeroAt _ fun q hq => ?_
    by_cases hi : InertQ D q
    · convert VacMove.zeroAt_mul D hq (hz q hq hi) (-(1 - (ε + η))) using 1
      ring
    · convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) (1 - u) using 1
      ring
  refine ⟨x, ⟨?_, ?_⟩, fun q hq hi => ?_, ?_, ?_, ?_⟩
  · rw [hxv]; exact add_mem (sub_mem (one_mem _) hηO) (mul_mem hηO huO)
  · change (1 - η) + η * v ∈ OhE D
    exact add_mem (sub_mem (one_mem _) hηO) (mul_mem hηO (VacMove.sgA_mem D huO))
  · convert VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) (η * (u - 1)) using 1
    rw [hx1]
    linear_combination (-(u - 1)) * h2 + (-(u - 1)) * h1'
  · ext
    change (1 - η) + η * u = u * sgA D ((1 - η) + η * u)
    rw [map_add (f := _), map_mul, map_sub, map_one, hεε]
    linear_combination h0 - ε * hn
  · rw [hx1]; exact GlobalTheory.FunObj.StdDatum.mul_mem_hatId hηO hm1
  · rw [hx1]; exact GlobalTheory.FunObj.StdDatum.mul_mem_hatId hηO hm2

end GlobalTheory.FunObj.NormUniq.SplitDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitInertFactor
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.CongSplitFactor

variable {D : D7} {N : ℕ}

noncomputable def phi (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D) :=
  e • A + (1 - e) • (1 : Matrix (Fin N) (Fin N) (AE D))

theorem phi_apply (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) (i j : Fin N) :
    phi e A i j = e * A i j + (1 - e) * (1 : Matrix (Fin N) (Fin N) (AE D)) i j := by
  simp [phi, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem phi_sub_one (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A - 1 = e • (A - 1) := by
  rw [phi, sub_smul, one_smul, smul_sub]; abel

theorem phi_one (e : AE D) : phi e (1 : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
  rw [phi, ← add_smul, add_sub_cancel, one_smul]

theorem phi_mul {e : AE D} (he : e * e = e) (A B : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A * phi e B = phi e (A * B) := by
  have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem phi_mul_compl {e : AE D} (he : e * e = e) (A : Matrix (Fin N) (Fin N) (AE D)) :
    phi e A * phi (1 - e) A = A := by
  have h1 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  simp only [phi, sub_sub_cancel, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

noncomputable def phiHom {e : AE D} (he : e * e = e) :
    Matrix (Fin N) (Fin N) (AE D) →* Matrix (Fin N) (Fin N) (AE D) where
  toFun := phi e
  map_one' := phi_one e
  map_mul' A B := (phi_mul he A B).symm

theorem phi_map (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    (phi e A).map (sgA D) = phi (sgA D e) (A.map (sgA D)) := by
  ext i j
  simp only [Matrix.map_apply, phi_apply, map_add (f := _), map_mul, map_sub, map_one]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem phi_transpose (e : AE D) (A : Matrix (Fin N) (Fin N) (AE D)) :
    (phi e A).transpose = phi e A.transpose := by
  simp [phi, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem phi_mem_OhE {e : AE D} (he : e ∈ OhE D) {A : Matrix (Fin N) (Fin N) (AE D)}
    (hA : ∀ i j, A i j ∈ OhE D) (i j : Fin N) : phi e A i j ∈ OhE D := by
  rw [phi_apply]
  refine add_mem (mul_mem he (hA i j)) (mul_mem (sub_mem (one_mem _) he) ?_)
  by_cases h : i = j
  · simp [Matrix.one_apply, h, one_mem]
  · simp [Matrix.one_apply, h, zero_mem]

theorem hatId_mul {𝔪 : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D 𝔪) {s : AE D}
    (hs : s ∈ OhE D) : s * x ∈ hatId D 𝔪 := by
  unfold hatId at hx ⊢
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha

noncomputable def part {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) : GA D N :=
  ⟨Units.map (phiHom he) (k : GL (Fin N) (AE D)), by
    rw [PtsMem.mem_GA]
    have hk := (PtsMem.mem_GA D (k : GL (Fin N) (AE D))).1 k.2
    show ((phi e (↑(k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).map (sgA D)).transpose *
      phi e (↑(k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = 1
    rw [phi_map, hse, phi_transpose, phi_mul he, hk, phi_one]⟩

theorem part_val {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) :
    (((part he hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      phi e ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem part_inv_val {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) :
    ((((part he hse k : GA D N) : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) :
      Matrix (Fin N) (Fin N) (AE D)) =
      phi e (((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem part_intG {e : AE D} (he : e * e = e) (hse : sgA D e = e) (heO : e ∈ OhE D) {k : GA D N}
    (hk : k ∈ intG D N) : part he hse k ∈ intG D N := by
  rw [mem_intG] at hk ⊢
  intro i j
  refine ⟨?_, ?_⟩
  · rw [part_val]; exact phi_mem_OhE heO (fun a b => (hk a b).1) i j
  · rw [part_inv_val]; exact phi_mem_OhE heO (fun a b => (hk a b).2) i j

theorem part_sub_one_apply {e : AE D} (he : e * e = e) (hse : sgA D e = e) (k : GA D N) (i j : Fin N) :
    (((part he hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j -
        (1 : Matrix (Fin N) (Fin N) (AE D)) i j =
      e * ((((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j) := by
  rw [← Matrix.sub_apply, part_val, phi_sub_one, Matrix.smul_apply, smul_eq_mul]

theorem exists_split_inert_factor : ∀ {D : D7} {N : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {k : GA D N},
    k ∈ intG D N → CongOne D 𝔪 k →
    ∃ ks ki : GA D N, k = ks * ki ∧ ks ∈ intG D N ∧ ki ∈ intG D N ∧ CongOne D 𝔪 ks ∧
      SuppSplit D (ks : GL (Fin N) (AE D)) ∧ SuppInert D (ki : GL (Fin N) (AE D)) := by
  intro D N 𝔪 k hk hc
  obtain ⟨ε, hεO, hεε, hεs, hq⟩ := VacMove.exists_half_idem D
  set e := ε + sgA D ε with he_def
  have heO : e ∈ OhE D := add_mem hεO (VacMove.sgA_mem D hεO)
  have hse : sgA D e = e := by rw [he_def, map_add (f := _), VacMove.sgA_sgA, add_comm]
  have hee : e * e = e := by
    have h2 : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, hεε]
    have h3 : sgA D ε * ε = 0 := by rw [mul_comm, hεs]
    rw [he_def, add_mul, mul_add, mul_add, hεε, hεs, h3, h2, zero_add, add_zero]
  have hfO : 1 - e ∈ OhE D := sub_mem (one_mem _) heO
  have hsf : sgA D (1 - e) = 1 - e := by rw [map_sub, map_one, hse]
  have hff : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  refine ⟨part hee hse k, part hff hsf k, ?_, part_intG hee hse heO hk, part_intG hff hsf hfO hk,
    ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Units.ext
    show ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      phi e ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        phi (1 - e) ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    rw [phi_mul_compl hee]
  · intro i j
    show ((((part hee hse k : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1) i j ∈ hatId D 𝔪
    rw [Matrix.sub_apply, part_sub_one_apply]
    exact hatId_mul (hc i j) heO
  · intro q hqp hin i j
    rw [part_sub_one_apply]
    exact VacMove.zeroAt_mul D hqp ((hq q hqp).1 hin) _
  · intro q hqp hin i j
    rw [part_sub_one_apply]
    exact VacMove.zeroAt_mul D hqp ((hq q hqp).2 hin) _

end GlobalTheory.CongSplitFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VlLeOfMemHatId
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.NuTrivSq
variable {D : D7}

open GlobalTheory.Mem.Col2.SplitChar in
theorem vl_le_of_mem_hatId' {I : Ideal (𝓞 D.host.E)} {PP : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (hI : I ≤ PP.asIdeal ^ n) {x : AE D} (hx : x ∈ hatId D I) : vl D PP x ≤ WithZero.exp (-(n : ℤ)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    rw [map_mul, vl_inc]
    refine (mul_le_of_le_one_right' (vl_le hs PP)).trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem PP b n).2 (hI hb)
  | zero => simp
  | add a b _ _ ha hb => exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  | neg a _ ha => rwa [Valuation.map_neg]


open GlobalTheory.Mem.Col2.SplitChar in
theorem sgA_mem_hatId' {I : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D I) :
    sgA D x ∈ hatId D (D.host.conj • I) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s,
      GlobalTheory.NormSum.UnramHecke.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.sgA_inc]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem conj_conj_smul (𝔪 : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
  have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z
  rw [smul_smul, h, one_smul]


open GlobalTheory.Mem.Col2.SplitChar in
theorem vl_sub_le' {T : Type} {L : LevCh D T} (P : Places L) {y : AE D}
    (h1 : y ∈ hatId D (condE P)) (h2 : y ∈ hatId D (D.host.conj • condE P))
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hv : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ P.S0) :
    vl D PP y ≤ WithZero.exp (-(condExp P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) : ℤ)) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  set v := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hvdef
  have hw : (P.w v).under (𝓞 D.host.F) = v := P.under_w hv
  have hle : condE P ≤ (P.w v).asIdeal ^ condExp P v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (P.w v) PP).1 (by rw [hw]) with e | h
  · rw [e]
    exact vl_le_of_mem_hatId' (e ▸ hle) h1
  · have e : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
    rw [e] at h
    rw [← GlobalTheory.NormSum.UnramHecke.sgA_sgA D y, vl_sgA h]
    have h3 := sgA_mem_hatId' h2
    rw [conj_conj_smul] at h3
    exact vl_le_of_mem_hatId' hle h3

end GlobalTheory.NuTrivSq


open GlobalTheory.Mem.Col2.SplitChar Formalism.L2.Host GlobalTheory.NuTrivSq in
theorem GlobalTheory.NuTrivSq.nuH_finIdl_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m) {μ₀ : T},
    L.Is μ₀ → ∀ x : (AE D)ˣ, IntU D x → (x : AE D) - 1 ∈ hatId D (condE G.pl) →
      (x : AE D) - 1 ∈ hatId D (D.host.conj • condE G.pl) →
      (nuH G μ₀ i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x) = 1 := by
  intro D T L sc G i j μ₀ hL u hu hc1 hc2
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j).2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  have hsub : Valued.v ((x : PP.adicCompletion D.host.E) - 1) = vl D PP ((u : AE D) - 1) := by
    rw [hx, vl_sub_one]
  have hμ : (L.C.mu0 j).loc PP x = 1 := by
    by_cases hg : ∃ k, OverP D.host (D.host.g k) PP
    · obtain ⟨k, hk⟩ := hg
      have hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0 := by
        refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
        have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
          change _ ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl this
        · exact Or.inr (Or.inl this)
      refine (L.C.isMu0 j).tame PP x hunit ?_
      rw [hsub]
      refine (vl_sub_le' G.pl hc1 hc2 hS).trans ?_
      have : 1 ≤ condExp G.pl ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by unfold condExp; split_ifs <;> omega
      exact WithZero.exp_le_exp.2 (by omega)
    · push_neg at hg
      exact (L.C.isMu0 j).unr PP hg x hunit
  have hχ : (G.ch.chiH (D.R.m - i)).loc PP x = 1 := by
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
    by_cases hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0
    · have hb := vl_sub_le' G.pl hc1 hc2 hS
      rw [← hsub] at hb
      rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1'
      · rw [condExp, if_pos h0] at hb
        exact (G.ch.lev0 _ h1 h2 PP h0).1 x hunit (by simpa using hb)
      · have hne : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ G.pl.v0 := fun e => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ h1')
        rw [condExp, if_neg hne] at hb
        exact (G.ch.lev1 _ h1 h2 PP h1').1 x hunit (by simpa using hb)
    · exact G.ch.unr _ h1 h2 PP hS x hunit
  show (nuH G μ₀ i j).loc PP x = 1
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv]
  change (L.C.mu0 j).loc PP x * ((G.ch.chiH (D.R.m - i)).loc PP x)⁻¹ = 1
  rw [hμ, hχ, inv_one, one_mul]

end
end

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.CosetFix

variable {D : D7}

theorem zeroAt_zero (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left _, 0, zero_mem _, by simp⟩

theorem trivAt_one {N : ℕ} (q : ℕ) : TrivAt D q ((1 : GA D N) : GL (Fin N) (AE D)) := fun i j => by
  simpa using zeroAt_zero (D := D) q


set_option maxHeartbeats 1000000 in
theorem fix_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d) {g' : GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) :
    H ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧ ∀ k : GA D P.a, P.W.Om k 1 P.e0 = P.e0 → P.W.Om k 1 H = H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have hHT : H ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
    have e : H = c⁻¹ • P.W.Om 1 g' P.e0 := by rw [hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hm : P.W.Om 1 g' P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := P.W.maps 1 g' P.e0 hT
    rw [e]
    exact NormUniq.tt_smul hm c⁻¹
  refine ⟨hHT, fun k he => ?_⟩
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : GA D P.a) = k := mul_one k
  have f2 : (1 : GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = P.W.Om 1 g' P.e0 := by rw [← e1, e2, he]
  rw [hc', P.W.smul _ _ _ _ hHT] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_facts (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 ∈
      TT D (tor0 D ⊤ δ) P.a P.d ∧
    ∀ k : GA D P.a, P.W.Om k 1 P.e0 = P.e0 →
      P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact fix_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem vac_fix_split (G : GridData L sc) (i j : Fin D.R.m) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) (hs : SuppSplit D (k : GL (Fin P.a) (AE D))) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨x, hxu, hxi, hx, h1, h2⟩ := GlobalTheory.FunObj.NormUniq.SplitDet.exists_splitComp_det hk hk' hs
  have hm : Moves D (k : GL (Fin P.a) (AE D)) (stdL D P.a) := by
    simpa using VacMove.moves_mul_int hk (VacMove.moves_one D P.a)
  have e := P.W.split k 1 x 1 (stdL D P.a) (stdL D P.d) hs (fun q _ _ => trivAt_one q)
    (fun q hq hi => ⟨hxi q hq hi, by simpa using zeroAt_zero (D := D) q⟩) hx (by simp) hm (VacMove.moves_one D P.d)
  have hc : P.W.chV'.f x ^ P.W.ep' = 1 := by
    rw [h.chars.2 x]
    show ((nuH G μ₀ i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x))⁻¹ = 1
    rw [GlobalTheory.NuTrivSq.nuH_finIdl_eq_one G i j hL x hxu h1 h2, inv_one]
  rw [e, map_one, one_zpow, hc, one_mul,
    show La D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d) = La0 D (tor0 D ⊤ δ) P.a P.d from rfl,
    VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) P.a P.d) P.vac.1]
  funext z
  simp

theorem vac_fix (G : GridData L sc) (i j : Fin D.R.m) (hI : Inp D) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨ks, ki, rfl, hs, hi, hs', hss, hii⟩ := GlobalTheory.CongSplitFactor.exists_split_inert_factor hk hk'
  have hT := VacMove.vac_TT hI.g1 P.crv P.vac.1
  have h1 : P.W.Om ki 1 P.e0 = P.e0 :=
    P.W.inert ki 1 ((mem_intG ki).1 hi) ((mem_intG 1).1 (one_mem _)) hii (fun q _ _ => trivAt_one q)
  have e := P.W.mul ks ki 1 1 P.e0 hT
  rw [mul_one] at e
  rw [e, h1, vac_fix_split G i j hL h hs hs' hss]

theorem cosetVec_fix (G : GridData L sc) (i j : Fin D.R.m) (hI : Inp D) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) : P.W.Om k 1 (cosetVec P (condE G.pl) 0) = cosetVec P (condE G.pl) 0 := by
  obtain ⟨hHT, hfix⟩ := iop_facts hI P (condE_ne_bot G.pl)
  have hH := hfix k (vac_fix G i j hI hL h hk hk')
  have hW := GlobalTheory.HeisFix.heis_fix hI P (condE_ne_bot G.pl) 0 hk hk' hHT hH
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ 0 P.a P.d) hHT
  unfold cosetVec
  rw [P.W.smul _ _ _ _ hWT, hW]

end GlobalTheory.FunObj.CosetFix
