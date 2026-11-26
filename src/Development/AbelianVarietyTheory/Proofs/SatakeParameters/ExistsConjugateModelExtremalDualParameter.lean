module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeOfIntegralGramMatrix
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGramClassRepsSelfDualLatticeGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntUnitaryOfGramClass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassTranslateSumMemSpanSelfDualLatticeVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateSumSelfDualLatticeFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateSumSelfDualLatticeFixed
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem vacuum_sum_selfDual_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a → ∀ Z : Finset (Matrix (Fin n') (Fin n) L),
    (∀ z ∈ Z, ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
      z = u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) →
    (∀ z ∈ Z, ∀ z' ∈ Z, z - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → z = z') →
    (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ z ∈ Z, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - z ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) →
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (∑ z ∈ Z, ρ z s) = ∑ z ∈ Z, ρ z s := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac a hSD Z hZform hZdist hZcov u hu
  classical
  obtain ⟨hU, hodd, hSint, hTint, -, -, hδ, hpsi, -, -, hρ, -, -, -⟩ := hP
  have hσσ := hU.1
  have hσv := hU.2.1
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hodd
  set A : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hA
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef

  have hloc : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      locH σ δ JS JT (w * A) (w' * A) ∈ Formalism.UG.intL L := by
    intro w w' hw hw'
    have hw'σ : ∀ i j, (w'.map σ)ᵀ i j ∈ Formalism.UG.intL L := by
      intro i j
      show Valued.v (σ (w' j i)) ≤ 1
      rw [hσv]; exact hw' j i
    have hJT : ∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L := fun i j => glint_entry hTint i j
    have hB : ∀ i j, (A * P * (A.map σ)ᵀ) i j ∈ Formalism.UG.intL L := hSD.2
    have hC : ∀ i j, ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) i j ∈ Formalism.UG.intL L :=
      matMul_int (matMul_int hw'σ hJT) hw
    have e : locH σ δ JS JT (w * A) (w' * A) =
        δ * Matrix.trace ((A * P * (A.map σ)ᵀ) * ((w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) := by
      unfold locH
      congr 1
      rw [Matrix.map_mul, Matrix.transpose_mul]
      calc Matrix.trace (P * ((A.map σ)ᵀ * (w'.map σ)ᵀ) * (JT : Matrix (Fin n') (Fin n') L) * (w * A))
          = Matrix.trace ((P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w) * A) := by
            simp only [Matrix.mul_assoc]
        _ = Matrix.trace (A * (P * (A.map σ)ᵀ * (w'.map σ)ᵀ * (JT : Matrix (Fin n') (Fin n') L) * w)) :=
            Matrix.trace_mul_comm _ _
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e]
    refine (Formalism.UG.intL L).mul_mem (le_of_eq hδ.1) ?_
    unfold Matrix.trace
    exact (Formalism.UG.intL L).sum_mem fun i _ => matMul_int hB hC i i

  have hpair : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      ψ ((locH σ δ JS JT (w * A) (w' * A) + σ (locH σ δ JS JT (w * A) (w' * A))) / 2) = 1 := by
    intro w w' hw hw'
    have hcI := hloc w w' hw hw'
    have hσc : σ (locH σ δ JS JT (w * A) (w' * A)) ∈ Formalism.UG.intL L := by
      show Valued.v (σ _) ≤ 1
      rw [hσv]; exact hcI
    apply hpsi
    · rw [GlobalTheory.Hk3.mem_intL_iff, map_div₀, h2, div_one]
      exact (Formalism.UG.intL L).add_mem hcI hσc
    · rw [map_div₀, map_add (f := _), hσσ, map_ofNat]; ring
  have hcomb : ∀ w w' : Matrix (Fin n') (Fin n) L, (∀ i j, w i j ∈ Formalism.UG.intL L) → (∀ i j, w' i j ∈ Formalism.UG.intL L) →
      ∀ t : M, ρ (w * A) (ρ (w' * A) t) = ρ (w * A + w' * A) t := by
    intro w w' hw hw' t
    have := congrArg (fun f => f t) (hρ (w * A) (w' * A))
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hpair w w' hw hw', one_smul]
  have key : ∀ z ∈ Z, ∃ z' ∈ Z, ρ (u * A) (ρ z s) = ρ z' s ∧ (u * A + z) - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := hZform z hz
    have huv : ∀ i j, (u + v) i j ∈ Formalism.UG.intL L := fun i j => (Formalism.UG.intL L).add_mem (hu i j) (hv i j)
    obtain ⟨z', hz', hdiff⟩ := hZcov (u + v) huv
    obtain ⟨v', hv', rfl⟩ := hZform z' hz'
    refine ⟨v' * A, hz', ?_, by rwa [← Matrix.add_mul]⟩
    have hw : ∀ i j, (u + v - v') i j ∈ Formalism.UG.intL L := fun i j => (Formalism.UG.intL L).sub_mem (huv i j) (hv' i j)
    have hl : ρ ((u + v - v') * A) s = s := by
      apply hvac
      rw [Matrix.sub_mul]
      exact hdiff
    rw [hcomb u v hu hv]
    calc ρ (u * A + v * A) s = ρ (v' * A + (u + v - v') * A) s := by
          congr 1; rw [Matrix.sub_mul, Matrix.add_mul]; abel
      _ = ρ (v' * A) (ρ ((u + v - v') * A) s) := (hcomb v' _ hv' hw s).symm
      _ = ρ (v' * A) s := by rw [hl]
  choose! f hfZ hf hfd using key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl hf]
  have hinj : ∀ x ∈ Z, ∀ y ∈ Z, f x = f y → x = y := by
    intro z1 h1 z2 h2 he
    apply hZdist z1 h1 z2 h2
    have := sub_mem (hfd z1 h1) (hfd z2 h2)
    rw [he] at this
    convert this using 1; abel
  have himg : Z.image f = Z := Finset.eq_of_subset_of_card_le
    (fun x hx => by obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx; exact hfZ z hz)
    (by rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)])
  rw [← Finset.sum_image (f := fun z => ρ z s) hinj, himg]

end GlobalTheory.Hk3.HoweG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateSumSelfDualLatticeFixedStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumTranslateSum_selfDualLattice_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M),
    GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a → ∀ Z : Finset (Matrix (Fin n') (Fin n) L),
    (∀ z ∈ Z, ∃ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
      z = u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) →
    (∀ z ∈ Z, ∀ z' ∈ Z, z - z' ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n → z = z') →
    (∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ∃ z ∈ Z, u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - z ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n) →
    ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
      ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) (∑ z ∈ Z, ρ z s) = ∑ z ∈ Z, ρ z s := by
  first | exact @GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed | exact GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed | (intros; apply GlobalTheory.Hk3.HoweG.vacuum_sum_selfDual_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassTranslateSumMemSpanSelfDualLatticeVacua
open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem sum_charSum_eq_card_filter {B ι M : Type} [AddCommGroup B] [Fintype B] [AddCommGroup M] [Module ℂ M]
    (Y : Finset ι) (x : ι) (hx : x ∈ Y) (χ : B → ι → ℂ)
    (hmul : ∀ b b', ∀ y ∈ Y, χ (b + b') y = χ b y * χ b' y) (hne : ∀ b, ∀ y ∈ Y, χ b y ≠ 0) (v : ι → M)
    [DecidablePred (fun y => ∀ b, χ b y = χ b x)] :
    ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • v y =
      (Fintype.card B : ℂ) • ∑ y ∈ Y.filter (fun y => ∀ b, χ b y = χ b x), v y := by
  have h0 : ∀ y ∈ Y, χ 0 y = 1 := by
    intro y hy
    have e := hmul 0 0 y hy
    rw [add_zero] at e
    exact mul_left_cancel₀ (hne 0 y hy) (by rw [mul_one]; exact e.symm)
  have key : ∀ y ∈ Y, ∑ b, (χ b x)⁻¹ * χ b y =
      if (∀ b, χ b y = χ b x) then (Fintype.card B : ℂ) else 0 := by
    intro y hy
    split_ifs with hP
    · simp [hP, inv_mul_cancel₀ (hne _ x hx)]
    · let φ : AddChar B ℂ :=
        { toFun := fun b => (χ b x)⁻¹ * χ b y
          map_zero_eq_one' := by simp [h0 x hx, h0 y hy]
          map_add_eq_mul' := by
            intro b b'
            show (χ (b + b') x)⁻¹ * χ (b + b') y = ((χ b x)⁻¹ * χ b y) * ((χ b' x)⁻¹ * χ b' y)
            rw [hmul b b' x hx, hmul b b' y hy, mul_inv]
            ring }
      have hφ : φ ≠ 1 := by
        intro h1
        apply hP
        intro b
        have e : φ b = 1 := by rw [h1, AddChar.one_apply]
        exact ((inv_mul_eq_one₀ (hne b x hx)).mp e).symm
      show ∑ b, φ b = 0
      exact AddChar.sum_eq_zero_of_ne_one hφ
  calc ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • v y = ∑ y ∈ Y, (∑ b, (χ b x)⁻¹ * χ b y) • v y := by
        simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]; exact Finset.sum_comm
    _ = ∑ y ∈ Y, (if (∀ b, χ b y = χ b x) then (Fintype.card B : ℂ) else 0) • v y :=
        Finset.sum_congr rfl (fun y hy => by rw [key y hy])
    _ = _ := by
        rw [Finset.smul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        split_ifs <;> simp

end GlobalTheory.Hk3.HoweG

namespace GlobalTheory.Hk3.HoweG

open GlobalTheory.Hk3

theorem gramClass_sum_mem_span_selfDual_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ C : Finset (Matrix (Fin n') (Fin n) L), ∃ c : Matrix (Fin n') (Fin n) L → ℂ, x ∈ C ∧
      (∀ y ∈ C, c y ≠ 0 ∧ GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ∧ GlobalTheory.Hk3.HoweG.GramEq σ JT x y) ∧
      (∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → y - y' ∉ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
      ∑ y ∈ C, c y • ρ y s ∈ Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac x hx
  classical
  have hP' := hP
  obtain ⟨hU, hodd, hSint, hTint, hS, hT, hδ, hpsi_int, hpsi_ne, -, hρ, -, -, -⟩ := hP'
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.selfDual_lattice_of_integral_gramMatrix L ϖ σ q n n' JS JT hU hodd hSint hTint hS hT x hx
  obtain ⟨Y, hxY, hYA, hYd, B, _, _, b0, l, hb0, hl, hcov, hmul, hsep⟩ :=
    GlobalTheory.T.exists_gramClass_reps_selfDualLattice_group L ϖ σ q δ n n' JS JT ψ hU hodd hSint hTint hS hT hδ hpsi_int hpsi_ne x hx a ⟨ha1, ha2, ha3, ha4⟩
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hshift : ∀ y u, u ∈ HoweDuality.intMat L n' n →
      ρ (y + u) s = ψ (-((locH σ δ JS JT y u + σ (locH σ δ JS JT y u)) / 2)) • ρ y s := by
    intro y u hu
    have h1 : ρ y s = ψ ((locH σ δ JS JT y u + σ (locH σ δ JS JT y u)) / 2) • ρ (y + u) s := by
      have := congrArg (fun f => f s) (hρ y u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  set χ : B → Matrix (Fin n') (Fin n) L → ℂ :=
    fun b y => ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) with hχ
  have hne : ∀ b, ∀ y ∈ Y, χ b y ≠ 0 := by
    intro b y _ h0
    have := hψinv (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2))
    rw [show ψ (-((locH σ δ JS JT y (l b y) + σ (locH σ δ JS JT y (l b y))) / 2)) = χ b y from rfl, h0,
      zero_mul] at this
    exact zero_ne_one this
  set Spn := Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) →
          ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} with hSpn

  have hvacb : ∀ b, ∑ y ∈ Y, χ b y • ρ y s ∈ Spn := by
    intro b
    have hinj : Set.InjOn (fun y => y + l b y) Y := by
      intro y hy y' hy' e
      refine hYd y hy y' hy' ?_
      have e' : y - y' = l b y' - l b y := by
        have := congrArg (fun z => z - l b y - y') e
        simp only at this
        rw [show y + l b y - l b y - y' = y - y' by abel, show y' + l b y' - l b y - y' = l b y' - l b y by abel] at this
        exact this
      rw [e']
      exact (HoweDuality.intMat L n' n).sub_mem (hl b y' hy').1 (hl b y hy).1
    have hsum : ∑ y ∈ Y, χ b y • ρ y s = ∑ z ∈ Y.image (fun y => y + l b y), ρ z s := by
      rw [Finset.sum_image hinj]
      exact Finset.sum_congr rfl (fun y hy => (hshift y (l b y) (hl b y hy).1).symm)
    rw [hsum]
    refine Submodule.subset_span ⟨b0 b, hb0 b, ?_⟩
    refine GlobalTheory.T.vacuumTranslateSum_selfDualLattice_fixed L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac (b0 b) (hb0 b) _ ?_ ?_ ?_
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact (hl b y hy).2
    · intro z hz z' hz' hzz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hz'
      have : y = y' := by
        refine hYd y hy y' hy' ?_
        have e : y - y' = (y + l b y - (y' + l b y')) + (l b y' - l b y) := by abel
        rw [e]
        exact (HoweDuality.intMat L n' n).add_mem hzz
          ((HoweDuality.intMat L n' n).sub_mem (hl b y' hy').1 (hl b y hy).1)
      rw [this]
    · intro u hu
      obtain ⟨y, hy, hm⟩ := hcov b u hu
      exact ⟨y + l b y, Finset.mem_image_of_mem _ hy, hm⟩
  have hF := sum_charSum_eq_card_filter Y x hxY χ hmul hne (fun y => ρ y s)
  have hcard : (Fintype.card B : ℂ) ≠ 0 := by
    have : 0 < Fintype.card B := Fintype.card_pos
    exact_mod_cast this.ne'
  refine ⟨Y.filter (fun y => ∀ b, χ b y = χ b x), fun _ => 1, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hxY, fun _ => rfl⟩
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    exact ⟨one_ne_zero, hYA y hy1, (hsep y hy1).mpr hy2⟩
  · intro y hy y' hy' hne' hm
    exact hne' (hYd y (Finset.mem_filter.mp hy).1 y' (Finset.mem_filter.mp hy').1 hm)
  · simp only [one_smul]
    have e : ∑ y ∈ Y.filter (fun y => ∀ b, χ b y = χ b x), ρ y s =
        (Fintype.card B : ℂ)⁻¹ • ∑ b, (χ b x)⁻¹ • ∑ y ∈ Y, χ b y • ρ y s := by
      rw [hF, smul_smul, inv_mul_cancel₀ hcard, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hvacb b))

end GlobalTheory.Hk3.HoweG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GramClassTranslateSumMemSpanSelfDualLatticeVacuaStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_class_translate_sum_mem_span_selfDual_lattice_vacua : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ C : Finset (Matrix (Fin n') (Fin n) L), ∃ c : Matrix (Fin n') (Fin n) L → ℂ, x ∈ C ∧
      (∀ y ∈ C, c y ≠ 0 ∧ GlobalTheory.Hk3.HoweG.HomA σ JS JT x y ∧ GlobalTheory.Hk3.HoweG.GramEq σ JT x y) ∧
      (∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → y - y' ∉ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ∧
      ∑ y ∈ C, c y • ρ y s ∈ Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} := by
  first | exact @GlobalTheory.Hk3.HoweG.gramClass_sum_mem_span_selfDual_vac | exact GlobalTheory.Hk3.HoweG.gramClass_sum_mem_span_selfDual_vac | (intros; apply GlobalTheory.Hk3.HoweG.gramClass_sum_mem_span_selfDual_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLatticeVacuumMemSpanFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLatticeVacuumMemSpanFixed
open Matrix

namespace GlobalTheory.Hk3

theorem locVac_mem_span_vac : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ w : M, GlobalTheory.Hk3.LocVac ρ w → w ∈ Submodule.span ℂ {s} := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac hspan w hw
  classical
  have hind := locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) s = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x s := by
    intro x u hu
    have h1 : ρ x s = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) s := by
      have := congrArg (fun f => f s) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [hvac u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x s) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x s := by
    intro x u hu
    have := congrArg (fun f => f s) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  set Λ := HoweDuality.intMat L n' n with hΛdef
  set V : Matrix (Fin n') (Fin n) L ⧸ Λ → Submodule ℂ M := fun c => Submodule.span ℂ {ρ c.out s} with hVdef
  have hVind : iSupIndep V := by
    refine hind.mono fun c => Submodule.span_le.mpr ?_
    rintro _ rfl
    exact Submodule.subset_span ⟨c.out, QuotientAddGroup.out_eq' c, rfl⟩
  have hmemV : ∀ x, ρ x s ∈ V (QuotientAddGroup.mk x) := by
    intro x
    have hm : -(QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq'])
    have := hshift (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ).out _ hm
    rw [add_neg_cancel_left] at this
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hwV : w ∈ ⨆ c, V c := by
    have hle : Submodule.span ℂ (Set.range fun x => ρ x s) ≤ ⨆ c, V c :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact Submodule.mem_iSup_of_mem _ (hmemV x))
    exact hle (hspan ▸ Submodule.mem_top)
  obtain ⟨f, hf, hfw⟩ := (Submodule.mem_iSup_iff_exists_finsupp V w).mp hwV
  set χ : Matrix (Fin n') (Fin n) L ⧸ Λ → Matrix (Fin n') (Fin n) L → ℂ :=
    fun c u => ψ (locH σ δ JS JT u c.out + σ (locH σ δ JS JT u c.out)) with hχ
  have heigV : ∀ c, ∀ u ∈ intMatSub (L := L) n n', ∀ v ∈ V c, ρ u v = χ c u • v := by
    intro c u hu v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, heig _ u hu, smul_comm]
  have hzero : ∀ c, c ≠ 0 → f c = 0 := by
    intro c hc
    obtain ⟨u, hu, hχu⟩ : ∃ u ∈ intMatSub (L := L) n n', χ c u ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hint := intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne c.out hcon
      apply hc
      rw [hΛ] at hint
      rw [← QuotientAddGroup.out_eq' c, QuotientAddGroup.eq_zero_iff]
      exact hint
    have hsum : (f.support.sum fun d => (χ d u - 1) • f d) = 0 := by
      have e1 : ρ u w = f.support.sum fun d => χ d u • f d := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hfw, Finsupp.sum, map_sum]
        exact Finset.sum_congr rfl fun d _ => heigV d u hu _ (hf d)
      have e2 : w = f.support.sum fun d => f d := by rw [← hfw, Finsupp.sum]
      simp only [sub_smul, one_smul, Finset.sum_sub_distrib, ← e1, ← e2, hw u hu, sub_self]
    by_cases hcs : c ∈ f.support
    · rw [← Finset.add_sum_erase _ _ hcs, add_eq_zero_iff_eq_neg] at hsum
      have hmem1 : (χ c u - 1) • f c ∈ V c := Submodule.smul_mem _ _ (hf c)
      have hmem2 : (χ c u - 1) • f c ∈ ⨆ (j) (_ : j ≠ c), V j := by
        rw [hsum]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd => ?_)
        have hdc : d ≠ c := Finset.ne_of_mem_erase hd
        exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hdc (Submodule.smul_mem _ _ (hf d)))
      have hz : (χ c u - 1) • f c = 0 := by
        have := (iSupIndep_def.mp hVind c)
        rw [Submodule.disjoint_def] at this
        exact this _ hmem1 hmem2
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hχu)
    · exact Finsupp.notMem_support_iff.mp hcs
  have hw0 : w = f 0 := by
    rw [← hfw, Finsupp.sum, Finset.sum_eq_single (0 : Matrix (Fin n') (Fin n) L ⧸ Λ)]
    · intro d _ hd; exact hzero d hd
    · intro h0; exact Finsupp.notMem_support_iff.mp h0
  have hout : ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s = s := by
    apply hvac
    have : (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out ∈ Λ := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
    exact this
  have := hf 0
  change f 0 ∈ Submodule.span ℂ {ρ (0 : Matrix (Fin n') (Fin n) L ⧸ Λ).out s} at this
  rw [hout] at this
  rw [hw0]; exact this

end GlobalTheory.Hk3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLatticeVacuumMemSpanFixedStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLatticeVacuum_mem_span_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ w : M, GlobalTheory.Hk3.LocVac ρ w → w ∈ Submodule.span ℂ {s} := by
  first | exact @GlobalTheory.Hk3.locVac_mem_span_vac | exact GlobalTheory.Hk3.locVac_mem_span_vac | (intros; apply GlobalTheory.Hk3.locVac_mem_span_vac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeEqUnitaryMulIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeEqUnitaryMulIntegralGL
noncomputable section

open Matrix

namespace GlobalTheory.Hk3.HoweG

theorem mem_GLint_of_entries' {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

def cTGL {L : Type} [Field L] (σ : L →+* L) {n : ℕ} (a : GL (Fin n) L) : GL (Fin n) L :=
  ⟨Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L), Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    by rw [← Formalism.UG.cT_mul, Units.inv_mul, Formalism.UG.cT_one],
    by rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]⟩

theorem selfDual_eq_unitary_mul_int : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (JS : GL (Fin n) L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
      ∃ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), ∃ k : GL (Fin n) L, k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        a = (g : GL (Fin n) L) * k := by
  intro L _ _ _ ϖ σ q n JS hU _hq hJS hJh a ha
  have hσ : ∀ x, σ (σ x) = x := hU.1
  have cTcT : ∀ M : Matrix (Fin n) (Fin n) L, Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
    intro M; ext i j; simp [Formalism.UG.cT, hσ]
  have hJc : Formalism.UG.cT σ (JS : Matrix (Fin n) (Fin n) L) = JS := by
    ext i j; simp [Formalism.UG.cT, hJh]
  set G : GL (Fin n) L := cTGL σ a * JS * a with hGdef
  have hGv : (G : Matrix (Fin n) (Fin n) L) =
      Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L) := rfl
  have hGi : ((G⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hGdef, _root_.mul_inv_rev, _root_.mul_inv_rev, ← _root_.mul_assoc]; rfl
  have hGint : G ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) :=
    mem_GLint_of_entries' _ G (fun i j => by rw [hGv]; exact ha.1 i j) (fun i j => by rw [hGi]; exact ha.2 i j)
  have hGc : Formalism.UG.cT σ (G : Matrix (Fin n) (Fin n) L) = G := by
    rw [hGv, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTcT, hJc, Matrix.mul_assoc]
  have hGh : ∀ i j, σ ((G : Matrix (Fin n) (Fin n) L) i j) = (G : Matrix (Fin n) (Fin n) L) j i := by
    intro i j
    have := congrFun (congrFun hGc j) i
    simpa [Formalism.UG.cT] using this
  obtain ⟨P, hP, eP⟩ := GlobalTheory.NormalHyp.frame hU hGint hGh
  obtain ⟨Q, hQ, eQ⟩ := GlobalTheory.NormalHyp.frame hU hJS hJh
  have hU' : a * P * Q⁻¹ ∈ Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) := by
    show Formalism.UG.cT σ ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) *
      ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = JS
    have e1 : Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Formalism.UG.cT_mul, Units.mul_inv, Formalism.UG.cT_one]
    have e2 : (Q : Matrix (Fin n) (Fin n) L) * ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv Q
    rw [hGv] at eP
    calc Formalism.UG.cT σ ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) *
          ((a * P * Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
        = Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (Formalism.UG.cT σ (P : Matrix (Fin n) (Fin n) L) * (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) *
              (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) * (P : Matrix (Fin n) (Fin n) L)) *
            ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          simp only [Units.val_mul, Formalism.UG.cT_mul, Matrix.mul_assoc]
      _ = Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (Q : Matrix (Fin n) (Fin n) L)) *
            ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by rw [eP, eQ]
      _ = (Formalism.UG.cT σ ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ (Q : Matrix (Fin n) (Fin n) L)) *
            (JS : Matrix (Fin n) (Fin n) L) * ((Q : Matrix (Fin n) (Fin n) L) * ((Q⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
          simp only [Matrix.mul_assoc]
      _ = JS := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨a * P * Q⁻¹, hU'⟩, Q * P⁻¹, mul_mem hQ (inv_mem hP), ?_⟩
  show a = a * P * Q⁻¹ * (Q * P⁻¹)
  group

end GlobalTheory.Hk3.HoweG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualLatticeEqUnitaryMulIntegralGLStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_eq_unitary_mul_integralGL : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ) (JS : GL (Fin n) L),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    ∀ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
      ∃ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), ∃ k : GL (Fin n) L, k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        a = (g : GL (Fin n) L) * k := by
  first | exact @GlobalTheory.Hk3.HoweG.selfDual_eq_unitary_mul_int | exact GlobalTheory.Hk3.HoweG.selfDual_eq_unitary_mul_int | (intros; apply GlobalTheory.Hk3.HoweG.selfDual_eq_unitary_mul_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjugateModelExtremalDualParameter
noncomputable section

namespace GlobalTheory.Hk3.HoweG

theorem gramClass_orbit_mod_lower : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweDuality.latIdx y < GlobalTheory.Hk3.HoweDuality.latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs hvac hspan x hx
  classical
  obtain ⟨C, c, hxC, hC, hpw, hsum⟩ := GlobalTheory.T.gram_class_translate_sum_mem_span_selfDual_lattice_vacua L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac x hx
  have hψ0 : ∀ e : L, ψ e ≠ 0 := fun e h => by
    have h2 : ψ e * ψ (-e) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [h, zero_mul] at h2; exact zero_ne_one h2
  have hint_mul : ∀ (u : Matrix (Fin n') (Fin n) L) (k : GL (Fin n) L), (∀ i j, u i j ∈ Formalism.UG.intL L) →
      k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ∀ i j, (u * (k : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L := by
    intro u k hu hk i j
    obtain ⟨k0, rfl⟩ := hk
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hu i l) ((k0 : Matrix (Fin n) (Fin n) (Formalism.UG.intL L)) l j).2

  have hvacSS : Submodule.span ℂ {w : M | ∃ a : GL (Fin n) L, GlobalTheory.Hk3.HoweG.SelfDual σ JS a ∧
        ∀ u : Matrix (Fin n') (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → ρ (u * ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w} ≤
      Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s) := by
    rw [Submodule.span_le]
    rintro w ⟨a, ha, hw⟩
    obtain ⟨g, k, hk, hak⟩ := GlobalTheory.T.selfDual_lattice_eq_unitary_mul_integralGL L ϖ σ q n JS hP.unr hP.odd hP.intS hP.hermS a ha
    have hw' : GlobalTheory.Hk3.LocVac ρ (ω (g⁻¹, 1) w) := by
      intro u hu
      have h1 := hP.norm g⁻¹ 1 (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))
      have h2 : ρ (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) w = w := by
        have := hw (u * (k : Matrix (Fin n) (Fin n) L)) (hint_mul u k hu hk)
        rw [hak] at this
        simpa [Matrix.mul_assoc, mul_inv_rev] using this
      have h3 := congrArg (fun F : Module.End ℂ M => F w) h1
      simp only [Module.End.mul_apply, h2] at h3
      have e : (((1 : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L)) : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) *
          (u * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
          ((((g⁻¹ : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L)) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = u := by
        rw [Subgroup.coe_inv, inv_inv, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.mul_assoc, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [e] at h3
      exact h3.symm
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (GlobalTheory.T.localLatticeVacuum_mem_span_fixed L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac hspan _ hw')
    have hww : w = t • ω (g, 1) s := by
      have e1 : ω (g, 1) (ω (g⁻¹, 1) w) = w := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one, Prod.mk_one_one, map_one,
          Module.End.one_apply]
      rw [← e1, ← ht, map_smul]
    rw [SetLike.mem_coe, hww]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  refine ⟨∑ y ∈ C, c y • ρ y s, hvacSS hsum,
    ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y ≠ GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, ?_, rfl⟩)
    obtain ⟨hyC, hne⟩ := Finset.mem_filter.1 hy
    exact lt_of_le_of_ne (GlobalTheory.T.matrixLatticeIndex_le_of_integral_kernel L ϖ σ q n' n x y hP.unr (hC y hyC).2.1.1) hne
  have hsplit : ∑ y ∈ C, c y • ρ y s - ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y ≠ GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s =
      ∑ y ∈ C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x), c y • ρ y s := by
    rw [← Finset.sum_filter_add_sum_filter_not C (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x)]
    exact add_sub_cancel_right _ _
  rw [hsplit]

  have hshift : ∀ y y' : Matrix (Fin n') (Fin n) L, (∀ i j, (y - y') i j ∈ Formalism.UG.intL L) → ∃ ζ : ℂ, ζ ≠ 0 ∧ ρ y' s = ζ • ρ y s := by
    intro y y' hl
    refine ⟨ψ ((GlobalTheory.Hk3.locH σ δ JS JT y' (y - y') + σ (GlobalTheory.Hk3.locH σ δ JS JT y' (y - y'))) / 2), hψ0 _, ?_⟩
    have h1 := congrArg (fun F : Module.End ℂ M => F s) (hP.rho_mul y' (y - y'))
    simp only [Module.End.mul_apply, hvac _ hl, LinearMap.smul_apply, add_sub_cancel] at h1
    exact h1
  refine ⟨Submodule.sum_mem _ fun y hy => ?_, ?_⟩
  · obtain ⟨hyC, heq⟩ := Finset.mem_filter.1 hy
    obtain ⟨h, hh, hyl⟩ := GlobalTheory.T.exists_intUnitary_of_gramClass_alt L ϖ σ q n n' JS JT hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT x y hx (hC y hyC).2.1 (hC y hyC).2.2 heq
    obtain ⟨ζ, hζ, hζe⟩ := hshift y (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) hyl
    have : ρ y s = ζ⁻¹ • ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s := by
      rw [hζe, smul_smul, inv_mul_cancel₀ hζ, one_smul]
    rw [this, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, hh, rfl⟩)
  ·
    have hI := GlobalTheory.Hk3.locVac_span_classes_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hvac
    set P := C.filter (fun y => GlobalTheory.Hk3.HoweDuality.latIdx y = GlobalTheory.Hk3.HoweDuality.latIdx x) with hPdef
    have hxP : x ∈ P := Finset.mem_filter.2 ⟨hxC, rfl⟩
    set F := fun cl : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = cl ∧ w = ρ x s} with hF
    have hmem : ∀ y : Matrix (Fin n') (Fin n) L, ∀ t : ℂ, t • ρ y s ∈ F (QuotientAddGroup.mk y) :=
      fun y t => Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl, rfl⟩)
    have hrest : ∑ y ∈ P.erase x, c y • ρ y s ∈ ⨆ (j) (_ : j ≠ (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n)), F j := by
      refine Submodule.sum_mem _ fun y hy => ?_
      have hyx : y ≠ x := Finset.ne_of_mem_erase hy
      have hyC : y ∈ C := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hy)).1
      have hne : (QuotientAddGroup.mk y : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) ≠ QuotientAddGroup.mk x := by
        intro he
        apply hpw y hyC x hxC hyx
        have := (QuotientAddGroup.eq).1 he.symm
        have h2 : y - x = -x + y := by abel
        rw [h2]; exact this
      exact (le_iSup₂_of_le (QuotientAddGroup.mk y) hne le_rfl : F (QuotientAddGroup.mk y) ≤ _) (hmem y (c y))
    intro h0
    rw [← Finset.add_sum_erase P _ hxP] at h0
    have hxx : c x • ρ x s = 0 := by
      have hd := (hI (QuotientAddGroup.mk x))
      rw [Submodule.disjoint_def] at hd
      apply hd _ (hmem x (c x))
      have : c x • ρ x s = -(∑ y ∈ P.erase x, c y • ρ y s) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact neg_mem hrest
    have hcx := (hC x hxC).1
    rw [smul_eq_zero] at hxx
    rcases hxx with h | h
    · exact hcx h
    · apply hs
      have h1 := congrArg (fun F : Module.End ℂ M => F s) (hP.rho_mul (-x) x)
      simp only [Module.End.mul_apply, h, map_zero, neg_add_cancel, hP.rho_zero, LinearMap.smul_apply, Module.End.one_apply] at h1
      exact (smul_eq_zero.1 h1.symm).resolve_left (hψ0 _)

end GlobalTheory.Hk3.HoweG

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjugateModelExtremalDualParameterStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugateModel_extremal_dual_parameter : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∃ v ∈ Submodule.span ℂ (Set.range fun g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) => ω (g, 1) s),
      ∃ u ∈ Submodule.span ℂ {v : M | ∃ y : Matrix (Fin n') (Fin n) L, GlobalTheory.Hk3.HoweDuality.latIdx y < GlobalTheory.Hk3.HoweDuality.latIdx x ∧ v = ρ y s},
        v - u ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s} ∧ v - u ≠ 0 := by
  first | exact @GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower | exact GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower | (intros; apply GlobalTheory.Hk3.HoweG.gramClass_orbit_mod_lower <;> assumption)
end
