module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutChainCosetSumScalingOfUnimodularit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutChainCosetSumScalingOfUnimodularit
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem finsum_out_inv_congr {A : Type} [Group A] (U V : Subgroup A) (e : MulAut A) (f : A → ℂ)
    (he : ∀ a, a ∈ U ↔ e a ∈ V) (hV : ∀ v ∈ V, ∀ a, f (v * a) = f a) :
    ∑ᶠ y : A ⧸ U, f (e y.out)⁻¹ = ∑ᶠ y : A ⧸ V, f y.out⁻¹ := by
  let E : A ⧸ U ≃ A ⧸ V := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, he, map_mul, map_inv]
    rfl)
  have hE : ∀ a : A, E (QuotientGroup.mk a) = QuotientGroup.mk (e a) := fun a => rfl
  rw [← finsum_comp_equiv E]
  refine finsum_congr fun y => ?_
  have h1 : E y = QuotientGroup.mk (e y.out) := by
    rw [← hE, QuotientGroup.out_eq']
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V (e y.out)
  rw [h1, hv, mul_inv_rev, hV _ (V.inv_mem v.2)]

theorem chainSum_of_unimod : Unimod → ChainIndex → ChainSum := by
  classical
  intro hUn hCh A _ U c Q d f hc hQ hind hex hV hU hfin
  have hchain := hCh A U c Q hc hind
  have hmem : ∀ (j : ℤ) (a : A), a ∈ U.comap (c ^ j).toMonoidHom ↔ (c ^ j) a ∈ U := fun j a => Iff.rfl
  have hmono : ∀ j j' : ℤ, j ≤ j' → U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ j').toMonoidHom := by
    intro j j' h
    have := (hchain j (j' - j).toNat).1
    rwa [show j + ((j' - j).toNat : ℤ) = j' by omega] at this
  have h0 : U.comap (c ^ (0 : ℤ)).toMonoidHom = U := by
    ext a
    rw [hmem, zpow_zero, MulAut.one_apply]
  choose J hJ using hex
  obtain ⟨k, hkd, hk⟩ : ∃ k : ℕ, d ≤ k ∧ ∀ y : A ⧸ U, f y.out ≠ 0 → J y.out ≤ k := by
    refine ⟨hfin.toFinset.sup (fun y => J y.out) + d.toNat, by omega, fun y hy => ?_⟩
    exact le_trans (Finset.le_sup (f := fun y : A ⧸ U => J y.out) (hfin.mem_toFinset.2 hy)) (Nat.le_add_right _ _)
  obtain ⟨l, hl⟩ : ∃ l : ℕ, d + l = k := ⟨(k - d).toNat, by omega⟩
  have hUΓ : U ≤ U.comap (c ^ (k : ℤ)).toMonoidHom := by
    have := hmono 0 k (by omega)
    rwa [h0] at this
  have iU : U.relIndex (U.comap (c ^ (k : ℤ)).toMonoidHom) = Q ^ k := by
    have := (hchain 0 k).2
    rwa [h0, zero_add] at this
  have iV : (U.comap (c ^ d).toMonoidHom).relIndex (U.comap (c ^ (k : ℤ)).toMonoidHom) = Q ^ l := by
    have := (hchain d l).2
    rwa [hl] at this
  have hsupp : ∀ a, f a ≠ 0 → a ∈ U.comap (c ^ (k : ℤ)).toMonoidHom := by
    intro a ha
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U a
    have h1 : f (QuotientGroup.mk a : A ⧸ U).out ≠ 0 := by rwa [hu, hU _ u.2]
    have h2 : (QuotientGroup.mk a : A ⧸ U).out ∈ U.comap (c ^ (k : ℤ)).toMonoidHom := by
      refine hmono (J (QuotientGroup.mk a : A ⧸ U).out : ℕ) k (by exact_mod_cast hk _ h1) ?_
      rw [hmem, zpow_natCast]
      exact hJ _
    rw [hu] at h2
    exact (Subgroup.mul_mem_cancel_right _ (hUΓ u.2)).1 h2
  have key := hUn A _ U (U.comap (c ^ d).toMonoidHom) f hUΓ (hmono d k hkd)
    (by rw [iU]; exact pow_ne_zero _ hQ) (by rw [iV]; exact pow_ne_zero _ hQ) hsupp
    (fun v hv => hV v hv) hU
  rw [finsum_out_inv_congr U (U.comap (c ^ d).toMonoidHom) (c ^ (-d)) f (fun a => by
    rw [hmem, ← MulAut.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, MulAut.one_apply])
    (fun v hv => hV v hv)]
  rw [iU, iV] at key
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
  have hpow : (Q : ℂ) ^ l = (Q : ℂ) ^ k * (Q : ℂ) ^ (-d) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hQ']
    congr 1
    omega
  push_cast at key
  rw [hpow, mul_assoc] at key
  exact mul_left_cancel₀ (pow_ne_zero _ hQ') key

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutChainCosetSumScalingOfUnimodularitStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity : GlobalTheory.SatakeWeyl.Unimod → GlobalTheory.SatakeWeyl.ChainIndex → GlobalTheory.SatakeWeyl.ChainSum := by
  first | exact @GlobalTheory.SatakeWeyl.chainSum_of_unimod | exact GlobalTheory.SatakeWeyl.chainSum_of_unimod | (intros; apply GlobalTheory.SatakeWeyl.chainSum_of_unimod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumTwoStageDescentUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumTwoStageDescentUnipotent
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl


open Classical in
theorem finsum_partition {X Y : Type} (f : X → ℂ) (Q : X → Prop) (R : Y → X → Prop)
    (hf : (Function.support f).Finite) (hQ : ∀ x, Q x ↔ ∃ y, R y x)
    (hu : ∀ x y y', R y x → R y' x → y = y') :
    (Function.support fun y => ∑ᶠ x, if R y x then f x else 0).Finite ∧
      (∑ᶠ x, if Q x then f x else 0) = ∑ᶠ y, ∑ᶠ x, if R y x then f x else 0 := by
  have hS : ∀ (T : X → Prop) [DecidablePred T],
      (∑ᶠ x, if T x then f x else 0) = ∑ x ∈ hf.toFinset, if T x then f x else 0 := by
    intro T _
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    exact hx (by simp [h0])
  have hfin : ∀ x, (Function.support fun y => if R y x then f x else 0).Finite := by
    intro x
    refine Set.Subsingleton.finite fun y hy y' hy' => hu x y y' ?_ ?_
    · by_contra h; exact hy (by simp [h])
    · by_contra h; exact hy' (by simp [h])
  simp only [hS]
  constructor
  · refine (hf.biUnion fun x _ => hfin x).subset fun y hy => ?_
    obtain ⟨x, hx, hx'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    exact Set.mem_biUnion (hf.mem_toFinset.1 hx) hx'
  · rw [finsum_sum_comm _ _ fun x _ => hfin x]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Q x
    · obtain ⟨y, hy⟩ := (hQ x).1 hx
      rw [finsum_eq_single _ y, if_pos hx, if_pos hy]
      intro y' hy'
      exact if_neg fun h => hy' (hu x y' y h hy)
    · rw [if_neg hx]
      symm
      exact finsum_eq_zero_of_forall_eq_zero fun y => if_neg fun h => hx ((hQ x).2 ⟨y, h⟩)

theorem descent : GlobalTheory.SatakeWeyl.Descent := by
  intro G A _ _ K N N' ι h g hf hle hN hdec hK hconj
  have key := finsum_partition (fun x : G ⧸ K => h x.out)
    (fun x => ∃ u ∈ N, ∃ k ∈ K, x.out = g * u * k)
    (fun (y : A ⧸ K.comap ι) x => ∃ u ∈ N', ∃ k ∈ K, x.out = g * ι y.out * u * k) hf ?_ ?_
  · unfold cellSum
    convert key
  · intro x
    constructor
    · rintro ⟨u, hu, k, hk, e⟩
      obtain ⟨a, u', hu', rfl⟩ := hdec u hu
      obtain ⟨⟨u₀, hu₀⟩, e₀⟩ := QuotientGroup.mk_out_eq_mul (K.comap ι) a
      refine ⟨QuotientGroup.mk a, ι u₀⁻¹ * u' * (ι u₀⁻¹)⁻¹, hconj _ _ hu', ι u₀⁻¹ * k,
        K.mul_mem (by rw [map_inv]; exact K.inv_mem hu₀) hk, ?_⟩
      rw [e, e₀]
      simp only [map_mul, map_inv]
      group
    · rintro ⟨y, u, hu, k, hk, e⟩
      exact ⟨ι y.out * u, N.mul_mem (hN _) (hle hu), k, hk, by rw [e]; group⟩
  · rintro x y y' ⟨u₁, hu₁, k₁, hk₁, e₁⟩ ⟨u₂, hu₂, k₂, hk₂, e₂⟩
    have e : ι y.out * u₁ * k₁ = ι y'.out * u₂ * k₂ := by
      apply mul_left_cancel (a := g)
      have := e₁.symm.trans e₂
      simpa only [mul_assoc] using this
    set b := y'.out⁻¹ * y.out with hb
    have hb' : ι b ∈ K := by
      refine hK b (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) (N'.mul_mem (hconj _ _ (N'.inv_mem hu₂)) hu₁) ?_
      have : ι b * (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) = k₂ * k₁⁻¹ := by
        have e' : ι y.out * u₁ = ι y'.out * u₂ * k₂ * k₁⁻¹ := by rw [← e]; group
        calc _ = u₂⁻¹ * (ι y'.out)⁻¹ * (ι y.out * u₁) := by
              simp only [hb, map_mul, map_inv]; group
          _ = _ := by rw [e']; group
      rw [this]
      exact K.mul_mem hk₂ (K.inv_mem hk₁)
    rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
    exact (QuotientGroup.eq.2 hb').symm

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumTwoStageDescentUnipotentStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_sum_two_stage_descent_unipotent : GlobalTheory.SatakeWeyl.Descent := by
  first | exact @GlobalTheory.SatakeWeyl.descent | exact GlobalTheory.SatakeWeyl.descent | (intros; apply GlobalTheory.SatakeWeyl.descent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDominantDiagonalConjugationContracts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDominantDiagonalConjugationContracts
open Formalism.UG GlobalTheory.SatakeWeyl

noncomputable section

namespace GlobalTheory.SatakeWeyl.ContractProof

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_inv_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) :
    mat s⁻¹ = Matrix.diagonal (fun i => ϖ ^ (-c i)) := by
  have h1 : mat s * Matrix.diagonal (fun i => ϖ ^ (-c i)) = 1 := by
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; simp
  calc mat s⁻¹ = mat s⁻¹ * (mat s * Matrix.diagonal (fun i => ϖ ^ (-c i))) := by rw [h1, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_conj {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (i l : Fin r) :
    mat (s * g * s⁻¹) i l = ϖ ^ (c i - c l) * mat g i l := by
  rw [mat_mul, mat_mul, mat_inv_diag h0 c s hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg,
    zpow_add₀ h0]
  ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_pow_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (j : ℕ) :
    mat (s ^ j) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * c i)) := by
  induction j with
  | zero => simp [mat_one]
  | succ j ih =>
    rw [pow_succ, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; congr 1; push_cast; ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem conj_mem_root {ϖ : L} (h0 : ϖ ≠ 0) (γ : Fin r → ℕ) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ) : s * g * s⁻¹ ∈ rootU σ γ := by
  refine ⟨fun i l h => ?_, fun i l h => ?_⟩
  · rw [mat_conj h0 c s g hs, hg.1 i l h]
    by_cases e : i = l
    · subst e; simp
    · rw [Matrix.one_apply_ne e, mul_zero]
  · rw [mat_conj h0 c s g hs, hg.2 i l h, mul_zero]

theorem conj_mem_K {ϖ : L} (h0 : ϖ ≠ 0) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (γ : Fin r → ℕ) (c : Fin r → ℤ)
    (s g : GU σ r) (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ)
    (H : ∀ i l, i < l → γ i = γ l → ϖ ^ (c i - c l) * mat g i l ∈ intL L) : s * g * s⁻¹ ∈ KU σ r := by
  rw [mem_KU_iff hσ]
  intro i l
  have hr := conj_mem_root h0 γ c s g hs hg
  by_cases h1 : i < l
  · by_cases h2 : γ i = γ l
    · rw [mat_conj h0 c s g hs]; exact H i l h1 h2
    · rw [hr.2 i l h2]; exact zero_mem _
  · rw [hr.1 i l (not_lt.1 h1), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem zpow_mul_int {ϖ : L} (hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → ϖ ^ m * x ∈ intL L := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by rw [hx, mul_zero]; exact zero_mem _⟩
  have hx' : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := by simpa using hx
  refine ⟨(WithZero.log (Valued.v x : WithZero (Multiplicative ℤ))).toNat, fun m hm => ?_⟩
  show Valued.v (ϖ ^ m * x) ≤ (1 : WithZero (Multiplicative ℤ))
  rw [map_mul, map_zpow₀, hv, ← WithZero.exp_log hx', ← WithZero.exp_zsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  have := Int.self_le_toNat (WithZero.log (Valued.v x : WithZero (Multiplicative ℤ)))
  simp only [smul_eq_mul]
  omega

theorem contract : GlobalTheory.SatakeWeyl.Contract := by
  intro L _ _ ϖ σ q r γ b s g hU hb hs hg
  obtain ⟨-, hσ, -, hv, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  refine ⟨conj_mem_root h0 γ b s g hs hg, ?_, fun hK => ?_, ?_⟩
  · have := conj_mem_root h0 γ _ s⁻¹ g (mat_inv_diag h0 b s hs) hg
    rwa [inv_inv] at this
  · refine conj_mem_K h0 hσ γ b s g hs hg fun i l h1 h2 => ?_
    refine mul_mem ?_ ((mem_KU_iff hσ g).1 hK i l)
    show Valued.v (ϖ ^ (b i - b l)) ≤ (1 : WithZero (Multiplicative ℤ))
    have := hb i l h1 h2
    rw [map_zpow₀, hv', ← WithZero.exp_zsmul, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    omega
  · choose N hN using fun p : Fin r × Fin r => zpow_mul_int hv' (mat g p.1 p.2)
    refine ⟨Finset.univ.sup N, conj_mem_K h0 hσ γ _ _ g (mat_pow_diag h0 b s hs _) hg fun i l h1 h2 => ?_⟩
    refine hN (i, l) _ ?_
    have h3 := hb i l h1 h2
    have h4 : (N (i, l) : ℤ) ≤ (Finset.univ.sup N : ℕ) := by
      exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ _)
    have h5 : (0 : ℤ) ≤ (Finset.univ.sup N : ℕ) := Int.natCast_nonneg _
    nlinarith

end GlobalTheory.SatakeWeyl.ContractProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDominantDiagonalConjugationContractsStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts : GlobalTheory.SatakeWeyl.Contract := by
  first | exact @GlobalTheory.SatakeWeyl.ContractProof.contract | exact GlobalTheory.SatakeWeyl.ContractProof.contract | (intros; apply GlobalTheory.SatakeWeyl.ContractProof.contract <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSq
noncomputable section

open Formalism.UG

namespace GlobalTheory.SatakeWeyl.IdxFour

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def rootMat (σ : L →+* L) (x : L) : Matrix (Fin 4) (Fin 4) L :=
  !![1, x, 0, 0; 0, 1, 0, 0; 0, 0, 1, -σ x; 0, 0, 0, 1]

theorem rootMat_unitary (hσ : ∀ x, σ (σ x) = x) (x : L) :
    cT σ (rootMat σ x) * antiJ L 4 * rootMat σ x = antiJ L 4 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [P.fSatake_cTJ, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [rootMat, antiJ, Fin.rev, hσ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem rootMat_add (x y : L) : rootMat σ (x + y) = rootMat σ x * rootMat σ y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

theorem exists_hom (hσ : ∀ x, σ (σ x) = x) :
    ∃ φ : Multiplicative L →* GU σ 4, ∀ x, mat (φ x) = rootMat σ x.toAdd := by
  choose f hf using fun x : L => exists_mat (rootMat σ x) (rootMat_unitary hσ x)
  refine ⟨MonoidHom.mk' (fun x => f x.toAdd) fun a b => mat_injective ?_, fun x => hf _⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, rootMat_add]

theorem mat_of_mem (hσ : ∀ x, σ (σ x) = x) {g : GU σ 4} (hg : g ∈ rootU σ ![0, 0, 1, 1]) :
    mat g = rootMat σ (mat g 0 1) := by
  have h1 : ∀ i j : Fin 4, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 4) (Fin 4) L) i j := hg.1
  have h2 : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ (![0, 0, 1, 1] : Fin 4 → ℕ) j → mat g i j = 0 := hg.2
  have h3 : cT σ (mat g) * antiJ L 4 * mat g = antiJ L 4 := g.2
  have h4 := congrFun (congrFun h3 1) 3
  rw [Matrix.mul_apply] at h4
  simp only [P.fSatake_cTJ, Fin.sum_univ_four] at h4
  have e00 := h1 0 0 (by decide)
  have e11 := h1 1 1 (by decide)
  have e22 := h1 2 2 (by decide)
  have e33 := h1 3 3 (by decide)
  have e10 := h1 1 0 (by decide)
  have e32 := h1 3 2 (by decide)
  have e02 := h2 0 2 (by decide)
  have e03 := h2 0 3 (by decide)
  have e12 := h2 1 2 (by decide)
  have e13 := h2 1 3 (by decide)
  have e20 := h2 2 0 (by decide)
  have e21 := h2 2 1 (by decide)
  have e30 := h2 3 0 (by decide)
  have e31 := h2 3 1 (by decide)
  have r0 : Fin.rev (0 : Fin 4) = 3 := rfl
  have r1 : Fin.rev (1 : Fin 4) = 2 := rfl
  have r2 : Fin.rev (2 : Fin 4) = 1 := rfl
  have r3 : Fin.rev (3 : Fin 4) = 0 := rfl
  rw [r0, r1, r2, r3, e03, e13, e11, e33] at h4
  have e23 : mat g 2 3 = -σ (mat g 0 1) := by
    simp [antiJ] at h4
    exact eq_neg_of_add_eq_zero_left h4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rootMat, *]

theorem mem_root {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) : g ∈ rootU σ ![0, 0, 1, 1] := by
  refine ⟨fun i j h => ?_, fun i j h => ?_⟩
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢
  · rw [hg]
    fin_cases i <;> fin_cases j <;> simp [rootMat] at h ⊢

theorem mem_K_iff (hv : ∀ x, Valued.v (σ x) = Valued.v x) {g : GU σ 4} {x : L} (hg : mat g = rootMat σ x) :
    g ∈ KU σ 4 ↔ x ∈ intL L := by
  rw [mem_KU_iff hv, hg]
  refine ⟨fun h => by simpa [rootMat] using h 0 1, fun h i j => ?_⟩
  have h' : σ x ∈ intL L := by
    show Valued.v (σ x) ≤ 1
    rw [hv]
    exact h
  fin_cases i <;> fin_cases j <;> simp [rootMat, h, h', one_mem, zero_mem]

theorem indexFour (hI : IntIndex) : IndexFour := by
  intro L _ _ ϖ σ q hU s₀ hs
  obtain ⟨φ, hφ⟩ := exists_hom hU.1
  have hϖ : ϖ ≠ 0 := by
    rintro rfl
    have := hU.2.2.2.1
    simp at this
  have hinj : Function.Injective φ := fun a b h => by
    have := congrFun (congrFun ((hφ a).symm.trans ((congrArg mat h).trans (hφ b))) 0) 1
    simpa [rootMat] using this
  have hK : KU σ 4 ⊓ rootU σ ![0, 0, 1, 1] = (AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      have e := mat_of_mem hU.1 h2
      exact ⟨Multiplicative.ofAdd (mat g 0 1), (mem_K_iff hU.2.1 e).1 h1, mat_injective ((hφ _).trans e.symm)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(mem_K_iff hU.2.1 (hφ x)).2 hx, mem_root (hφ x)⟩
  have hc : ∀ x : L, s₀ * φ (Multiplicative.ofAdd x) * s₀⁻¹ = φ (Multiplicative.ofAdd (ϖ * x)) := by
    intro x
    rw [mul_inv_eq_iff_eq_mul]
    apply mat_injective
    rw [mat_mul, mat_mul, hφ, hφ, hs]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases j <;> simp [rootMat, hU.2.2.1]
    field_simp
  have hK' : ((AddSubgroup.toSubgroup (intL L).toAddSubgroup).map φ).map (MulAut.conj s₀).toMonoidHom =
      (AddSubgroup.toSubgroup ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ))).map φ := by
    ext g
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Multiplicative.ofAdd (ϖ * x.toAdd), ⟨x.toAdd, hx, rfl⟩, (hc x.toAdd).symm⟩
    · rintro ⟨y, ⟨x, hx, e⟩, rfl⟩
      refine ⟨φ (Multiplicative.ofAdd x), ⟨_, hx, rfl⟩, (hc x).trans (congrArg φ ?_)⟩
      exact congrArg Multiplicative.ofAdd e
  rw [hK, hK', Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup]
  exact hI L ϖ σ q hU

end GlobalTheory.SatakeWeyl.IdxFour

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSqStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.IndexFour := by
  first | exact @GlobalTheory.SatakeWeyl.IdxFour.indexFour | exact GlobalTheory.SatakeWeyl.IdxFour.indexFour | (intros; apply GlobalTheory.SatakeWeyl.IdxFour.indexFour <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankTwoRootIndexOfTraceZeroCard
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankTwoRootIndexOfTraceZeroCard
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

theorem indexTwo_unitary (y : L) (hy : σ y + y = 0) :
    cT σ !![1, y; 0, 1] * antiJ L 2 * !![1, y; 0, 1] = antiJ L 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cT, antiJ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [add_comm]; exact hy

theorem indexTwo_exists_hom (σ : L →+* L) (T : AddSubgroup L) (hT : ∀ y, y ∈ T ↔ σ y + y = 0) :
    ∃ ψ : Multiplicative T →* GU σ 2,
      ∀ y, mat (ψ y) = !![1, (y.toAdd : L); 0, 1] := by
  have h : ∀ y : Multiplicative T,
      ∃ g : GU σ 2, mat g = !![1, (y.toAdd : L); 0, 1] := fun y =>
    exists_mat _ (indexTwo_unitary _ ((hT _).1 y.toAdd.2))
  choose f hf using h
  refine ⟨MonoidHom.mk' f fun a b => mat_injective ?_, hf⟩
  rw [mat_mul, hf, hf, hf, toAdd_mul, AddSubgroup.coe_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem indexTwo_mem_root (g : GU σ 2) :
    g ∈ rootU σ ![0, 0] ↔ mat g = !![1, mat g 0 1; 0, 1] := by
  constructor
  · intro h
    have h1 : ∀ i j : Fin 2, j.val ≤ i.val → mat g i j = (1 : Matrix (Fin 2) (Fin 2) L) i j := h.1
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1 0 0 (by simp)
    · simp
    · simpa using h1 1 0 (by simp)
    · simpa using h1 1 1 (by simp)
  · intro h
    refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
    · rw [h]
      fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · fin_cases i <;> fin_cases j <;> simp at hij

theorem indexTwo_trace (g : GU σ 2) (y : L) (h : mat g = !![1, y; 0, 1]) : σ y + y = 0 := by
  have h1 : cT σ (mat g) * antiJ L 2 * mat g = antiJ L 2 := g.2
  rw [h] at h1
  have := congrFun (congrFun h1 1) 1
  simpa [cT, antiJ, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using this

theorem indexTwo_conj {ϖ : L} (h0 : ϖ ≠ 0) (s g : GU σ 2)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ (![1, -1] : Fin 2 → ℤ) i)) (y : L)
    (h : mat g = !![1, y; 0, 1]) : mat (s * g * s⁻¹) = !![1, ϖ * (ϖ * y); 0, 1] := by
  have e : mat s * mat g = !![1, ϖ * (ϖ * y); 0, 1] * mat s := by
    rw [hs, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
  rw [mat_mul, mat_mul, e, Matrix.mul_assoc, mat_mul_inv, Matrix.mul_one]

end

theorem indexTwo_of_traceZeroIndex (H : TraceZeroIndex) : IndexTwo := by
  intro L _ _ ϖ σ q hU s hs
  have hq := H L ϖ σ q hU
  have h0 : ϖ ≠ 0 := by
    intro h
    have := hU.2.2.2.1
    rw [h, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hϖ : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hU.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  have memT : ∀ y, y ∈ (σ.toAddMonoidHom + AddMonoidHom.id L).ker ↔ σ y + y = 0 := fun y => Iff.rfl
  generalize (σ.toAddMonoidHom + AddMonoidHom.id L).ker = T at hq memT
  obtain ⟨ψ, hψ⟩ := indexTwo_exists_hom σ T memT
  set U := (intL L).toAddSubgroup ⊓ T with hUdef
  set m : L →+ L := AddMonoidHom.mulLeft ϖ with hm
  have hmT : ∀ y, y ∈ T → ϖ * y ∈ T := fun y hy => by
    rw [memT] at hy ⊢
    rw [map_mul, hU.2.2.1, ← mul_add, hy, mul_zero]
  have hminj : Function.Injective m := mul_right_injective₀ h0
  have hle : U.map m ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(intL L).mul_mem hϖ hy.1, hmT y hy.2⟩
  have h2 : ((U.map m).map m).relIndex U = q ^ 2 := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ (U.map m) _ (AddSubgroup.map_mono hle) hle,
      AddSubgroup.relIndex_map_map_of_injective _ _ hminj, hq, sq]
  have hinj : Function.Injective ψ := by
    intro a b hab
    have := congrFun (congrFun ((hψ a).symm.trans ((congrArg mat hab).trans (hψ b))) 0) 1
    exact Multiplicative.toAdd.injective (Subtype.ext (by simpa using this))
  have e1 : KU σ 2 ⊓ rootU σ ![0, 0] = (AddSubgroup.toSubgroup (U.addSubgroupOf T)).map ψ := by
    ext g
    constructor
    · rintro ⟨hK, hr⟩
      have hr' := (indexTwo_mem_root g).1 hr
      have ht := (memT _).2 (indexTwo_trace g _ hr')
      refine ⟨Multiplicative.ofAdd ⟨mat g 0 1, ht⟩, ⟨(mem_KU_iff hU.2.1 g).1 hK 0 1, ht⟩, mat_injective ?_⟩
      rw [hψ]; exact hr'.symm
    · rintro ⟨y, hy, rfl⟩
      have hy1 : (y.toAdd : L) ∈ intL L := hy.1
      refine ⟨(mem_KU_iff hU.2.1 _).2 fun i j => ?_, (indexTwo_mem_root _).2 ?_⟩
      · rw [hψ]
        fin_cases i <;> fin_cases j
        · exact one_mem _
        · exact hy1
        · exact zero_mem _
        · exact one_mem _
      · rw [hψ]; rfl
  have e2 : ((AddSubgroup.toSubgroup (U.addSubgroupOf T)).map ψ).map (MulAut.conj s).toMonoidHom =
      (AddSubgroup.toSubgroup (((U.map m).map m).addSubgroupOf T)).map ψ := by
    ext g
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨Multiplicative.ofAdd ⟨ϖ * (ϖ * (y.toAdd : L)), hmT _ (hmT _ y.toAdd.2)⟩,
        ⟨_, ⟨_, hy, rfl⟩, rfl⟩, mat_injective ?_⟩
      rw [hψ]
      exact (indexTwo_conj h0 s _ hs _ (hψ y)).symm
    · rintro ⟨z, ⟨_, ⟨y, hy, rfl⟩, hz⟩, rfl⟩
      refine ⟨ψ (Multiplicative.ofAdd ⟨y, hy.2⟩), ⟨Multiplicative.ofAdd ⟨y, hy.2⟩, hy, rfl⟩, mat_injective ?_⟩
      refine (indexTwo_conj h0 s _ hs _ (hψ _)).trans ?_
      rw [hψ]
      exact congrArg (fun w => !![1, w; 0, 1]) hz
  rw [e1, e2, Subgroup.relIndex_map_map_of_injective _ _ hinj, AddSubgroup.relIndex_toSubgroup,
    AddSubgroup.relIndex_addSubgroupOf inf_le_right, h2]

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankTwoRootIndexOfTraceZeroCardStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard : GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexTwo := by
  first | exact @GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | exact GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex | (intros; apply GlobalTheory.SatakeWeyl.indexTwo_of_traceZeroIndex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSpanSingletonConstGenSurjective
noncomputable section

open CategoryTheory

namespace GlobalTheory

namespace PDivGroup

theorem exists_algHom_pi_eq_eval {O ι : Type*} [CommRing O] [Nontrivial O] [Finite ι]
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) (f : (ι → O) →ₐ[O] O) :
    ∃ k, ∀ g, f g = g k := by
  classical
  have := Fintype.ofFinite ι
  have h1 : ∃ k, f (Pi.single k 1) ≠ 0 := by
    by_contra h
    have h' : ∀ k, f (Pi.single k 1) = 0 := fun k => by_contra fun hk => h ⟨k, hk⟩
    have h2 : f (∑ k, Pi.single k 1) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun k _ => h' k
    have h3 : (∑ k, Pi.single k 1 : ι → O) = 1 := Finset.univ_sum_single (1 : ι → O)
    rw [h3, map_one] at h2
    exact one_ne_zero h2
  obtain ⟨k, hk⟩ := h1
  have hi : IsIdempotentElem (Pi.single k 1 : ι → O) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  have h4 : f (Pi.single k 1) = 1 := (hO _ (hi.map f)).resolve_left hk
  refine ⟨k, fun g => ?_⟩
  have h5 : g * Pi.single k 1 = g k • (Pi.single k 1 : ι → O) := by
    funext j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  have h6 := congrArg f h5
  rwa [map_mul, map_smul, h4, mul_one, smul_eq_mul, mul_one] at h6

variable (p : ℕ) (O : Type) [CommRing O] [Fact p.Prime]

variable [Nontrivial O]

theorem toSpanSingleton_constGen_surjective
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Surjective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) := fun t => by
  have h1 : ∀ n, ∃ k : ℕ, ∀ φ, t.pt n φ = constFun p O n φ k := fun n => by
    obtain ⟨k, hk⟩ := exists_algHom_pi_eq_eval hO
      ((t.pt n).comp ((constFun p O n).symm : (ZMod (p ^ n) → O) →ₐ[O] (const p O).A n))
    refine ⟨k.val, fun φ => ?_⟩
    rw [ZMod.natCast_zmod_val, ← hk (constFun p O n φ)]
    exact congrArg (t.pt n) ((constFun p O n).symm_apply_apply φ).symm
  choose k hk using h1
  have h2 : ∀ n, ((k (n + 1) : ℕ) : ZMod (p ^ n)) = k n := fun n => by
    have h := t.pt_mulP n ((constFun p O n).symm (Pi.single (k n : ZMod (p ^ n)) 1))
    rw [hk, hk, constFun_mulP, AlgEquiv.apply_symm_apply, Pi.single_eq_same] at h
    by_contra hne
    rw [Pi.single_eq_of_ne hne] at h
    exact zero_ne_one h
  have h3 : ∀ n, (p : ℤ) ^ n ∣ (k (n + 1) : ℤ) - k n := fun n => by
    rw [← Nat.cast_pow, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_natCast,
      Int.cast_natCast, h2, sub_self]
  refine ⟨PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun n => (k n : ℤ)) p h3),
    TateOver.ext (funext fun n => AlgHom.ext fun φ => ?_)⟩
  rw [LinearMap.toSpanSingleton_apply, smul_constGen_pt,
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun n => (k n : ℤ)) p h3 n, Int.cast_natCast, hk]

theorem toSpanSingleton_constGen_bijective
    (hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Function.Bijective (LinearMap.toSpanSingleton ℤ_[p] _ (constGen p O)) :=
  ⟨toSpanSingleton_constGen_injective p O, toSpanSingleton_constGen_surjective p O hO⟩

end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquiv
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem ghost_ofPadic (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ) (s : ℤ_[p]) :
    ghost p O n (ofPadic p O s) = padicToO p O s := by
  let g : ℤ_[p] →+* O :=
    { toFun := fun s => ghost p O n (ofPadic p O s)
      map_one' := by simp only [map_one, ghost, iterate_map_one]
      map_mul' := fun a b => by simp only [map_mul, ghost_mul]
      map_zero' := by simp only [map_zero, ghost_zero]
      map_add' := fun a b => by simp only [map_add (f := _), ghost_add] }
  exact congrArg (fun f : ℤ_[p] →+* O => f s) (padicToO_unique p O g)

theorem hodgeTate_constGen (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] :
    hodgeTate (const p O) (constGen p O) = constDlogT p O := by
  rw [hodgeTate_eq_omegaDualMap, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], omegaDualMap_id,
    LinearMap.id_apply]

theorem latt_const_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε),
    ∃ e : latt (const p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, e y = y.1 (constGen p O) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε
  have hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he =>
    IsIdempotentElem.iff_eq_zero_or_one.1 he

  let φ : ℤ_[p] ≃ₗ[ℤ_[p]] (const p O).Tate :=
    LinearEquiv.ofBijective _ (toSpanSingleton_constGen_bijective p O hO)
  have hφ : ∀ s, φ s = s • constGen p O := fun s => rfl
  obtain ⟨eω, heω⟩ := DieudonneSandwich.exists_equiv_constDlogT (p := p) (O := O)
  let f : latt (const p O) →ₗ[Ainf p O] Ainf p O :=
    { toFun := fun y => y.1 (constGen p O)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofBijective f ⟨fun y z h => ?_, fun a => ?_⟩, fun _ => rfl⟩
  · apply Subtype.ext
    apply LinearMap.ext
    intro t
    obtain ⟨s, rfl⟩ := φ.surjective t
    rw [hφ, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    exact congrArg _ h
  · let y : TDual (const p O) :=
      { toFun := fun t => ofPadic p O (φ.symm t) * a
        map_add' := fun t t' => by rw [map_add (f := _), map_add (f := _), add_mul]
        map_smul' := fun c t => by
          rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul, mul_assoc] }
    have hy : y ∈ latt (const p O) := fun n => by
      refine ⟨ghost p O n a • eω.symm.toLinearMap, fun t => ?_⟩
      obtain ⟨s, rfl⟩ := φ.surjective t
      change ghost p O n (ofPadic p O (φ.symm (φ s)) * a) = _
      rw [LinearEquiv.symm_apply_apply, ghost_mul, ghost_ofPadic, hφ,
        hodgeTate_smul (padicToO p O), hodgeTate_constGen, LinearMap.smul_apply,
        LinearEquiv.coe_toLinearMap, map_smul, ← heω, LinearEquiv.symm_apply_apply, smul_eq_mul,
        smul_eq_mul, mul_one, mul_comm]
    refine ⟨⟨y, hy⟩, ?_⟩
    change ofPadic p O (φ.symm (constGen p O)) * a = a
    have : φ.symm (constGen p O) = 1 := φ.symm_apply_eq.2 (by rw [hφ, one_smul])
    rw [this, map_one, one_mul]

end GlobalTheory.PDivLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquivStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (const p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, e y = y.1 (constGen p O) := by
  first | exact @GlobalTheory.PDivLat.latt_const_equiv | exact GlobalTheory.PDivLat.latt_const_equiv | (intros; apply GlobalTheory.PDivLat.latt_const_equiv <;> assumption)
end
end
