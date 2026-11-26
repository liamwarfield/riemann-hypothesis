module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsFinTyp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinTypCount

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

theorem countable_field : Countable L :=
  (Module.finBasis ℚ L).equivFun.toEquiv.injective.countable

theorem tmul_mem_ALint (o : 𝓞 L) {a : AFplus L} (ha : ∀ v, a v ∈ v.adicCompletionIntegers L⁺) :
    ((o : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L := by
  have h1 : ((o : L) ⊗ₜ[L⁺] (1 : AFplus L) : AL L) ∈ ALint L :=
    Subring.subset_closure (Or.inl ⟨o, rfl⟩)
  have h2 : ((1 : L) ⊗ₜ[L⁺] a : AL L) ∈ ALint L :=
    Subring.subset_closure (Or.inr ⟨a, ha, rfl⟩)
  have := Subring.mul_mem _ h1 h2
  rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this

theorem exists_nat_smul_int (e : L) : ∃ D : ℕ, 0 < D ∧ ∃ o : 𝓞 L, (o : L) = D • e := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := L) ({e} : Finset L)
  refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
  have hi : IsIntegral ℤ ((y * y).natAbs • e) := by
    rw [← natCast_zsmul, Int.natAbs_of_nonneg (mul_self_nonneg y), mul_smul]
    exact (h e (Finset.mem_singleton_self e)).smul y
  exact ⟨⟨_, hi⟩, rfl⟩

theorem exists_approx (M : ℕ) (hM : 0 < M) (x : AL L) :
    ∃ c : L, ∃ y ∈ ALint L, x = c ⊗ₜ[L⁺] (1 : AFplus L) + M • y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    obtain ⟨c, y, hy, rfl⟩ := hx
    obtain ⟨c', y', hy', rfl⟩ := hx'
    exact ⟨c + c', y + y', add_mem hy hy', by rw [TensorProduct.add_tmul, smul_add]; abel⟩
  | tmul e a =>
    obtain ⟨D, hD, o, ho⟩ := exists_nat_smul_int e
    obtain ⟨k, a', ha', rfl⟩ :=
      (GlobalTheory.AdLat.strong_approximation_mod_nat L⁺ (D * M) (Nat.mul_pos hD hM)).1 a
    refine ⟨algebraMap L⁺ L k * e, _, tmul_mem_ALint o ha', ?_⟩
    rw [TensorProduct.tmul_add, Algebra.algebraMap_eq_smul_one k, ← TensorProduct.smul_tmul,
      ← Algebra.smul_def, ho, TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_comm, mul_smul]
    simp only [TensorProduct.smul_tmul']

theorem exists_denom (x : AL L) : ∃ m : ℕ, 0 < m ∧ (m : AL L) * x ∈ ALint L := by
  obtain ⟨c, y, hy, rfl⟩ := exists_approx 1 one_pos x
  obtain ⟨D, hD, o, ho⟩ := exists_nat_smul_int c
  refine ⟨D, hD, ?_⟩
  have e1 : (D : AL L) * (c ⊗ₜ[L⁺] (1 : AFplus L)) = (o : L) ⊗ₜ[L⁺] (1 : AFplus L) := by
    rw [ho, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  rw [mul_add, e1, one_smul]
  exact add_mem (tmul_mem_ALint o (fun v => one_mem _)) (Subring.mul_mem _ (natCast_mem _ _) hy)

variable {n : ℕ}

theorem exists_denom_matrix (G : Matrix (Fin n) (Fin n) (AL L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, (m : AL L) * G i j ∈ ALint L := by
  classical
  choose m hm h using fun p : Fin n × Fin n => exists_denom (G p.1 p.2)
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun i j => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (i, j))
  rw [hk, Nat.cast_mul, mul_comm ((m (i, j) : ℕ) : AL L), mul_assoc]
  exact Subring.mul_mem _ (natCast_mem _ _) (h (i, j))

theorem exists_code (N : ℕ) (hN : 0 < N) (g : GAf L n) :
    ∃ p : ℕ × (Fin n → Fin n → L), 0 < p.1 ∧
      (∀ i j, (p.1 : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) ∧
      ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        p.2 i j ⊗ₜ[L⁺] (1 : AFplus L) + (p.1 * N) • y := by
  obtain ⟨m, hm, h⟩ := exists_denom_matrix (g.1 : Matrix (Fin n) (Fin n) (AL L))
  choose c y hy e using fun i j =>
    exists_approx (m * N) (Nat.mul_pos hm hN) ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j)
  exact ⟨(m, c), hm, h, fun i j => ⟨y i j, hy i j, e i j⟩⟩

theorem inv_val (g : GAf L n) :
    (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) (g.1 : Matrix (Fin n) (Fin n) (AL L)) := by
  have hm := g.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  exact Units.inv_eq_of_mul_eq_one_right hm

theorem cong_of_code {N m : ℕ} {c : Fin n → Fin n → L} {g g' : GAf L n}
    (hg : ∀ i j, (m : AL L) * (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L)
    (e : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y)
    (e' : ∀ i j, ∃ y ∈ ALint L, (g'.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
      c i j ⊗ₜ[L⁺] (1 : AFplus L) + (m * N) • y) :
    Cong L n N (g⁻¹ * g') := by
  choose y hy ey using e
  choose y' hy' ey' using e'
  set A : Matrix (Fin n) (Fin n) (AL L) := (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hAdef
  have hAint : ∀ i j, (m : AL L) * A i j ∈ ALint L := by
    intro i j
    rw [hAdef, inv_val]
    simp only [conjT, Matrix.transpose_apply, Matrix.map_apply]
    have := conjAL_mem_ALint L (hg j i)
    rwa [map_mul, map_natCast] at this
  have hAG : A * (g.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := Units.inv_mul g.1
  set Y : Matrix (Fin n) (Fin n) (AL L) := Matrix.of fun i j => y' i j - y i j
  have hG' : (g'.1 : Matrix (Fin n) (Fin n) (AL L)) =
      (g.1 : Matrix (Fin n) (Fin n) (AL L)) + (N : AL L) • ((m : AL L) • Y) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Y, Matrix.of_apply, smul_eq_mul, ey, ey',
      nsmul_eq_mul]
    push_cast
    ring
  have hk : (((g⁻¹ * g' : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + (N : AL L) • (((m : AL L) • A) * Y) := by
    change A * (g'.1 : Matrix (Fin n) (Fin n) (AL L)) = _
    rw [hG', Matrix.mul_add, hAG, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hz : ∀ i j, (((m : AL L) • A) * Y) i j ∈ ALint L := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Y, Matrix.of_apply, smul_eq_mul]
    exact Subring.sum_mem _ fun k _ =>
      Subring.mul_mem _ (hAint i k) (Subring.sub_mem _ (hy' k j) (hy k j))
  refine ⟨fun i j => ?_, fun i j => ⟨_, hz i j, ?_⟩⟩
  · show (((g⁻¹ * g' : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
    rw [hk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine Subring.add_mem _ ?_ (Subring.mul_mem _ (natCast_mem _ _) (hz i j))
    rw [Matrix.one_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hk, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem rt_mul (h h' : GAf L n) (f : GAf L n → ℂ) : rt L n (h * h') f = rt L n h (rt L n h' f) := by
  funext x
  simp [rt, mul_assoc]

theorem countable_range_rt {f : GAf L n → ℂ} {N : ℕ} (hN : 0 < N)
    (hf : ∀ κ, Cong L n N κ → rt L n κ f = f) :
    (Set.range fun h : GAf L n => rt L n h f).Countable := by
  classical
  haveI := countable_field (L := L)
  choose p _ hp2 hp3 using exists_code (L := L) (n := n) N hN
  let Ψ : ℕ × (Fin n → Fin n → L) → (GAf L n → ℂ) := fun q =>
    if hq : ∃ g, p g = q then rt L n hq.choose f else 0
  have key : ∀ g, rt L n g f = Ψ (p g) := by
    intro g
    have hq : ∃ g', p g' = p g := ⟨g, rfl⟩
    simp only [Ψ, dif_pos hq]
    have e := hq.choose_spec
    have h3 := hp3 hq.choose
    rw [e] at h3
    have hc : Cong L n N (g⁻¹ * hq.choose) :=
      cong_of_code (c := (p g).2) (hp2 g) (hp3 g) h3
    calc rt L n g f = rt L n g (rt L n (g⁻¹ * hq.choose) f) := by rw [hf _ hc]
      _ = rt L n hq.choose f := by rw [← rt_mul, mul_inv_cancel_left]
  refine (Set.countable_range Ψ).mono ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨p g, (key g).symm⟩

end GlobalTheory.FinTypCount

namespace GlobalTheory


open GlobalTheory.FinTypCount in
theorem FinTyp.rank_le_aleph0 : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by
  intro L _ _ _ n π
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne
  obtain ⟨N, hN, hfix⟩ := π.smooth f hfS
  let T := Submodule.span ℂ (Set.range fun h : GAf L n => rt L n h f)
  have hle : T ≤ π.S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact π.stable h f hfS
  have hst : ∀ h, ∀ u ∈ T, rt L n h u ∈ T := by
    intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h', rfl⟩ := hx
      exact Submodule.subset_span ⟨h * h', rt_mul h h' f⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hfT : f ∈ T := Submodule.subset_span ⟨1, by funext x; simp [rt]⟩
  have hT : T = π.S := by
    rcases π.irr T hle hst with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hfT)) hf0
    · exact h
  rw [← hT]
  exact (rank_span_le _).trans (Cardinal.le_aleph0_iff_set_countable.2 (countable_range_rt hN hfix))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelicStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_aleph0_smooth_irreducible_unitaryAdelic : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.FinTyp.rank_le_aleph0 | exact GlobalTheory.FinTyp.rank_le_aleph0 | (intros; apply GlobalTheory.FinTyp.rank_le_aleph0 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitarySiegelParabolicBlockRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitarySiegelParabolicBlockRelations
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp


open MeasureTheory Matrix in
theorem _root_.GlobalTheory.KSp.sieg_blocks : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E)
    (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (p : _root_.GlobalTheory.WeilM.UG c (_root_.GlobalTheory.SplitUnitary.stdJ ν E)), p ∈ _root_.GlobalTheory.KSp.sieg c ν →
    (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₂₂).map c)ᵀ = 1 ∧
    (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₁₂).map c)ᵀ = (_root_.GlobalTheory.KSp.mat c p).toBlocks₁₂ * (((_root_.GlobalTheory.KSp.mat c p).toBlocks₁₁).map c)ᵀ ∧
    ∃ (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b), p = _root_.GlobalTheory.SplitUnitary.levi c hE.invol a * _root_.GlobalTheory.KSp.unip c b hb := by
  intro F _ _ E _ _ c δ hE ν _ _ p hp
  rw [_root_.GlobalTheory.KSp.mem_sieg] at hp
  have hc := hE.invol
  have hu := (_root_.GlobalTheory.SplitUnitary.mem_UG_iff c (p : GL (ν ⊕ ν) E)).mp p.2
  have hM : ((p : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = _root_.GlobalTheory.KSp.mat c p := rfl
  set M := _root_.GlobalTheory.KSp.mat c p
  rw [hM, ← fromBlocks_toBlocks M, hp] at hu
  unfold _root_.GlobalTheory.SplitUnitary.stdJ at hu
  simp only [fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_inj] at hu
  simp at hu
  obtain ⟨h1, h2, h3⟩ := hu
  have h2' := mul_eq_one_comm.mp h2
  have h3' := mul_eq_one_comm.mp h3
  have hcc : ∀ X : Matrix ν ν E, (X.map c).map c = X := fun X => by ext i j; simp [hc]
  have hAB : M.toBlocks₁₁ * (M.toBlocks₁₂.map c)ᵀ = M.toBlocks₁₂ * (M.toBlocks₁₁.map c)ᵀ :=
    sub_eq_zero.mp (by rw [← neg_add_eq_sub]; exact h1)
  refine ⟨h2, hAB, ?_⟩
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set D := M.toBlocks₂₂
  let a : GL ν E := ⟨A, (D.map c)ᵀ, h2, h2'⟩
  have hb : (((D.map c)ᵀ * B).map c)ᵀ = (D.map c)ᵀ * B := by
    rw [Matrix.map_mul, transpose_mul, transpose_map, hcc, transpose_transpose]
    have hB : B * (A.map c)ᵀ = A * (B.map c)ᵀ := hAB.symm
    calc (B.map c)ᵀ * D = (D.map c)ᵀ * A * (B.map c)ᵀ * D := by rw [h2', Matrix.one_mul]
      _ = (D.map c)ᵀ * (B * (A.map c)ᵀ) * D := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B * ((A.map c)ᵀ * D) := by simp only [Matrix.mul_assoc]
      _ = (D.map c)ᵀ * B := by rw [h3', Matrix.mul_one]
  refine ⟨a, (D.map c)ᵀ * B, hb, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, _root_.GlobalTheory.SplitUnitary.levi_val, hM]
  unfold _root_.GlobalTheory.KSp.unip
  simp only [fromBlocks_multiply]
  have ha : ((a⁻¹ : GL ν E) : Matrix ν ν E) = (D.map c)ᵀ := rfl
  rw [ha, transpose_map, hcc, transpose_transpose, ← Matrix.mul_assoc, h2]
  conv_lhs => rw [← fromBlocks_toBlocks M, hp]
  simp [A, B, D]
  rfl

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitarySiegelParabolicBlockRelationsStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitUnitarySiegelParabolic_block_relations : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (p : UG c (stdJ ν E)), p ∈ sieg c ν → (mat c p).toBlocks₁₁ * (((mat c p).toBlocks₂₂).map c)ᵀ = 1 ∧ (mat c p).toBlocks₁₁ * (((mat c p).toBlocks₁₂).map c)ᵀ = (mat c p).toBlocks₁₂ * (((mat c p).toBlocks₁₁).map c)ᵀ ∧ ∃ (a : GL ν E) (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b), p = levi c hE.invol a * unip c b hb := by
  first | exact @GlobalTheory.KSp.sieg_blocks | exact GlobalTheory.KSp.sieg_blocks | (intros; apply GlobalTheory.KSp.sieg_blocks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.RankFibre

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indScal_lift_law (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    (fun x => f x ⊗ₜ[ℂ] (1:ℂ)) ∈ indSpace (parab k (blocks a b))
      ((twist ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) (deltaHalf k (Two (Fin a) (Fin b)))).comp
        (leviProj k (blocks a b))) := by
  intro p x
  have h := hf.2 p x
  apply (TensorProduct.lid ℂ ℂ).injective
  simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, MonoidHom.coe_coe] at h ⊢
  rw [h]
  simp [parChar, detRep, ofChar_apply]
  ring

def indScalLift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
  ⟨⟨fun x => f x ⊗ₜ[ℂ] (1:ℂ), indScal_lift_law ν β a b hf⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((show IsOpen {g : GL (Fin (a + b)) k | rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f} from hf.1).mem_nhds (by simp)) fun g hg => by
      have hg' : rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f := hg
      apply Subtype.ext
      funext x
      show f (x * g) ⊗ₜ[ℂ] (1:ℂ) = f x ⊗ₜ[ℂ] (1:ℂ)
      rw [show f (x * g) = f x from congrFun hg' x])⟩

theorem indScal_lift_apply (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b)
    (x : GL (Fin (a + b)) k) : TensorProduct.lid ℂ ℂ ((indScalLift ν β a b hf).1.1 x) = f x := by
  simp [indScalLift]

def indScalVal (ν β : kˣ →* ℂˣ) (a b : ℕ) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] (GL (Fin (a + b)) k → ℂ) where
  toFun F x := TensorProduct.lid ℂ ℂ (F.1.1 x)
  map_add' F G := by
    funext x
    show TensorProduct.lid ℂ ℂ (F.1.1 x + G.1.1 x) = _
    rw [map_add (f := _)]
    rfl
  map_smul' c F := by
    funext x
    show TensorProduct.lid ℂ ℂ (c • F.1.1 x) = _
    rw [map_smul]
    rfl

theorem indScal_scal_lift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    indScalVal ν β a b (indScalLift ν β a b hf) = f :=
  funext (indScal_lift_apply ν β a b hf)

theorem indScal_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M := by
  intro H k _ _ _ _ a b ν β hνs hνu hβs hβu M hM hinv
  have hs : IsSmoothChar (ν * β) := hνs.mul hβs
  have hu : IsUnitaryChar (ν * β) := fun g => by simp [hνu g, hβu g]
  have h₁ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp a hs hu
  have h₂ := GlobalTheory.Published.BernsteinUnitaryProductIrreducible.detRep_hyp b hβs hβu
  have hirr := H k a b ℂ ℂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β) h₁.1 h₁.2.1 h₁.2.2 h₂.1 h₂.2.1 h₂.2.2
  let S : Subrepresentation (prod₂ (detRep (Fin a) (ν * β)) (detRep (Fin b) β)) :=
    ⟨M.comap (indScalVal ν β a b), fun g F hF => hinv _ hF g⟩
  have hS : S.toSubmodule = M.comap (indScalVal ν β a b) := rfl
  have hmem : ∀ f (hf : f ∈ indScal ν β a b), f ∈ M ↔ indScalLift ν β a b hf ∈ S.toSubmodule := fun f hf => by
    rw [hS, Submodule.mem_comap, indScal_scal_lift]
  rcases hirr.eq_bot_or_eq_top S with h | h
  · left
    refine (Submodule.eq_bot_iff M).2 fun f hf => ?_
    have h' := (hmem f (hM hf)).1 hf
    rw [h] at h'
    have h0 : indScalLift ν β a b (hM hf) = 0 := (Submodule.mem_bot ℂ).1 h'
    rw [← indScal_scal_lift ν β a b (hM hf), h0, map_zero]
  · right
    intro f hf
    refine (hmem f hf).2 ?_
    rw [h]
    exact Submodule.mem_top

end GlobalTheory.RankFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducibleStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_scalar_irreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M := by
  first | exact @GlobalTheory.RankFibre.indScal_irreducible | exact GlobalTheory.RankFibre.indScal_irreducible | (intros; apply GlobalTheory.RankFibre.indScal_irreducible <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalBlockSumSqNormBlockUnitaryInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalBlockSumSqNormBlockUnitaryInvariant
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.OffDiagUnitary

def Pm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun a => if ε a then 1 else 0

def Qm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun a => if ε a then 0 else 1

lemma Pm_eq {n : ℕ} (ε : Fin n → Bool) : Pm ε = (1/2 : ℂ) • (1 + Jm ε) := by
  ext i j
  by_cases h : i = j
  · subst h; cases hε : ε i <;> simp [Pm, Jm, hε] <;> norm_num
  · simp [Pm, Jm, h, diagonal_apply_ne _ h, one_apply_ne h]

lemma Qm_eq {n : ℕ} (ε : Fin n → Bool) : Qm ε = 1 - Pm ε := by
  ext i j
  by_cases h : i = j
  · subst h; cases hε : ε i <;> simp [Pm, Qm, hε]
  · simp [Pm, Qm, h, diagonal_apply_ne _ h, one_apply_ne h]

lemma comm_Pm {n : ℕ} {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    (h : a * Jm ε = Jm ε * a) : a * Pm ε = Pm ε * a := by
  rw [Pm_eq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, h,
    Matrix.mul_one, Matrix.one_mul]

lemma comm_Qm {n : ℕ} {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ}
    (h : a * Jm ε = Jm ε * a) : a * Qm ε = Qm ε * a := by
  rw [Qm_eq, Matrix.mul_sub, Matrix.sub_mul, comm_Pm h, Matrix.mul_one, Matrix.one_mul]

lemma sum_sq_norm_eq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) = trace (Mᴴ * M) := by
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

lemma trace_unitary_conj {n : ℕ} (a b h : Matrix (Fin n) (Fin n) ℂ) (ha : aᴴ * a = 1)
    (hb : bᴴ * b = 1) : trace ((a * h * b)ᴴ * (a * h * b)) = trace (hᴴ * h) := by
  have hb' : b * bᴴ = 1 := mul_eq_one_comm.mp hb
  have e : (a * h * b)ᴴ * (a * h * b) = bᴴ * ((hᴴ * h) * b) := by
    rw [conjTranspose_mul, conjTranspose_mul]
    calc bᴴ * (hᴴ * aᴴ) * (a * h * b) = bᴴ * (hᴴ * (aᴴ * a) * h * b) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, trace_mul_comm, Matrix.mul_assoc, hb', Matrix.mul_one]

lemma off_sum_eq {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2
      = ∑ i, ∑ j, ‖(Pm ε * M * Qm ε) i j‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun z : Fin n × Fin n => ε z.1 = true ∧ ε z.2 = false)
      (by simp) (fun z => ‖M z.1 z.2‖ ^ 2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pm, Qm, diagonal_mul, mul_diagonal]
  cases ε i <;> cases ε j <;> simp

end GlobalTheory.OffDiagUnitary

open GlobalTheory.OffDiagUnitary in
theorem GlobalTheory.offDiag_sum_sq_norm_unitary_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (a b g : Matrix (Fin n) (Fin n) ℂ), aᴴ * a = 1 → a * Jm ε = Jm ε * a → bᴴ * b = 1 → b * Jm ε = Jm ε * b → ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(a * g * b) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε a b g ha haJ hb hbJ
  rw [off_sum_eq, off_sum_eq]
  have e : Pm ε * (a * g * b) * Qm ε = a * (Pm ε * g * Qm ε) * b := by
    calc Pm ε * (a * g * b) * Qm ε = (Pm ε * a) * g * (b * Qm ε) := by simp only [Matrix.mul_assoc]
      _ = (a * Pm ε) * g * (Qm ε * b) := by rw [comm_Pm haJ, comm_Qm hbJ]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  apply Complex.ofReal_injective
  rw [sum_sq_norm_eq_trace, sum_sq_norm_eq_trace, trace_unitary_conj _ _ _ ha hb]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalBlockSumSqNormBlockUnitaryInvariantStatement
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offDiagonalBlock_sum_sq_norm_blockUnitary_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (a b g : Matrix (Fin n) (Fin n) ℂ), aᴴ * a = 1 → a * Jm ε = Jm ε * a → bᴴ * b = 1 → b * Jm ε = Jm ε * b → ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(a * g * b) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(g) z.1.1 z.1.2‖ ^ 2 := by
  first | exact @GlobalTheory.offDiag_sum_sq_norm_unitary_invariant | exact GlobalTheory.offDiag_sum_sq_norm_unitary_invariant | (intros; apply GlobalTheory.offDiag_sum_sq_norm_unitary_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem offDiagBlockNorm_cont_inv : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε
  refine ⟨?_, ?_⟩
  · have hM : Continuous fun g : UJ ε => toM g :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_finsetSum _ fun z _ => ?_
    exact ((continuous_apply z.1.2).comp ((continuous_apply z.1.1).comp hM)).norm.pow 2
  · intro k k' g
    have hk : toM (k : UJ ε) ∈ Kset ε := k.2
    have hk' : toM (k' : UJ ε) ∈ Kset ε := k'.2
    have hmul : toM ((k : UJ ε) * g * (k' : UJ ε)) = toM (k : UJ ε) * toM g * toM (k' : UJ ε) := rfl
    rw [hmul]
    refine GlobalTheory.T.offDiagonalBlock_sum_sq_norm_blockUnitary_invariant n ε _ _ _ ?_ hk.2 ?_ hk'.2
    · exact Matrix.mem_unitaryGroup_iff'.mp hk.1
    · exact Matrix.mem_unitaryGroup_iff'.mp hk'.1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInvStatement
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.offDiagBlockNorm_mul_invariant : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  first | exact @GlobalTheory.offDiagBlockNorm_cont_inv | exact GlobalTheory.offDiagBlockNorm_cont_inv | (intros; apply GlobalTheory.offDiagBlockNorm_cont_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevel
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.UJOffDiag

open Formalism.REAL

def sgn (e : Bool) : ℝ := if e then 1 else -1

def ind (e : Bool) : ℝ := if e then 1 else 0

lemma term_left (z : ℂ) (e : Bool) :
    star z * (if e then (1 : ℂ) else -1) * z = ((sgn e * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  cases e
  · rw [show star z * (if false = true then (1 : ℂ) else -1) * z = -(star z * z) by simp, h]
    simp [sgn]
  · rw [show star z * (if true = true then (1 : ℂ) else -1) * z = star z * z by simp, h]
    simp [sgn]

lemma term_right (z : ℂ) (e : Bool) :
    z * (if e then (1 : ℂ) else -1) * star z = ((sgn e * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [show z * (if e then (1 : ℂ) else -1) * star z = star z * (if e then (1 : ℂ) else -1) * z by ring]
  exact term_left z e

lemma col_id {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) (b : Fin n) :
    ∑ a, sgn (ε a) * ‖g a b‖ ^ 2 = sgn (ε b) := by
  unfold inUJ at hg
  have h := congrFun (congrFun hg b) b
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at h
  simp only [term_left] at h
  have h2 : ((∑ a, sgn (ε a) * ‖g a b‖ ^ 2 : ℝ) : ℂ) = ((sgn (ε b) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Matrix.diagonal_apply_eq]; cases ε b <;> simp [sgn]
  exact_mod_cast h2

lemma row_id {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) (a : Fin n) :
    ∑ b, sgn (ε b) * ‖g a b‖ ^ 2 = sgn (ε a) := by
  have h1 := (indefinite_unitary_inv_closed n ε g hg).1
  have hJ : g * Jm ε * gᴴ = Jm ε := by
    calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
          simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
      _ = Jm ε := by rw [h1, Matrix.one_mul]
  have h := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at h
  simp only [term_right] at h
  have h2 : ((∑ b, sgn (ε b) * ‖g a b‖ ^ 2 : ℝ) : ℂ) = ((sgn (ε a) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Matrix.diagonal_apply_eq]; cases ε a <;> simp [sgn]
  exact_mod_cast h2

end GlobalTheory.UJOffDiag

namespace GlobalTheory.UJOffDiag

open Formalism.REAL

lemma off_sum_eq {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 =
      ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖M a b‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun z : Fin n × Fin n => ε z.1 = true ∧ ε z.2 = false)
    (fun x => by simp) (fun z => ‖M z.1 z.2‖ ^ 2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  cases ε a <;> cases ε b <;> simp [ind]

lemma hs_eq {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    hs g = n + 4 * ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2 := by
  have key : ∀ a b, ‖g a b‖ ^ 2 = 4 * (ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
      (-(sgn (ε a) * ‖g a b‖ ^ 2) + 2 * (ind (ε a) * (sgn (ε b) * ‖g a b‖ ^ 2))) := by
    intro a b; cases ε a <;> cases ε b <;> simp [ind, sgn] <;> ring
  have hcol : ∑ a, ∑ b, sgn (ε a) * ‖g a b‖ ^ 2 = ∑ b, sgn (ε b) := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ => col_id ε g hg b
  have hrow : ∑ a, ind (ε a) * ∑ b, sgn (ε b) * ‖g a b‖ ^ 2 = ∑ a, ind (ε a) * sgn (ε a) :=
    Finset.sum_congr rfl fun a _ => by rw [row_id ε g hg a]
  have hn : ∑ a : Fin n, (-(sgn (ε a)) + 2 * (ind (ε a) * sgn (ε a))) = n := by
    rw [show (n : ℝ) = ∑ _a : Fin n, (1 : ℝ) by simp]
    exact Finset.sum_congr rfl fun a _ => by cases ε a <;> simp [ind, sgn] <;> norm_num
  calc hs g = ∑ a, ∑ b, (4 * (ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
      (-(sgn (ε a) * ‖g a b‖ ^ 2) + 2 * (ind (ε a) * (sgn (ε b) * ‖g a b‖ ^ 2)))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
    _ = 4 * (∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
        (-(∑ a, ∑ b, sgn (ε a) * ‖g a b‖ ^ 2) +
          2 * ∑ a, ind (ε a) * ∑ b, sgn (ε b) * ‖g a b‖ ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_neg_distrib]
    _ = n + 4 * ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2 := by
        rw [hcol, hrow, ← hn, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
        ring

end GlobalTheory.UJOffDiag

namespace GlobalTheory

open Formalism.REAL

theorem isCompact_offDiag_sublevel : ∀ (n : ℕ) (ε : Fin n → Bool) (C : ℝ),
    IsCompact {g : UJ ε | ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false},
      ‖(toM g) z.1.1 z.1.2‖ ^ 2 ≤ C} := by
  intro n ε C
  set F : Matrix (Fin n) (Fin n) ℂ → ℝ := fun M =>
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun z _ => (continuous_norm.comp (continuous_id.matrix_elem z.1.1 z.1.2)).pow 2
  have hK : IsCompact {M : Matrix (Fin n) (Fin n) ℂ | inUJ ε M ∧ F M ≤ C} := by
    refine IsCompact.of_isClosed_subset ((hermitian_small_ball n ε).1 (n + 4 * C)) ?_ ?_
    · exact (indefinite_unitary_closed n ε).inter (isClosed_le hFc continuous_const)
    · rintro M ⟨hM, hFM⟩
      refine ⟨hM, ?_⟩
      rw [UJOffDiag.hs_eq ε M hM, ← UJOffDiag.off_sum_eq]
      have : F M = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 := rfl
      linarith
  have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage hK
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevelStatement
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel : ∀ (n : ℕ) (ε : Fin n → Bool) (C : ℝ), IsCompact {g : UJ ε | ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 ≤ C} := by
  first | exact @GlobalTheory.isCompact_offDiag_sublevel | exact GlobalTheory.isCompact_offDiag_sublevel | (intros; apply GlobalTheory.isCompact_offDiag_sublevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicProperties
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section
namespace GlobalTheory.KSp.ScBasic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E]

end GlobalTheory.KSp.ScBasic
end

namespace GlobalTheory.KSp

open MeasureTheory Matrix in
private theorem sc_units_eq_mul_nabs_norm_rpow {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : Eˣ) :
    _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := by
  simp [_root_.GlobalTheory.KSp.sc, z.ne_zero]

open MeasureTheory Matrix in
private theorem rpow_natCast_div_two_sq {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x ^ ((m : ℝ) / 2)) ^ 2 = x ^ m := by
  rw [← Real.rpow_natCast (x ^ ((m : ℝ) / 2)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x m]
  congr 1
  push_cast
  ring

open MeasureTheory Matrix in
private theorem sc_zero' {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) : _root_.GlobalTheory.KSp.sc F χ m 0 = 0 := by
  simp [_root_.GlobalTheory.KSp.sc]

open MeasureTheory Matrix in
theorem _root_.GlobalTheory.KSp.sc_basic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : _root_.GlobalTheory.WeilM.IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : _root_.GlobalTheory.WeilM.ResEtaPow (R := F) ⊥ χ m), _root_.GlobalTheory.KSp.sc F χ m 1 = 1 ∧ (∀ z z' : E, _root_.GlobalTheory.KSp.sc F χ m (z * z') = _root_.GlobalTheory.KSp.sc F χ m z * _root_.GlobalTheory.KSp.sc F χ m z') ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖_root_.GlobalTheory.KSp.sc F χ m (z : E)‖ ^ 2 = _root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (c (z : E))⁻¹ * ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = _root_.GlobalTheory.KSp.sc F χ m (z : E)) ∧ (∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) = (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m ((z : E) * c (z : E)) = ((_root_.GlobalTheory.SplitWeil.nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hinj := hE.algebraMap_injective
  have hinv := hE.invol
  have hpos : ∀ t : Fˣ, 0 < _root_.GlobalTheory.SplitWeil.nabs F t :=
    _root_.GlobalTheory.SplitWeil.nabs_pos F
  have hmul := _root_.GlobalTheory.SplitWeil.nabs_mul F
  have hunit : ∀ z : Eˣ, _root_.GlobalTheory.KSp.sc F χ m (z : E) = (χ z : ℂ) *
      ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := fun z => sc_units_eq_mul_nabs_norm_rpow F χ m z
  have hnorm : ∀ z : Eˣ, algebraMap F E ((Units.map (Algebra.norm F : E →* F) z : Fˣ) : F) =
      (z : E) * c z := fun z => by
    simpa using hE.algebraMap_norm (z : E)
  have hNc : ∀ z : Eˣ, Units.map (Algebra.norm F : E →* F) (Units.map (c : E →* E) z) =
      Units.map (Algebra.norm F : E →* F) z := by
    intro z
    apply Units.ext
    apply hinj
    rw [hnorm, hnorm]
    simp [hinv, mul_comm]
  have hNa : ∀ t : Fˣ, Units.map (Algebra.norm F : E →* F) (Units.map (algebraMap F E : F →* E) t)
      = t * t := by
    intro t
    apply Units.ext
    apply hinj
    rw [hnorm]
    simp
  have hbase : ∀ t : Fˣ, _root_.GlobalTheory.KSp.sc F χ m (algebraMap F E t) =
      (_root_.GlobalTheory.KSp.sgn E t * (_root_.GlobalTheory.SplitWeil.nabs F t : ℝ)) ^ m := by
    intro t
    have h1 := hunit (Units.map (algebraMap F E : F →* E) t)
    simp only [Units.coe_map, MonoidHom.coe_coe] at h1
    rw [h1, hχ t, hNa, hmul, Real.mul_rpow (hpos t).le (hpos t).le, ← sq,
      rpow_natCast_div_two_sq (hpos t) m, mul_pow]
    simp only [_root_.GlobalTheory.KSp.sgn, bot_sup_eq]
    split_ifs with h₁ h₂ h₂ <;>
      first
        | (push_cast; ring1)
        | exact absurd (Subgroup.mem_sup_right h₂) h₁
        | exact absurd (by rwa [bot_sup_eq] at h₁) h₂
  refine ⟨?_, ?_, hunit, ?_, ?_, hbase, ?_⟩
  · simpa [_root_.GlobalTheory.SplitWeil.nabs_one] using hunit 1
  · intro z z'
    rcases eq_or_ne z 0 with rfl | hz
    · simp [sc_zero']
    rcases eq_or_ne z' 0 with rfl | hz'
    · simp [sc_zero']
    obtain ⟨u, rfl⟩ : ∃ u : Eˣ, (u : E) = z := ⟨Units.mk0 z hz, rfl⟩
    obtain ⟨u', rfl⟩ : ∃ u : Eˣ, (u : E) = z' := ⟨Units.mk0 z' hz', rfl⟩
    rw [← Units.val_mul, hunit, hunit, hunit, map_mul, map_mul, hmul,
      Real.mul_rpow (hpos _).le (hpos _).le]
    push_cast [Circle.coe_mul]
    ring
  · intro z
    rw [hunit, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (hpos _).le _), rpow_natCast_div_two_sq (hpos _) m]
  · intro z
    have h1 := hunit (Units.map (c : E →* E) z)⁻¹
    simp only [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe, map_inv] at h1
    have hs := hpos (Units.map (Algebra.norm F : E →* F) z)
    have habs_inv : ∀ t : Fˣ, _root_.GlobalTheory.SplitWeil.nabs F t⁻¹ =
        (_root_.GlobalTheory.SplitWeil.nabs F t)⁻¹ := fun t =>
      eq_inv_of_mul_eq_one_left (by rw [← hmul, inv_mul_cancel, _root_.GlobalTheory.SplitWeil.nabs_one])
    rw [h1, hNc, hunit,
      _root_.GlobalTheory.WeilM.ResEtaPow.map_conj (c := c) hE hχ z, inv_inv,
      habs_inv, Real.inv_rpow hs.le, ← rpow_natCast_div_two_sq hs m]
    have ha0 : ((_root_.GlobalTheory.SplitWeil.nabs F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hs _).ne'
    push_cast at ha0 ⊢
    field_simp
  · intro z
    have hz : Units.map (Algebra.norm F : E →* F) z ∈ (Units.map (Algebra.norm F : E →* F)).range :=
      ⟨z, rfl⟩
    rw [← hnorm, hbase]
    simp [_root_.GlobalTheory.KSp.sgn, hz]

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharacterAbsScalarBasicPropertiesStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (m : ℕ) (χ : Eˣ →* Circle) (_ : ResEtaPow (R := F) ⊥ χ m), sc F χ m 1 = 1 ∧ (∀ z z' : E, sc F χ m (z * z') = sc F χ m z * sc F χ m z') ∧ (∀ z : Eˣ, sc F χ m (z : E) = (χ z : ℂ) * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ, ‖sc F χ m (z : E)‖ ^ 2 = nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ, sc F χ m (c (z : E))⁻¹ * ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = sc F χ m (z : E)) ∧ (∀ t : Fˣ, sc F χ m (algebraMap F E t) = (sgn E t * (nabs F t : ℝ)) ^ m) ∧ ∀ z : Eˣ, sc F χ m ((z : E) * c (z : E)) = ((nabs F ((Units.map (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  first | exact @GlobalTheory.KSp.sc_basic | exact GlobalTheory.KSp.sc_basic | (intros; apply GlobalTheory.KSp.sc_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
namespace GlobalTheory.IntBall

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal Matrix

noncomputable section

abbrev Low (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}

def lowMat {r : ℕ} (w : Low r → ℂ) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  if h : b < a then w ⟨(a, b), h⟩ else if a = b then 1 else 0

def colGram {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) (k : Fin (q + 1)) : ℝ := ‖lminor (Mᴴ * M) k‖

def blkW {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : Matrix (Fin (r - 1)) (Fin (r - 1)) ℂ := fun i j =>
  if p0 = 1 then lowMat w ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ else lowMat w ⟨i, by omega⟩ ⟨j, by omega⟩

def gB {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : ℝ :=
  ∏ k : Fin (r - 1), colGram (blkW p0 w) k.castSucc ^ (-2 : ℤ)

def hB {r : ℕ} (p0 : ℕ) : (Low r → ℂ) → ℝ≥0∞ :=
  Set.indicator {w | ∀ p : Low r, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    fun w => ENNReal.ofReal (gB p0 w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def zOf (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : Low r → ℂ := fun p =>
  z (Fintype.equivFin (Ent X) ⟨τ, p⟩)

def bnd (X : Data E r) (z : V (nd X)) : ℝ := ∏ τ, gB X.p0 (zOf X z τ)

theorem nmat_eq_lowMat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (Matrix.of (nmat X z τ) : Matrix (Fin r) (Fin r) ℂ) = lowMat (zOf X z τ) := by
  ext a b
  simp only [Matrix.of_apply, nmat, lowMat, zOf]

end

end GlobalTheory.IntBall
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichCharts
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

theorem perCl_injective (K : Charts F) (hK : K.Rich) (per per' : Λ →+ Hol F.V)
    (h : K.perCl per = K.perCl per') : per = per' := by
  obtain ⟨G, hG⟩ := (H1.mk_eq_mk (F := K.Oc)).1 h

  have hd : ∀ (T T' : K.Obj) (φ : T ⟶ T'), G T' - φ.φ (G T) =
      algebraMap (Hol F.V) T'.C (per φ.deg) - algebraMap (Hol F.V) T'.C (per' φ.deg) := by
    intro T T' φ
    have := congrFun (congrFun (congrFun hG T) T') φ
    exact this

  have h0 : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T) := by
    intro T T' φ hφ
    have := hd T T' φ
    simp only [hφ, map_zero, sub_zero] at this
    exact sub_eq_zero.1 this
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible K hK G h0

  have hv : ∀ (T T' : K.Obj) (φ : T ⟶ T'), algebraMap (Hol F.V) T'.C (per φ.deg - per' φ.deg) = 0 := by
    intro T T' φ
    have := hd T T' φ
    rw [hp T, hp T', AlgHom.commutes, sub_self] at this
    exact ((algebraMap (Hol F.V) T'.C).map_sub (per φ.deg) (per' φ.deg)).trans this.symm
  ext l : 1
  rw [← sub_eq_zero]
  refine GlobalTheory.T.parameter_function_eq_zero_of_composable K hK l 0 (per l - per' l) fun k k' k'' e e' ↦ ?_
  have h1 : K.cst k' (per l - per' l) = 0 := hv _ _ (ptHom (K.triv k') e)
  rw [← sh_cst e' (per l - per' l), h1, map_zero]

end GlobalTheory.AnPer.Charts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodClass_injective_of_rich_charts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ per per' : Λ →+ Hol F.V, K.perCl per = K.perCl per' → per = per' := by
  first | exact @GlobalTheory.AnPer.Charts.perCl_injective | exact GlobalTheory.AnPer.Charts.perCl_injective | (intros; apply GlobalTheory.AnPer.Charts.perCl_injective <;> assumption)
end
end
