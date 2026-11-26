module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactUnitHolds

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphStarU
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Eig

def SphStarU : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w)),
  GlobalTheory.SmGL.IsUnitarisable σ.ρ → Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1 → ∀ h₁ h₂, IsHecke (KL n w) h₁ → IsHecke (KL n w) h₂ →
    twTr σ.ρ (KL n w) (KL n w) (lconv h₁ h₂) LinearMap.id =
      twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id * twTr σ.ρ (KL n w) (KL n w) h₂ LinearMap.id ∧
    twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id = starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) ∧
    twTr σ.ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1

end PositivityTheory.Rg.BcB.F.Eig

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.SphStarUPlug
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.SphStar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseDoubleCosetNonsplit
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseDoubleCosetNonsplit
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG GlobalTheory.PRep
open GlobalTheory.CuspRep Formalism.BasicNotions
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.InvDoubleCoset

section Generic

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

def wJ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) : GL (Fin n) L :=
  ⟨antiJ L n, antiJ L n, GlobalTheory.UnitarySwap.antiJ_mul_self, GlobalTheory.UnitarySwap.antiJ_mul_self⟩

theorem cT_antiJ (σ : L →+* L) : cT σ (antiJ L n) = antiJ L n := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, antiJ]
  by_cases h : i.val + j.val + 1 = n
  · rw [if_pos h, if_pos (by omega)]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

theorem wJ_mem_GU (σ : L →+* L) : wJ L n ∈ GU σ n := by
  change cT σ (antiJ L n) * antiJ L n * antiJ L n = antiJ L n
  rw [cT_antiJ, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]

theorem wJ_mem_GLint (O : Subring L) : wJ L n ∈ GLint (Fin n) O := by
  have h : ∀ i j, antiJ L n i j ∈ O := fun i j => by
    simp only [antiJ]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  exact GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨h, h⟩

theorem wJ_conj_diag {σ : L →+* L} {ϖ : L} (hϖ : σ ϖ = ϖ) (d : Fin n → ℤ) (t : GU σ n)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) : wJ L n * t.1 * wJ L n = (t.1)⁻¹ := by
  have h0 : cT σ t.1.1 * antiJ L n * t.1.1 = antiJ L n := t.2
  have hc : cT σ t.1.1 = t.1.1 := by
    rw [ht]
    ext i j
    by_cases h : i = j
    · subst h
      simp [cT, map_zpow₀, hϖ]
    · simp [cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [hc] at h0
  refine eq_inv_of_mul_eq_one_left (Units.ext ?_)
  change antiJ L n * t.1.1 * antiJ L n * t.1.1 = 1
  calc antiJ L n * t.1.1 * antiJ L n * t.1.1 = antiJ L n * (t.1.1 * antiJ L n * t.1.1) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h0, GlobalTheory.UnitarySwap.antiJ_mul_self]

end Generic

theorem inv_mem_doubleCoset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (g : UL n w),
      ∃ k₁ ∈ KL n w, ∃ k₂ ∈ KL n w, g⁻¹ = k₁ * g * k₂ := by
  intro E _ _ _ hU w hw n g
  obtain ⟨-, -, -, hns, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, -⟩, -⟩ := hns hw
  obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hUI (B := 1) (one_mem _) (cT_one _)
  have hb' : cT (cj w) b.val * b.val = antiJ _ n := by simpa using hb
  have hconj : ∀ x : GLw n w, b * x * b⁻¹ ∈ UL n w ↔ x ∈ UJ (cj w) (antiJ _ n) := fun x => by
    rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
    exact GlobalTheory.CompanionTheory.UnitaryWitt.conj_mem_UJ_one_iff _ b x hb'
  have hback : b⁻¹ * g.1 * b ∈ UJ (cj w) (antiJ _ n) :=
    (hconj _).1 (by rw [show b * (b⁻¹ * g.1 * b) * b⁻¹ = g.1 by group]; exact g.2)
  have hbi := (GlobalTheory.LFun.KGL w (n := n)).inv_mem hbK
  have hO : Ov E w = intL (w.adicCompletion E) := Subring.ext fun _ => Iff.rfl
  have hKU : ∀ k ∈ KU (cj w) n, (k.1 : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) := fun k hk => by
    have h : k.1 ∈ intPts (intL (w.adicCompletion E)).subtype (GU (cj w) n) := Subgroup.mem_subgroupOf.1 hk
    show k.1 ∈ (bc (Ov E w).subtype).range
    rw [hO]
    exact (Subgroup.mem_inf.1 h).2
  obtain ⟨d, t, ht, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.ChainOnto.CayleyVac.exists_cartanU hUI ⟨_, hback⟩
  have e' : b⁻¹ * g.1 * b = k₁.1 * t.1 * k₂.1 := congrArg Subtype.val e
  have hinv : (t.1)⁻¹ = wJ _ n * t.1 * wJ _ n := (wJ_conj_diag hUI.2.2.1 d t ht).symm

  set c : GLw n w := (k₂.1 : GLw n w)⁻¹ * wJ _ n * (k₁.1 : GLw n w)⁻¹ with hc
  have hcU : c ∈ UJ (cj w) (antiJ _ n) :=
    mul_mem (mul_mem (inv_mem k₂.2) (wJ_mem_GU _)) (inv_mem k₁.2)
  have hcK : c ∈ GlobalTheory.LFun.KGL w (n := n) :=
    mul_mem (mul_mem (inv_mem (hKU k₂ hk₂)) (wJ_mem_GLint _)) (inv_mem (hKU k₁ hk₁))
  have hx : b * c * b⁻¹ ∈ UL n w := (hconj _).2 hcU
  have hxK : (⟨b * c * b⁻¹, hx⟩ : UL n w) ∈ KL n w :=
    Subgroup.mem_subgroupOf.2 (mul_mem (mul_mem hbK hcK) hbi)
  refine ⟨_, hxK, _, hxK, Subtype.ext ?_⟩
  show (g.1)⁻¹ = b * c * b⁻¹ * g.1 * (b * c * b⁻¹)
  have hg : g.1 = b * (k₁.1 * t.1 * k₂.1) * b⁻¹ := by
    rw [← e']
    group
  have hti : (k₁.1 * t.1 * k₂.1 : GLw n w)⁻¹ = c * (k₁.1 * t.1 * k₂.1) * c := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, hinv, hc]
    group
  calc (g.1)⁻¹ = b * (k₁.1 * t.1 * k₂.1 : GLw n w)⁻¹ * b⁻¹ := by
        rw [hg]
        group
    _ = b * c * b⁻¹ * g.1 * (b * c * b⁻¹) := by
        rw [hti, hg]
        group

end GlobalTheory.CompanionTheory.InvDoubleCoset
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseDoubleCosetNonsplitStatement
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_double_coset_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (g : UL n w), ∃ k₁ ∈ KL n w, ∃ k₂ ∈ KL n w, g⁻¹ = k₁ * g * k₂ := by
  first | exact @GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset | exact GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset | (intros; apply GlobalTheory.CompanionTheory.InvDoubleCoset.inv_mem_doubleCoset <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.FinrankFixedEqOne
noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.Rg.BcB.F.EigA

section Sums

theorem out_mk_inv {H M : Type} [Group H] (A : Subgroup H) (F : H → M) (hF : ∀ x, ∀ a ∈ A, F (x * a) = F x)
    (y : H) : F ((y : H ⧸ A).out) = F y := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A y
  rw [ha, hF _ _ a.2]

end Sums

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  change (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2


def GelPair (K : Subgroup G) : Prop :=
  (∀ g : G, (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) ∧
    ∃ τ : G → G, (∀ a b, τ (a * b) = τ b * τ a) ∧ (∀ a, τ (τ a) = a) ∧
      (∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) ∧ ∀ k ∈ K, τ k ∈ K

end PositivityTheory.Rg.BcB.F.EigA

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.SphOne
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.EigA

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_conj_KL_ne_zero (n : ℕ) (w : Pl E) (g : UL n w) :
    ((KL n w).map (MulAut.conj g).toMonoidHom).relIndex (KL n w) ≠ 0 := by
  have hK : IsCompact (KL n w : Set (UL n w)) := GlobalTheory.LocFinU.isCompact_KL n w
  have hKo : IsOpen (KL n w : Set (UL n w)) := GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w
  have hH : IsOpen (((KL n w).map (MulAut.conj g).toMonoidHom : Subgroup (UL n w)) : Set (UL n w)) := by
    rw [GlobalTheory.LocFinU.conj_map_eq]
    exact ((Homeomorph.mulLeft g).trans (Homeomorph.mulRight g⁻¹)).isOpenMap _ hKo
  exact GlobalTheory.CompanionTheory.IwLevels.relIndex_ne_zero hH hK

theorem gelPair_split (n : ℕ) (w : Pl E) (hw : IsSplitAt w) : GelPair (KL n w) := by
  have hmem : ∀ x : GLw n w, x ∈ UL n w := fun x => by
    have h : UL n w = ⊤ := if_pos hw
    rw [h]
    exact Subgroup.mem_top x
  refine ⟨relIndex_conj_KL_ne_zero n w, fun g => ⟨Formalism.UG.P.heckecomm_tr g.1, hmem _⟩, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact Subtype.ext (Formalism.UG.P.heckecomm_tr_mul a.1 b.1)
  · intro a
    exact Subtype.ext (Formalism.UG.P.heckecomm_tr_tr a.1)
  · intro g
    obtain ⟨a, b, e⟩ := Formalism.UG.P.heckecomm_tr_dc Formalism.UG.Final.CartanDecomp E w n g.1
    exact ⟨⟨a, hmem _⟩, Subgroup.mem_subgroupOf.2 a.2, ⟨b, hmem _⟩, Subgroup.mem_subgroupOf.2 b.2, Subtype.ext e⟩
  · intro k hk
    exact Subgroup.mem_subgroupOf.2 (Formalism.UG.P.heckecomm_tr_mem (Ov E w) k.1 (Subgroup.mem_subgroupOf.1 hk))

theorem gelPair_inert (hE : Unr E) (n : ℕ) (w : Pl E) (hw : ¬ IsSplitAt w) : GelPair (KL n w) :=
  ⟨relIndex_conj_KL_ne_zero n w, fun g => g⁻¹, fun a b => mul_inv_rev a b, fun a => inv_inv a,
    fun g => GlobalTheory.T.inverse_double_coset_nonsplit E hE w hw n g, fun _ hk => (KL n w).inv_mem hk⟩

theorem gelPair_KL (hE : Unr E) (n : ℕ) (w : Pl E) : GelPair (KL n w) := by
  by_cases hw : IsSplitAt w
  · exact gelPair_split n w hw
  · exact gelPair_inert hE n w hw

end PositivityTheory.Rg.BcB.F.EigA

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FixedSpaceRankOne.TraceMulOfFinrankOne
noncomputable section

open scoped Pointwise

namespace PositivityTheory.Rg.BcB.F.EigA

section Inv

variable {G : Type} [Group G]

theorem finsum_inv_eq {K : Subgroup G} (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (hK : ∀ k ∈ K, τ k ∈ K)
    {M : Type} [AddCommMonoid M] (F : G → M) (hF : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ x, F (k₁ * x * k₂) = F x) :
    ∑ᶠ q : G ⧸ K, F (q.out)⁻¹ = ∑ᶠ q : G ⧸ K, F q.out := by
  have hone : τ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.mp h.symm)
  have hτinv : ∀ a, τ a⁻¹ = (τ a)⁻¹ := fun a => by
    have h := hmul a a⁻¹
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  let σ : G → G := fun x => τ x⁻¹
  have hσmul : ∀ a b, σ (a * b) = σ a * σ b := by
    intro a b
    simp only [σ, mul_inv_rev, hmul]
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    simp only [σ, hτinv, inv_inv, hinv]
  have hσK : ∀ k ∈ K, σ k ∈ K := fun k hk => hK _ (K.inv_mem hk)
  have hFτ : ∀ x, F (τ x) = F x := fun x => by
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hdc x
    rw [e, hF _ h₁ _ h₂]
  have hFr : ∀ x, ∀ k ∈ K, F (x * k) = F x := fun x k hk => by
    simpa using hF 1 K.one_mem k hk x
  let s : G ⧸ K → G ⧸ K := fun q => ((σ q.out : G) : G ⧸ K)
  have hs : ∀ q, s (s q) = q := by
    intro q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (σ q.out)
    show ((σ ((σ q.out : G) : G ⧸ K).out : G) : G ⧸ K) = q
    rw [hk, hσmul, hσσ, QuotientGroup.mk_mul_of_mem _ (hσK _ k.2), QuotientGroup.out_eq']
  let e : G ⧸ K ≃ G ⧸ K := ⟨s, s, hs, hs⟩
  conv_rhs => rw [← finsum_comp_equiv e]
  refine finsum_congr fun q => ?_
  show F (q.out)⁻¹ = F ((σ q.out : G) : G ⧸ K).out
  rw [out_mk_inv K F hFr]
  show F (q.out)⁻¹ = F (τ (q.out)⁻¹)
  rw [hFτ]

end Inv

section Top

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_support_quot (K : Subgroup G) (hK : IsOpen (K : Set G)) {M : Type} [Zero M] [TopologicalSpace M]
    (f : G → M) (hf : HasCompactSupport f) : {q : G ⧸ K | f q.out ≠ 0}.Finite := by
  obtain ⟨s, hs⟩ := hf.isCompact.elim_finite_subcover (fun x : tsupport f => (x : G) • (K : Set G))
    (fun x => hK.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K.one_mem, mul_one x⟩⟩)
  refine (s.finite_toSet.image (fun i : tsupport f => ((i : G) : G ⧸ K))).subset ?_
  intro q hq
  have hx : q.out ∈ tsupport f := subset_tsupport _ hq
  have h2 := hs hx
  simp only [Set.mem_iUnion] at h2
  obtain ⟨i, hi, k, hk, hik⟩ := h2
  refine ⟨i, hi, ?_⟩
  show ((i : G) : G ⧸ K) = q
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [← hik]
  exact (QuotientGroup.mk_mul_of_mem (i : G) hk).symm

end Top

section Line

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem end_eq_trace_smul (h : Module.finrank ℂ M = 1) (f : Module.End ℂ M) : f = LinearMap.trace ℂ M f • 1 := by
  haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h
  let b : Module.Basis (Fin 1) ℂ M := Module.finBasisOfFinrankEq ℂ M h
  apply b.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rw [LinearMap.trace_eq_matrix_trace ℂ b f, Matrix.trace_fin_one, LinearMap.toMatrix_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  conv_lhs => rw [← b.sum_repr (f (b 0))]
  rw [Fin.sum_univ_one]

theorem trace_mul_of_finrank_one (h : Module.finrank ℂ M = 1) (f g : Module.End ℂ M) :
    LinearMap.trace ℂ M (f * g) = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by
  haveI : FiniteDimensional ℂ M := Module.finite_of_finrank_eq_succ h
  have hf := end_eq_trace_smul h f
  have hg := end_eq_trace_smul h g
  calc LinearMap.trace ℂ M (f * g)
      = LinearMap.trace ℂ M ((LinearMap.trace ℂ M f • 1) * (LinearMap.trace ℂ M g • 1)) := by
        rw [← hf, ← hg]
    _ = LinearMap.trace ℂ M f * LinearMap.trace ℂ M g := by
        rw [smul_mul_smul_comm, one_mul, map_smul, LinearMap.trace_one, h, smul_eq_mul, Nat.cast_one, mul_one]

end Line

end PositivityTheory.Rg.BcB.F.EigA

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.EigA

open PositivityTheory.Rg.BcB.F.Eig (locOp lconv lstar LocAlg SphStarU)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem levOp_KL_apply {n : ℕ} {w : Pl E} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (UL n w) V) (f : UL n w → ℂ) (S : Finset (UL n w ⧸ KL n w))
    (hS : ∀ q : UL n w ⧸ KL n w, f q.out ≠ 0 → q ∈ S) (v : V) :
    levOp ρ (KL n w) (KL n w) f LinearMap.id v = ∑ q ∈ S, f q.out • ρ q.out v := by
  have hsub : Function.support (fun q : UL n w ⧸ KL n w => f q.out • (ρ q.out ∘ₗ LinearMap.id)) ⊆ ↑S := by
    intro q hq
    refine Finset.mem_coe.2 (hS q fun h0 => ?_)
    apply Function.mem_support.1 hq
    simp only [h0, zero_smul]
  rw [levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul,
    finsum_eq_sum_of_support_subset _ hsub, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply]

theorem sphStar : LocAlg → SphStarU := by
  intro hLA E _ _ _ hE n w σ hU hrank h₁ h₂ hh₁ hh₂
  have hlev : IsLevel (MonoidHom.id (UL n w)) (KL n w) (KL n w) :=
    ⟨GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w, le_rfl, fun k hk => hk⟩
  have LA := fun f₁ f₂ (hf₁ : IsHecke (KL n w) f₁) (hf₂ : IsHecke (KL n w) f₂) =>
    hLA E n w σ (KL n w) hlev f₁ f₂ hf₁ hf₂
  obtain ⟨tr1, app1, hconv, hstar, hmul, -, -, -⟩ := LA h₁ h₂ hh₁ hh₂
  obtain ⟨tr2, -⟩ := LA h₂ h₁ hh₂ hh₁
  obtain ⟨trc, -⟩ := LA (lconv h₁ h₂) h₁ hconv hh₁
  obtain ⟨trs, apps, -⟩ := LA (lstar h₁) h₁ hstar hh₁
  refine ⟨?_, ?_, ?_⟩
  · rw [trc, hmul, trace_mul_of_finrank_one hrank, ← tr1, ← tr2]
  · obtain ⟨B, hBh, hBpos, hBinv⟩ := hU
    haveI : Nontrivial (fixed σ.ρ (KL n w)) := Module.nontrivial_of_finrank_eq_succ hrank
    obtain ⟨v, hv0⟩ := exists_ne (0 : fixed σ.ρ (KL n w))
    have hvfix := mem_fixed_iff.1 v.2
    let φ : UL n w → ℂ := fun x => B (σ.ρ x v) v
    have key : ∀ f, IsHecke (KL n w) f →
        twTr σ.ρ (KL n w) (KL n w) f LinearMap.id = LinearMap.trace ℂ _ (locOp σ (KL n w) f) →
        (∀ u : fixed σ.ρ (KL n w), (locOp σ (KL n w) f u).1 = levOp σ.ρ (KL n w) (KL n w) f LinearMap.id u.1) →
        twTr σ.ρ (KL n w) (KL n w) f LinearMap.id * B v v = ∑ᶠ q : UL n w ⧸ KL n w, f q.out * φ q.out := by
      intro f hf htr happ
      have hfin := finite_support_quot (KL n w) (GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w) f hf.1
      have hS : ∀ q : UL n w ⧸ KL n w, f q.out ≠ 0 → q ∈ hfin.toFinset := fun q hq => hfin.mem_toFinset.2 hq
      have hline : locOp σ (KL n w) f v = twTr σ.ρ (KL n w) (KL n w) f LinearMap.id • v := by
        rw [htr]
        conv_lhs => rw [end_eq_trace_smul hrank (locOp σ (KL n w) f)]
        rfl
      have h1 : levOp σ.ρ (KL n w) (KL n w) f LinearMap.id v.1 = twTr σ.ρ (KL n w) (KL n w) f LinearMap.id • v.1 := by
        rw [← happ, hline]
        rfl
      rw [levOp_KL_apply σ.ρ f hfin.toFinset hS] at h1
      have h2 := congrArg (fun x => B x v.1) h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h2
      have hsub : Function.support (fun q : UL n w ⧸ KL n w => f q.out * φ q.out) ⊆ ↑hfin.toFinset := by
        intro q hq
        exact Finset.mem_coe.2 (hS q (left_ne_zero_of_mul (Function.mem_support.1 hq)))
      rw [← h2, finsum_eq_sum_of_support_subset _ hsub]
    have hφ : ∀ x, starRingEnd ℂ (φ x) = φ x⁻¹ := by
      intro x
      show starRingEnd ℂ (B (σ.ρ x v) v) = B (σ.ρ x⁻¹ v) v
      rw [← hBh, ← hBinv x⁻¹ (v : σ.V) (σ.ρ x v), ← Module.End.mul_apply (σ.ρ x⁻¹) (σ.ρ x), ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    have hφbi : ∀ k₁ ∈ KL n w, ∀ k₂ ∈ KL n w, ∀ x, φ (k₁ * x * k₂) = φ x := by
      intro k₁ hk₁ k₂ hk₂ x
      show B (σ.ρ (k₁ * x * k₂) v) v = B (σ.ρ x v) v
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hvfix k₂ hk₂,
        ← hBinv k₁⁻¹ (σ.ρ k₁ (σ.ρ x v)) (v : σ.V), hvfix _ ((KL n w).inv_mem hk₁),
        ← Module.End.mul_apply (σ.ρ k₁⁻¹) (σ.ρ k₁), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    let F : UL n w → ℂ := fun x => starRingEnd ℂ (h₁ x) * φ x⁻¹
    have hF : ∀ k₁ ∈ KL n w, ∀ k₂ ∈ KL n w, ∀ x, F (k₁ * x * k₂) = F x := by
      intro k₁ hk₁ k₂ hk₂ x
      show starRingEnd ℂ (h₁ (k₁ * x * k₂)) * φ (k₁ * x * k₂)⁻¹ = starRingEnd ℂ (h₁ x) * φ x⁻¹
      rw [(hh₁.2 k₂ hk₂ _).2, mul_assoc, (hh₁.2 k₁ hk₁ _).1, _root_.mul_inv_rev, _root_.mul_inv_rev,
        hφbi _ ((KL n w).inv_mem hk₂) _ ((KL n w).inv_mem hk₁)]
    have eqL := key h₁ hh₁ tr1 app1
    have eqμ := key (lstar h₁) hstar trs apps
    have hBvv : starRingEnd ℂ (B v v) = B v v := (hBh v v).symm
    have hBne : B v v ≠ 0 := by
      intro h
      have := hBpos (v : σ.V) (fun h0 => hv0 (Subtype.ext h0))
      rw [h] at this
      simp at this
    have hfin1 := finite_support_quot (KL n w) (GlobalTheory.CompanionTheory.IwLevels.isOpen_KL n w) h₁ hh₁.1
    have hsupp : (Function.support fun q : UL n w ⧸ KL n w => h₁ q.out * φ q.out).Finite :=
      hfin1.subset fun q hq => left_ne_zero_of_mul (Function.mem_support.1 hq)
    have eqc : starRingEnd ℂ (twTr σ.ρ (KL n w) (KL n w) h₁ LinearMap.id) * B v v =
        ∑ᶠ q : UL n w ⧸ KL n w, F q.out := by
      have h := congrArg (starRingEnd ℂ) eqL
      rw [map_mul, hBvv, map_finsum _ hsupp] at h
      rw [h]
      refine finsum_congr fun q => ?_
      simp only [map_mul, hφ, F]
    have eqμ' : twTr σ.ρ (KL n w) (KL n w) (lstar h₁) LinearMap.id * B v v =
        ∑ᶠ q : UL n w ⧸ KL n w, F (q.out)⁻¹ := by
      rw [eqμ]
      refine finsum_congr fun q => ?_
      simp only [F, lstar, inv_inv]
    obtain ⟨-, τ, hmulτ, hinvτ, hdcτ, hKτ⟩ := gelPair_KL hE n w
    have heq := finsum_inv_eq τ hmulτ hinvτ hdcτ hKτ F hF
    rw [← eqμ', ← eqc] at heq
    exact mul_right_cancel₀ hBne heq
  · have h := (GlobalTheory.T.twistedTrace_indicator_level_localUnitary E n w (KL n w) hlev σ).2.2.1
    rw [h, Subgroup.relIndex_self, hrank]
    simp

end PositivityTheory.Rg.BcB.F.EigA

end
end

namespace PositivityTheory.Rg.BcB.F.Fok

theorem sphStarU : PositivityTheory.Rg.BcB.F.Eig.SphStarU := PositivityTheory.Rg.BcB.F.EigA.sphStar GlobalTheory.T.local_algebra_holds

end PositivityTheory.Rg.BcB.F.Fok
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SphericalHeckeUnitary.PuSphHecke
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.U.UU

open PositivityTheory.Rg.BcB.F.Eig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem pu_hz {w : Pl E} (K : Subgroup (UL n w)) : IsHecke K (0 : UL n w → ℂ) :=
  ⟨HasCompactSupport.zero, fun _ _ _ => ⟨rfl, rfl⟩⟩

theorem pu_lev {S : Set (Pl E)} {B : Finset (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} (hB : LevelOff S B K')
    (w : Pl E) (hw : w ∉ B) : IsLevel (MonoidHom.id _) (KL n w) (KL n w) := by
  have h := hB.2.1.1 w
  rw [hB.2.2 w hw] at h
  exact h

theorem uAdjOfU : DiagAlg → LocAlg → SphOne → CompUnit → SphStarU → UAdj := by
  intro hD hL h1 hC hS E _ _ _ hE n S lam K' F B g R hB x hx
  rcases x with c | ⟨w0, h⟩
  · refine ⟨trivial, ?_⟩
    unfold UMod.op
    rw [(hD _ _ R.blk _ 0 0).2.2.2]
    rfl
  · obtain ⟨hw, hwB, hh⟩ := hx
    have hlev := pu_lev hB w0 hwB
    refine ⟨⟨hw, hwB, (hL E n w0 (SmIrr.triv _) (KL n w0) hlev h h hh hh).2.2.2.1⟩, ?_⟩
    unfold UMod.op
    rw [(hD _ _ R.blk _ 0 0).2.2.2]
    congr 1
    funext i
    exact (hS E hE n w0 (F.σ i w0) (hC E n (F.π i) (F.comp i).1 w0 _ ((F.comp i).2.2.2 w0 hw).1)
      (sph_line h1 hE F hB i w0 hw hwB) h h hh hh).2.1

section Word

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  {F : UFam S lam K'} {B : Finset (Pl E)}

theorem pu_sph_inl (c : ℂ) (l : List (UGen E n)) (w : Pl E) : UGen.sph (Sum.inl c :: l) w = UGen.sph l w := rfl

theorem pu_sph_inr (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) (w : Pl E) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w = if hw : w0 = w then lconv (hw ▸ h) (UGen.sph l w) else UGen.sph l w := rfl

theorem pu_sph_self (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w0 = lconv h (UGen.sph l w0) := by
  rw [pu_sph_inr, dite_eq_left rfl]

theorem pu_sph_ne (w0 : Pl E) (h : UL n w0 → ℂ) (l : List (UGen E n)) (w : Pl E) (hw : w0 ≠ w) :
    UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w = UGen.sph l w := by
  rw [pu_sph_inr, dite_eq_right hw]

def pu_pls (l : List (UGen E n)) : Finset (Pl E) :=
  (l.filterMap fun x => Sum.elim (fun _ => none) (fun y : Σ w : Pl E, UL n w → ℂ => some y.1) x).toFinset

theorem pu_sph_off (l : List (UGen E n)) (w : Pl E) (hw : w ∉ pu_pls l) :
    UGen.sph l w = (KL n w : Set (UL n w)).indicator 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hw' : w ∉ pu_pls l := fun h => hw (by
      unfold pu_pls at h ⊢
      rw [List.mem_toFinset, List.mem_filterMap] at h ⊢
      obtain ⟨a, ha, hb⟩ := h
      exact ⟨a, List.mem_cons_of_mem _ ha, hb⟩)
    rcases x with c | ⟨w0, h⟩
    · rw [pu_sph_inl, ih hw']
    · have hne : w0 ≠ w := by
        rintro rfl
        apply hw
        unfold pu_pls
        rw [List.mem_toFinset, List.mem_filterMap]
        exact ⟨_, List.mem_cons_self, rfl⟩
      rw [pu_sph_ne _ _ _ _ hne, ih hw']

theorem pu_sph_hecke (hL : LocAlg) (hB : LevelOff S B K') (l : List (UGen E n)) (hl : ∀ x ∈ l, x.Ok S B)
    (w : Pl E) (hw : w ∉ B) : IsHecke (KL n w) (UGen.sph l w) := by
  have hlev := pu_lev hB w hw
  induction l with
  | nil =>
    have h := (hL E n w (SmIrr.triv _) (KL n w) hlev 0 0 (pu_hz _) (pu_hz _)).2.2.2.2.2.2.1
    rw [Subgroup.relIndex_self, Nat.cast_one] at h
    exact h
  | cons x l ih =>
    have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    rcases x with c | ⟨w0, h⟩
    · rw [pu_sph_inl]; exact ih'
    · by_cases hw0 : w0 = w
      · subst hw0
        have hh : IsHecke (KL n w0) h := (hl _ List.mem_cons_self).2.2
        rw [pu_sph_self]
        exact (hL E n w0 (SmIrr.triv _) (KL n w0) hlev h _ hh ih').2.2.1
      · rw [pu_sph_ne _ _ _ _ hw0]; exact ih'

theorem pu_lpow (hL : LocAlg) (w : Pl E) (K : Subgroup (UL n w)) (hlev : IsLevel (MonoidHom.id _) (KL n w) K)
    (g : UL n w → ℂ) (hg : IsHecke K g) (σ : SmIrr (UL n w)) (k : ℕ) :
    IsHecke K (lpow K g k) ∧ locOp σ K (lpow K g k) = locOp σ K g ^ k := by
  induction k with
  | zero =>
    have h := hL E n w σ K hlev g g hg hg
    exact ⟨h.2.2.2.2.2.2.1, by rw [pow_zero]; exact h.2.2.2.2.2.2.2⟩
  | succ k ih =>
    have h := hL E n w σ K hlev g _ hg ih.1
    refine ⟨h.2.2.1, ?_⟩
    show locOp σ K (lconv g (lpow K g k)) = _
    rw [h.2.2.2.2.1, ih.2, pow_succ']

end Word

section Word2

variable {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
  {F : UFam S lam K'} {B : Finset (Pl E)}

theorem pu_tw (h1 : SphOne) (hC : CompUnit) (hS : SphStarU) (hE : GlobalTheory.BCT.Unr E) (hB : LevelOff S B K') (i : F.ι)
    (w : Pl E) (hw : w ∈ S) (hwB : w ∉ B) (h₁ h₂ : UL n w → ℂ) (hh₁ : IsHecke (KL n w) h₁) (hh₂ : IsHecke (KL n w) h₂) :
    twTr (F.σ i w).ρ (KL n w) (KL n w) (lconv h₁ h₂) LinearMap.id =
      twTr (F.σ i w).ρ (KL n w) (KL n w) h₁ LinearMap.id * twTr (F.σ i w).ρ (KL n w) (KL n w) h₂ LinearMap.id ∧
    twTr (F.σ i w).ρ (KL n w) (KL n w) ((KL n w : Set (UL n w)).indicator 1) LinearMap.id = 1 := by
  have h := hS E hE n w (F.σ i w) (hC E n (F.π i) (F.comp i).1 w _ ((F.comp i).2.2.2 w hw).1)
    (sph_line h1 hE F hB i w hw hwB) h₁ h₂ hh₁ hh₂
  exact ⟨h.1, h.2.2⟩

theorem pu_supp (h1 : SphOne) (hC : CompUnit) (hS : SphStarU) (hE : GlobalTheory.BCT.Unr E) (hB : LevelOff S B K') (i : F.ι)
    (l : List (UGen E n)) :
    (S \ ↑B ∩ Function.mulSupport fun w => twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id).Finite := by
  refine (pu_pls l).finite_toSet.subset fun w hw => ?_
  obtain ⟨⟨hwS, hwB⟩, hne⟩ := hw
  by_contra hp
  apply hne
  show twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id = 1
  rw [pu_sph_off l w hp]
  exact (pu_tw h1 hC hS hE hB i w hwS hwB 0 0 (pu_hz _) (pu_hz _)).2

theorem pu_prod (hL : LocAlg) (h1 : SphOne) (hC : CompUnit) (hS : SphStarU) (hE : GlobalTheory.BCT.Unr E) (hB : LevelOff S B K')
    (i : F.ι) (l : List (UGen E n)) (hl : ∀ x ∈ l, x.Ok S B) :
    (l.map fun x => x.p F i).prod =
      UGen.sc l * ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id := by
  induction l with
  | nil =>
    have h : ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph ([] : List (UGen E n)) w) LinearMap.id = 1 :=
      (finprod_mem_congr (g := fun _ => (1 : ℂ)) rfl fun w (hw : w ∈ S \ (↑B : Set (Pl E))) =>
        (pu_tw h1 hC hS hE hB i w hw.1 hw.2 0 0 (pu_hz _) (pu_hz _)).2).trans (finprod_mem_one _)
    rw [h, mul_one]
    rfl
  | cons x l ih =>
    have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    rcases x with c | ⟨w0, h⟩
    · rw [List.map_cons, List.prod_cons, ih']
      show c * (UGen.sc l * _) = (c * UGen.sc l) * ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id
      rw [mul_assoc]
    · obtain ⟨hw0, hw0B, hh⟩ := hl _ List.mem_cons_self
      set t0 := twTr (F.σ i w0).ρ (KL n w0) (KL n w0) h LinearMap.id with ht0
      have hP : ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph (Sum.inr ⟨w0, h⟩ :: l) w) LinearMap.id =
          t0 * ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id := by
        rw [finprod_mem_congr (g := fun w => (if w = w0 then t0 else 1) *
          twTr (F.σ i w).ρ (KL n w) (KL n w) (UGen.sph l w) LinearMap.id) rfl ?_]
        · rw [finprod_mem_mul_distrib' ?_ (pu_supp h1 hC hS hE hB i l)]
          · congr 1
            rw [finprod_eq_single _ w0 (fun x hx => by simp [hx])]
            simp [show w0 ∈ S \ ↑B from ⟨hw0, hw0B⟩]
          · refine (Set.finite_singleton w0).subset fun w hw => ?_
            by_contra hne
            exact hw.2 (if_neg hne)
        · intro w hw
          rcases eq_or_ne w w0 with rfl | hne
          · rw [if_pos rfl, pu_sph_self]
            exact (pu_tw h1 hC hS hE hB i w hw.1 hw.2 h _ hh (pu_sph_hecke hL hB l (fun y hy => hl y
              (List.mem_cons_of_mem _ hy)) w hw.2)).1
          · rw [if_neg hne, one_mul, pu_sph_ne _ _ _ _ (Ne.symm hne)]
      rw [List.map_cons, List.prod_cons, ih']
      show t0 * (UGen.sc l * _) = (1 * UGen.sc l) * _
      rw [hP, one_mul, mul_left_comm]

theorem pu_opprod (hD : DiagAlg) {g : ∀ w : Pl E, UL n w → ℂ} (R : UMod F B g) (l : List (UGen E n)) :
    (l.map R.op).prod = diagOp R.blk (fun i => (l.map fun x => x.p F i).prod) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [(hD F.ι R.d R.blk 1 1 1).2.2.1, one_smul]
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih]
    unfold UMod.op
    rw [← (hD F.ι R.d R.blk _ _ 0).1]
    rfl

end Word2

theorem uWordOfU : DiagAlg → LocAlg → SphOne → CompUnit → SphStarU → UWord := by
  intro hD hL h1 hC hS E _ _ _ hE n S lam K' F B g R hB hg k l hl
  have hT : GlobalTheory.BCT.IsTest (KL n) K' (fam B K' g k l) := by
    refine ⟨fun w => ?_, ?_⟩
    · by_cases hw : w ∈ B
      · rw [fam, if_pos hw]
        exact (pu_lpow hL w (K' w) (hB.2.1.1 w) (g w) (hg w hw) (SmIrr.triv _) k).1
      · rw [fam, if_neg hw, hB.2.2 w hw]
        exact pu_sph_hecke hL hB l hl w hw
    · rw [Filter.eventually_cofinite]
      refine (B ∪ pu_pls l).finite_toSet.subset fun w hw => ?_
      by_contra hc
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hc
      exact hw (by rw [fam, if_neg hc.1, pu_sph_off l w hc.2])
  refine ⟨hT, fun hreg => ?_⟩
  have hloc : ∀ i, ∀ w ∈ B, locOp (F.σ i w) (K' w) (fam B K' g k l w) = locOp (F.σ i w) (K' w) (g w) ^ k :=
    fun i w hw => by
      rw [fam, if_pos hw]
      exact (pu_lpow hL w (K' w) (hB.2.1.1 w) (g w) (hg w hw) (F.σ i w) k).2
  have e1 := R.tr k _ hT hloc
  rw [F.tf _ hT hreg] at e1
  have e2 : (fun i => (l.map fun x => x.p F i).prod) = (fun _ => UGen.sc l) * fun i =>
      ∏ᶠ w ∈ S \ ↑B, twTr (F.σ i w).ρ (KL n w) (KL n w) (fam B K' g k l w) LinearMap.id := by
    funext i
    rw [Pi.mul_apply, pu_prod hL h1 hC hS hE hB i l hl]
    congr 1
    exact finprod_mem_congr rfl fun w hw => by rw [fam, if_neg (show w ∉ B from hw.2)]
  rw [pu_opprod hD R l, e2, (hD F.ι R.d R.blk (fun _ => UGen.sc l) _ 0).1, (hD F.ι R.d R.blk 0 0 (UGen.sc l)).2.2.1,
    smul_mul_assoc, one_mul, mul_smul_comm, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul, e1]

end PositivityTheory.Rg.BcB.F.U.UU

end
end

namespace PositivityTheory.Rg.BcB.F.U

theorem unitary_words_holds : UWord :=
  UU.uWordOfU GlobalTheory.T.diagonal_algebra_holds GlobalTheory.T.local_algebra_holds (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.T.local_algebra_holds) GlobalTheory.T.compact_unit_holds PositivityTheory.Rg.BcB.F.Fok.sphStarU

theorem unitary_adjoint_holds : UAdj :=
  UU.uAdjOfU GlobalTheory.T.diagonal_algebra_holds GlobalTheory.T.local_algebra_holds (GlobalTheory.T.spherical_one_of_local_algebra GlobalTheory.T.local_algebra_holds) GlobalTheory.T.compact_unit_holds PositivityTheory.Rg.BcB.F.Fok.sphStarU

end PositivityTheory.Rg.BcB.F.U
