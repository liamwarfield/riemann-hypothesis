module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierConstantAtZeroDifferentiableOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalingOpenSubgroupsFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootProdLinearFactorsLatticeFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLenChainAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLenChainAdd
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem relLen_chain_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ),
    RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  intro C _ v M _ _ X'' X' X r₁ r₂ h₂ h₁
  obtain ⟨n, b, b', A, hA, hrA⟩ := h₁
  obtain ⟨m, c, c', B, hB, hrB⟩ := h₂
  have hnm : n = m := by simpa using Fintype.card_congr (b'.indexEquiv c)
  subst m
  have le_of_basis : ∀ {Y Z : Submodule (Int0 v) M}
      (d : Basis (Fin n) (Int0 v) Y) (e : Basis (Fin n) (Int0 v) Z)
      (D : Matrix (Fin n) (Fin n) (Int0 v)),
      (∀ k, (e k : M) = ∑ i, D i k • (d i : M)) → Z ≤ Y := by
    intro Y Z d e D h x hx
    have hx' : (x : M) = ∑ k, e.repr ⟨x, hx⟩ k • (e k : M) := by
      have hh := congrArg Z.subtype (e.sum_repr ⟨x, hx⟩)
      rw [map_sum] at hh
      exact hh.symm
    rw [hx']
    exact Y.sum_mem fun k _ => Y.smul_mem _ (by
      rw [h k]
      exact Y.sum_mem fun i _ => Y.smul_mem _ (d i).2)
  have hle₁ : X' ≤ X := le_of_basis b b' A hA
  have hle₂ : X'' ≤ X' := le_of_basis c c' B hB
  have key : ∀ {Y Z : Submodule (Int0 v) M} (h : Z ≤ Y)
      (d : Basis (Fin n) (Int0 v) Y) (e : Basis (Fin n) (Int0 v) Z)
      (D : Matrix (Fin n) (Fin n) (Int0 v)),
      (∀ k, (e k : M) = ∑ i, D i k • (d i : M)) →
      LinearMap.toMatrix e d (Submodule.inclusion h) = D := by
    intro Y Z h d e D hD
    ext i k
    have hh : Submodule.inclusion h (e k) = ∑ i, D i k • d i := by
      apply Subtype.ext
      simpa using hD k
    rw [LinearMap.toMatrix_apply, hh]
    simp [Finsupp.single_apply]
  have hmat₁ := key hle₁ b b' A hA
  have hmat₂ := key hle₂ c c' B hB
  let D := LinearMap.toMatrix c' b (Submodule.inclusion (hle₂.trans hle₁))
  have hD : D = A * (b'.toMatrix c) * B := by
    have hc : Submodule.inclusion (hle₂.trans hle₁) =
        (Submodule.inclusion hle₁).comp (Submodule.inclusion hle₂) := by
      ext x; rfl
    dsimp [D]
    rw [hc, LinearMap.toMatrix_comp c' b' b, hmat₁]
    rw [← basis_toMatrix_mul_linearMap_toMatrix c' b' c (Submodule.inclusion hle₂), hmat₂, Matrix.mul_assoc]
  refine ⟨n, b, c', D, ?_, ?_⟩
  · intro k
    have hh := b.sum_repr (Submodule.inclusion (hle₂.trans hle₁) (c' k))
    have hh' := congrArg X.subtype hh
    rw [map_sum] at hh'
    simpa [D, LinearMap.toMatrix_apply] using hh'.symm
  · have hu : IsUnit (b'.toMatrix c).det := by
      letI := b'.invertibleToMatrix c
      exact Matrix.isUnit_det_of_invertible _
    rw [hD, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul,
      v.map_mul, v.map_mul, v_unit v hu, add_zero, hrA, hrB]
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLenChainAddStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relLen_trans_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ), RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  first | exact @GlobalTheory.relLen_chain_add | exact GlobalTheory.relLen_chain_add | (intros; apply GlobalTheory.relLen_chain_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeRelativeLengthOfSmulLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeRelativeLengthOfSmulLe
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.SubLen

theorem exists_relLen_of_smul_le (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M]
    (htf : ∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0)
    (X' X : Submodule (Int0 v) M) (hle : X' ≤ X) (hX : Module.Finite (Int0 v) X)
    (hX' : Module.Finite (Int0 v) X') (c : Int0 v) (hc : c ≠ 0) (hcX : ∀ x ∈ X, c • x ∈ X') :
    ∃ r : ℝ, RelLen v X' X r := by
  haveI tfX : Module.IsTorsionFree (Int0 v) X :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr (Subtype.ext ?_)
        have h' : r • (x : M) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
        exact htf r _ hr h'
  haveI tfX' : Module.IsTorsionFree (Int0 v) X' :=
    Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · refine Or.inr (Subtype.ext ?_)
        have h' : r • (x : M) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
        exact htf r _ hr h'
  haveI := hX
  haveI := hX'
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X)
  haveI := GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := X')
  let ι : X' →ₗ[Int0 v] X := Submodule.inclusion hle
  have hι : Function.Injective ι := Submodule.inclusion_injective hle
  let μ : X →ₗ[Int0 v] X' :=
    { toFun := fun x => ⟨c • (x : M), hcX x x.2⟩
      map_add' := fun x y => Subtype.ext (smul_add c (x : M) y)
      map_smul' := fun r x => Subtype.ext (by
        change c • (r • (x : M)) = r • (c • (x : M))
        exact smul_comm c r (x : M)) }
  have hμ : Function.Injective μ := by
    intro x y hxy
    have : c • ((x : M) - y) = 0 := by
      have h3 : c • (x : M) = c • (y : M) := congrArg Subtype.val hxy
      rw [smul_sub, h3, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (htf c _ hc this))
  have h1 : finrank (Int0 v) X' ≤ finrank (Int0 v) X := LinearMap.finrank_le_finrank_of_injective hι
  have h2 : finrank (Int0 v) X ≤ finrank (Int0 v) X' := LinearMap.finrank_le_finrank_of_injective hμ
  have heq : finrank (Int0 v) X' = finrank (Int0 v) X := le_antisymm h1 h2
  let b := Module.finBasis (Int0 v) X
  let b' := Module.finBasisOfFinrankEq (Int0 v) X' heq
  let A := LinearMap.toMatrix b' b ι
  have hA : ∀ k, (b' k : M) = ∑ i, A i k • (b i : M) := by
    intro k
    have e := b.sum_repr (ι (b' k))
    have e2 := congrArg (Submodule.subtype X) e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e2
    simp only [map_smul, Submodule.subtype_apply] at e2
    simpa [A, LinearMap.toMatrix_apply, ι] using e2.symm
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hw0
    have : ι (b'.equivFun.symm w) = 0 := by
      have := Matrix.toLin_toMatrix b' b ι
      rw [← this, Matrix.toLin_apply]
      simp only [Basis.equivFun_symm_apply, Basis.repr_sum_self]
      change ∑ x, (A.mulVec w) x • b x = 0
      simp [hw]
    have h4 := hι (this.trans (map_zero ι).symm)
    have h5 := congrArg b'.equivFun h4
    rw [LinearEquiv.apply_symm_apply, map_zero] at h5
    exact h5
  have hv : v (A.det : C) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact_mod_cast hdet
  exact ⟨(v (A.det : C)).untop hv, _, b, b', A, hA, (WithTop.coe_untop _ hv).symm⟩

end GlobalTheory.SubLen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeRelativeLengthOfSmulLeStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeRelativeLength_of_smul_le : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X' X : Submodule (Int0 v) M), X' ≤ X → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ c : Int0 v, c ≠ 0 → (∀ x ∈ X, c • x ∈ X') → ∃ r : ℝ, RelLen v X' X r := by
  first | exact @GlobalTheory.SubLen.exists_relLen_of_smul_le | exact GlobalTheory.SubLen.exists_relLen_of_smul_le | (intros; apply GlobalTheory.SubLen.exists_relLen_of_smul_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRelativeLengthSmulEqRankMulValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRelativeLengthSmulEqRankMulValuation
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory.ScalLen

theorem relLen_map_lsmul : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) →
    ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ),
      v (c : C) = r →
      RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  intro C _ v M _ _ htf X hX c r hr
  have hc : c ≠ 0 := by
    rintro rfl
    simp at hr
  have : Module.IsTorsionFree (Int0 v) X := ⟨fun s hs x y hxy => by
    have hs0 : s ≠ 0 := hs.ne_zero
    apply Subtype.ext
    have h1 : s • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      have := congrArg Subtype.val hxy
      simp only [Submodule.coe_smul] at this
      rw [this, sub_self]
    exact sub_eq_zero.1 (htf s _ hs0 h1)⟩
  have : ValuationRing (Int0 v) := by
    have hInt : Int0 v = v.toValuation.integer := by
      ext x
      rw [mem_addValuationIntegerRing_iff]
    rw [hInt]
    infer_instance
  have : Module.Free (Int0 v) X :=
    GlobalTheory.free_of_finite_of_isTorsionFree_of_valuationRing (R := Int0 v) (M := ↥X)
  set n := finrank (Int0 v) X with hn
  let b : Basis (Fin n) (Int0 v) X := Module.finBasis _ _
  let g : X →ₗ[Int0 v] M := (LinearMap.lsmul (Int0 v) M c).comp X.subtype
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have h1 : c • ((x : M) - (y : M)) = 0 := by
      rw [smul_sub]
      simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.lsmul_apply] at hxy
      rw [hxy, sub_self]
    exact sub_eq_zero.1 (htf c _ hc h1)
  have hrange : LinearMap.range g = X.map (LinearMap.lsmul (Int0 v) M c) := by
    simp only [g, LinearMap.range_comp, Submodule.range_subtype]
  let e : X ≃ₗ[Int0 v] X.map (LinearMap.lsmul (Int0 v) M c) :=
    (LinearEquiv.ofInjective g hg).trans (LinearEquiv.ofEq _ _ hrange)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.RelLen
  refine ⟨n, b, b.map e, Matrix.diagonal (fun _ => c), fun k => ?_, ?_⟩
  · simp only [Basis.map_apply, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Subring.coe_pow, AddValuation.map_pow, hr, ← WithTop.coe_nsmul, nsmul_eq_mul]

end GlobalTheory.ScalLen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRelativeLengthSmulEqRankMulValuationStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeRelativeLength_smul_eq_rank_mul_valuation : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type) [AddCommGroup M] [Module (Int0 v) M], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → ∀ (X : Submodule (Int0 v) M), Module.Finite (Int0 v) X → ∀ (c : Int0 v) (r : ℝ), v (c : C) = r → RelLen v (X.map (LinearMap.lsmul (Int0 v) M c)) X ((finrank (Int0 v) X : ℝ) * r) := by
  first | exact @GlobalTheory.ScalLen.relLen_map_lsmul | exact GlobalTheory.ScalLen.relLen_map_lsmul | (intros; apply GlobalTheory.ScalLen.relLen_map_lsmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandLengthIdentitiesOfRelativeLength
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

noncomputable section
namespace GlobalTheory.HerbLen

theorem relLen_nonneg {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {M : Type}
    [AddCommGroup M] [Module (Int0 v) M] {X' X : Submodule (Int0 v) M} {r : ℝ}
    (h : RelLen v X' X r) : 0 ≤ r := by
  obtain ⟨n, b, b', A, -, hr⟩ := h
  have h0 : (0 : WithTop ℝ) ≤ v (A.det : C) := (mem_addValuationIntegerRing_iff v _).1 A.det.2
  rw [hr] at h0
  exact_mod_cast h0

theorem addVal_prod {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (s : Finset ι) (f : ι → C) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, ih]

set_option maxHeartbeats 1000000 in
theorem herbrand_lengthIdentities_auxiliary_bound (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type)
    [Fintype S] [DecidableEq S] (a : S → Int0 v) (ha : Function.Injective a) (N : ℕ)
    (Fil : Submodule (RS a) (Fin N → RS a))
    (hsat : ∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) (τ : S) (r : ℝ)
    (hr : (r : WithTop ℝ) = yExp v a Fil τ)
    (hlen : RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ))
      ((preEig a Fil τ).map (comp a N τ)) r) :
    LengthIdentities v a Fil τ := by
  unfold LengthIdentities
  obtain ⟨hd0, hker, hkerrange, hXker, hAX, -, -, hprojX, hHX, hFX, htf, g, helem⟩ :=
    GlobalTheory.T.adjoinRootProdLinearFactors_lattice_facts C v S a ha N Fil hsat τ
  obtain ⟨fF, fX, fK, fH, -, fFt, fKP⟩ := GlobalTheory.T.finite_eigenFiltration_pieces_addValInt C v S a ha N Fil hsat τ
  obtain ⟨-, -, hlc, hevc, -, -, -⟩ := GlobalTheory.T.adjoinRootProdLinearFactors_structure (Int0 v) S a τ
  have m1 : ∀ x : Fin N → RS a, x ∈ eigSub a τ (Fin N → RS a) ↔ lin a τ • x = 0 := by
    intro x; simp [eigSub, kerMul]
  have m2 : ∀ x : Fin N → RS a, x ∈ preEig a Fil τ ↔ lin a τ • x ∈ Fil := by
    intro x; simp [preEig, mulR]
  have m3 : ∀ x : Fin N → RS a, x ∈ filKer a Fil τ ↔ x ∈ Fil ∧ cofac a τ • x = 0 := by
    intro x; simp [filKer, mulR]
  have m4 : ∀ x : Fil, x ∈ eigSub a τ Fil ↔ lin a τ • (x : Fin N → RS a) = 0 := by
    intro x; simp [eigSub, kerMul, Subtype.ext_iff]
  generalize hd : ev a τ (cofac a τ) = d at hd0 helem hevc
  have hlinP : ∀ x : Fin N → RS a, lin a τ • (cofac a τ • x) = 0 := by
    intro x; rw [smul_smul, hlc, zero_smul]
  have hPh : ∀ x : Fin N → RS a, lin a τ • x = 0 → d • x = cofac a τ • x := by
    intro x h; rw [helem, h, smul_zero, sub_zero]
  have hcA : ∀ x, comp a N τ (lin a τ • x) = 0 := by
    intro x
    have : lin a τ • x ∈ LinearMap.ker (comp a N τ) := by rw [hkerrange]; exact ⟨x, rfl⟩
    exact this
  have hcP : ∀ x, comp a N τ (cofac a τ • x) = d • comp a N τ x := by
    intro x
    rw [show d • comp a N τ x = comp a N τ (d • x) from (map_smul (comp a N τ) d x).symm, helem,
      map_sub, smul_comm g (lin a τ) x, hcA, sub_zero]
  have hker' : ∀ x, comp a N τ x = 0 ↔ cofac a τ • x = 0 := hker
  have hkerA : ∀ x, mulR a N (lin a τ) x = 0 → x ∈ eigSub a τ (Fin N → RS a) := fun x h => (m1 x).2 h
  have hIinj : Function.Injective (incl a Fil) := fun x y h => Subtype.ext h
  have htfQ : ∀ (c : Int0 v) (y : (Fin N → RS a) ⧸ Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
      exact (Submodule.Quotient.mk_eq_zero _).2 (hsat c x hc h)
  have htfF : ∀ (c : Int0 v) (y : Fil), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h
    exact Subtype.ext (htf c y hc (congrArg Subtype.val h))
  have htfO : ∀ (c : Int0 v) (y : Fin N → Int0 v), c ≠ 0 → c • y = 0 → y = 0 := by
    intro c y hc h; exact (smul_eq_zero.mp h).resolve_left hc
  have fgF : (Fil.restrictScalars (Int0 v)).FG := Module.Finite.iff_fg.mp fF
  have fgH : (eigSub a τ (Fin N → RS a)).FG := Module.Finite.iff_fg.mp fH
  have fgK : (filKer a Fil τ).FG := Module.Finite.iff_fg.mp fK
  have fB : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)) :=
    Module.Finite.iff_fg.mpr (fgH.sup fgF)

  have hBX : eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) ≤ preEig a Fil τ :=
    sup_le hHX hFX
  have hdB : ∀ x ∈ preEig a Fil τ,
      d • x ∈ eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) := by
    intro x hx
    rw [helem]
    refine Submodule.sub_mem_sup ?_ ?_
    · exact (m1 _).2 (hlinP x)
    · exact Fil.smul_mem g ((m2 x).1 hx)
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htf _ _ hBX fX fB d hd0 hdB

  have hmapB_proj : (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)).map (proj a Fil) =
      (eigSub a τ (Fin N → RS a)).map (proj a Fil) := by
    rw [Submodule.map_sup]
    have : (Fil.restrictScalars (Int0 v)).map (proj a Fil) = ⊥ := by
      rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
      exact (Submodule.mem_bot _).2 ((Submodule.Quotient.mk_eq_zero _).2 hx)
    rw [this, sup_bot_eq]
  have ha1 : RelLen v ((eigSub a τ (Fin N → RS a)).map (proj a Fil))
      (eigSub a τ ((Fin N → RS a) ⧸ Fil)) δ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfQ (proj a Fil) _ _ hBX ?_ fX fB δ).1 hδ
    · rwa [hmapB_proj, hprojX] at this
    · rintro x ⟨-, hx⟩
      exact Submodule.mem_sup_right ((Submodule.Quotient.mk_eq_zero _).1 hx)

  have hHA : (eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ := by
    rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot _).2 ((m1 x).1 hx)
  have hmapB_A : (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) := by
    rw [Submodule.map_sup, hHA, bot_sup_eq]
  have hb0 : RelLen v ((Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ))) (filKer a Fil τ) δ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hBX ?_ fX fB δ).1 hδ
    · rwa [hmapB_A, hAX] at this
    · rintro x ⟨-, hx⟩; exact Submodule.mem_sup_left (hkerA x hx)
  have hIm1 : (imMul a (lin a τ) Fil).map (incl a Fil) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (lin a τ)) := by
    ext z; constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨lin a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hIm2 : (kerMul a (cofac a τ) Fil).map (incl a Fil) = filKer a Fil τ := by
    ext z; constructor
    · rintro ⟨y, hy, rfl⟩
      exact (m3 _).2 ⟨y.2, by simpa [kerMul, Subtype.ext_iff, incl] using hy⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := (m3 z).1 hz
      exact ⟨⟨z, hz1⟩, by simpa [kerMul, Subtype.ext_iff] using hz2, rfl⟩
  have hfgImLin : (imMul a (lin a τ) Fil).FG :=
    Submodule.fg_of_fg_map_injective _ hIinj (by rw [hIm1]; exact fgF.map _)
  have hle2 : imMul a (lin a τ) Fil ≤ kerMul a (cofac a τ) Fil := by
    rintro _ ⟨y, rfl⟩
    show cofac a τ • lin a τ • y = 0
    rw [smul_smul, mul_comm, hlc, zero_smul]
  have hb : RelLen v (imMul a (lin a τ) Fil) (kerMul a (cofac a τ) Fil) δ := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htfF htf (incl a Fil) _ _ hle2 ?_ fKP
      (Module.Finite.iff_fg.mpr hfgImLin) δ).2 ?_
    · rintro x ⟨-, hx⟩
      have : x = 0 := hIinj (by rw [map_zero]; exact hx)
      rw [this]; exact Submodule.zero_mem _
    · rwa [hIm1, hIm2]

  have hIm3 : (imMul a (cofac a τ) Fil).map (incl a Fil) =
      (Fil.restrictScalars (Int0 v)).map (mulR a N (cofac a τ)) := by
    ext z; constructor
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, w.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
  have hfgImP : (imMul a (cofac a τ) Fil).FG :=
    Submodule.fg_of_fg_map_injective _ hIinj (by rw [hIm3]; exact fgF.map _)
  have hle3 : imMul a (cofac a τ) Fil ≤ eigSub a τ Fil := by
    rintro _ ⟨y, rfl⟩
    exact (m4 _).2 (hlinP y)
  have hd3 : ∀ y ∈ eigSub a τ Fil, d • y ∈ imMul a (cofac a τ) Fil := by
    intro y hy
    refine ⟨y, Subtype.ext ?_⟩
    show cofac a τ • (y : Fin N → RS a) = d • (y : Fin N → RS a)
    rw [hPh _ ((m4 y).1 hy)]
  obtain ⟨e₂, he₂⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htfF _ _ hle3 fFt (Module.Finite.iff_fg.mpr hfgImP) d hd0 hd3

  have fgE : (eigQuot a Fil τ).FG := fgF.map _
  have fE : Module.Finite (Int0 v) (eigQuot a Fil τ) := Module.Finite.iff_fg.mpr fgE
  have hfgFt : (eigSub a τ Fil).FG := Module.Finite.iff_fg.mp fFt
  have fCt : Module.Finite (Int0 v) ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) :=
    Module.Finite.iff_fg.mpr (hfgFt.map _)
  have hle4 : (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) ≤ eigQuot a Fil τ := by
    rintro _ ⟨y, -, rfl⟩; exact ⟨y, y.2, rfl⟩
  have hd4 : ∀ z ∈ eigQuot a Fil τ, d • z ∈ (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, (m4 _).2 (hlinP x), hcP x⟩
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_latticeRelativeLength_of_smul_le C v _ htfO _ _ hle4 fE fCt d hd0 hd4

  have hIm5 : (imMul a (cofac a τ) Fil).map ((comp a N τ).comp (incl a Fil)) =
      (eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d) := by
    ext z; constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨comp a N τ y, ⟨y, y.2, rfl⟩, (hcP y).symm⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨cofac a τ • x, Fil.smul_mem _ hx⟩, ⟨⟨x, hx⟩, rfl⟩, hcP x⟩
  have he5 : RelLen v ((eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d))
      ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) e₂ := by
    have := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htfF htfO ((comp a N τ).comp (incl a Fil)) _ _ hle3 ?_ fFt
      (Module.Finite.iff_fg.mpr hfgImP) e₂).1 he₂
    · rwa [hIm5] at this
    · rintro y ⟨hy, hy0⟩
      have h1 : cofac a τ • (y : Fin N → RS a) = 0 := (hker' _).1 hy0
      have h2 : d • (y : Fin N → RS a) = 0 := by rw [hPh _ ((m4 y).1 hy), h1]
      have : y = 0 := Subtype.ext (htf d _ hd0 h2)
      rw [this]; exact Submodule.zero_mem _
  have hme : RelLen v ((eigQuot a Fil τ).map (LinearMap.lsmul (Int0 v) (Fin N → Int0 v) d))
      (eigQuot a Fil τ) (m + e₂) :=
    GlobalTheory.T.relLen_trans_add C v _ _ _ _ m e₂ he5 hm
  have hdC0 : (d : C) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hvd : v (d : C) ≠ ⊤ := fun h => hdC0 ((AddValuation.top_iff v).1 h)
  obtain ⟨rd, hrd⟩ := WithTop.ne_top_iff_exists.1 hvd
  have hsc := GlobalTheory.T.latticeRelativeLength_smul_eq_rank_mul_valuation C v _ htfO (eigQuot a Fil τ) fE d rd hrd.symm
  have hsum : m + e₂ = (finrank (Int0 v) (eigQuot a Fil τ) : ℝ) * rd := RelLen.unique v hme hsc
  have hfr : finrank (Int0 v) (eigQuot a Fil τ) = eigRank v a Fil τ := GlobalTheory.T.finrank_int0_submodule_eq_finrank_span C v N _ fE
  have hdC : ((d : Int0 v) : C) = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
    rw [hevc]; push_cast; rfl
  have hvdeq : vd v a τ = (rd : WithTop ℝ) := by
    unfold vd; rw [← hdC, hrd]
  have hjr : eigRank v a Fil τ • vd v a τ = (((eigRank v a Fil τ : ℝ) * rd : ℝ) : WithTop ℝ) := by
    rw [hvdeq, ← WithTop.coe_nsmul, nsmul_eq_mul]

  have hKc : (filKer a Fil τ).map (comp a N τ) = ⊥ := by
    rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot _).2 ((hker' x).2 ((m3 x).1 hx).2)
  have hKF : filKer a Fil τ ≤ Fil.restrictScalars (Int0 v) := fun x hx => ((m3 x).1 hx).1
  have hD'F : (Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ ≤
      Fil.restrictScalars (Int0 v) := sup_le inf_le_left hKF
  have hDB : eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ ≤
      eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v) := sup_le_sup_left hKF _
  have hFHt : Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a) =
      (eigSub a τ Fil).map (incl a Fil) := by
    ext z; constructor
    · rintro ⟨hz1, hz2⟩
      exact ⟨⟨z, hz1⟩, (m4 _).2 ((m1 z).1 hz2), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (m1 _).2 ((m4 y).1 hy)⟩
  have fD' : Module.Finite (Int0 v)
      ↥((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ) :=
    Module.Finite.iff_fg.mpr (by rw [hFHt]; exact (hfgFt.map _).sup fgK)
  have fD : Module.Finite (Int0 v) ↥(eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ) :=
    Module.Finite.iff_fg.mpr (fgH.sup fgK)
  have hmapcD' : ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ).map
      (comp a N τ) = (eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil)) := by
    rw [Submodule.map_sup, hKc, sup_bot_eq, hFHt, Submodule.map_comp]
  have s1 : RelLen v ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ)
      (Fil.restrictScalars (Int0 v)) m := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hD'F ?_ fF fD' m).2 ?_
    · rintro x ⟨hxF, hx0⟩
      exact Submodule.mem_sup_right ((m3 x).2 ⟨hxF, (hker' x).1 hx0⟩)
    · rw [hmapcD']; exact hm
  have s2 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hD'F (by
      rintro x ⟨hxF, hx0⟩
      exact Submodule.mem_sup_left ⟨hxF, hkerA x hx0⟩) fF fD' m).1 s1
  have hDA' : ((Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)) ⊔ filKer a Fil τ).map
      (mulR a N (lin a τ)) = (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (mulR a N (lin a τ)) := by
    have h0 : (Fil.restrictScalars (Int0 v) ⊓ eigSub a τ (Fin N → RS a)).map (mulR a N (lin a τ)) = ⊥ :=
      le_bot_iff.1 (hHA ▸ Submodule.map_mono inf_le_right)
    rw [Submodule.map_sup, Submodule.map_sup, h0, hHA]
  have s3 : RelLen v (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ)
      (eigSub a τ (Fin N → RS a) ⊔ Fil.restrictScalars (Int0 v)) m := by
    refine (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htf (mulR a N (lin a τ)) _ _ hDB ?_ fB fD m).2 ?_
    · rintro x ⟨-, hx0⟩; exact Submodule.mem_sup_left (hkerA x hx0)
    · rw [← hDA', hmapB_A]; exact s2
  have s4 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hDB (by
      rintro x ⟨hxB, hx0⟩
      obtain ⟨h, hh, f', hf', rfl⟩ := Submodule.mem_sup.1 hxB
      have hP0 : cofac a τ • (h + f') = 0 := (hker' _).1 hx0
      have hdh : d • h ∈ Fil := by
        rw [hPh h ((m1 h).1 hh)]
        have e1 : cofac a τ • h = -(cofac a τ • f') :=
          eq_neg_of_add_eq_zero_left (by rw [← smul_add]; exact hP0)
        rw [e1]; exact Fil.neg_mem (Fil.smul_mem _ hf')
      have hhF := hsat d h hd0 hdh
      exact Submodule.mem_sup_right ((m3 _).2 ⟨Fil.add_mem hhF hf', hP0⟩)) fB fD m).1 s3
  have hDc : (eigSub a τ (Fin N → RS a) ⊔ filKer a Fil τ).map (comp a N τ) =
      (eigSub a τ (Fin N → RS a)).map (comp a N τ) := by
    rw [Submodule.map_sup, hKc, sup_bot_eq]
  rw [hDc] at s4
  have s5 := (GlobalTheory.T.hasLatticeRelativeLength_map_iff C v _ _ htf htfO (comp a N τ) _ _ hBX (by
      rintro x ⟨hxX, hx0⟩
      exact Submodule.mem_sup_right (hXker ⟨hxX, hx0⟩)) fX fB δ).1 hδ
  have s6 := GlobalTheory.T.relLen_trans_add C v _ _ _ _ δ m s4 s5
  have hrδ : r = δ + m := RelLen.unique v hlen s6
  refine ⟨δ, e₂, m, ha1, hb, he₂, hm, ?_, ?_⟩
  · rw [hsum, hfr, hjr]
  · intro hall
    have hy : yExp v a Fil τ = eigRank v a Fil τ • vd v a τ := by
      unfold yExp vd
      rw [Finset.sum_congr rfl (fun s _ => by rw [hall s]), ← Finset.smul_sum,
        addVal_prod v]
      congr 1
      exact Finset.sum_congr rfl (fun s _ => v.map_sub_swap _ _)
    have hrj : r = (eigRank v a Fil τ : ℝ) * rd := by
      have : (r : WithTop ℝ) = (((eigRank v a Fil τ : ℝ) * rd : ℝ) : WithTop ℝ) := by
        rw [hr, hy, hjr]
      exact_mod_cast this
    have hδ0 := relLen_nonneg hδ
    have hm0 := relLen_nonneg hm
    have he0 := relLen_nonneg he₂
    rw [hfr] at hsum
    rw [hjr]
    refine ⟨hδ0, ?_, hm0, ?_⟩
    · exact WithTop.coe_le_coe.2 (by linarith)
    · exact WithTop.coe_le_coe.2 (by linarith)

theorem lengthIdentities_of_relLen : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ → RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r → LengthIdentities v a Fil τ :=
  fun C _ v S _ _ a ha N Fil hsat τ r hr hlen =>
    herbrand_lengthIdentities_auxiliary_bound C v S a ha N Fil hsat τ r hr hlen

end GlobalTheory.HerbLen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandLengthIdentitiesOfRelativeLengthStatement
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.herbrand_lengthIdentities_of_relativeLength : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∀ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ → RelLen v ((eigSub a τ (Fin N → RS a)).map (comp a N τ)) ((preEig a Fil τ).map (comp a N τ)) r → LengthIdentities v a Fil τ := by
  first | exact @GlobalTheory.HerbLen.lengthIdentities_of_relLen | exact GlobalTheory.HerbLen.lengthIdentities_of_relLen | (intros; apply GlobalTheory.HerbLen.lengthIdentities_of_relLen <;> assumption)
end
