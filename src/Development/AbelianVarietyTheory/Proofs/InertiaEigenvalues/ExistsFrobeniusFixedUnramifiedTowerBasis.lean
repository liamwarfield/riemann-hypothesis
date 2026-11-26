module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEll

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedUnramifiedTowerBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedUnramifiedTowerBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobeniusFixedBasis

variable {F K M : Type} [Field F] [Field K] [Algebra F K] [AddCommGroup M] [Module K M] [Module F M]
  [IsScalarTower F K M]

theorem isScalarTower_sub (E : IntermediateField F K) : IsScalarTower F E M :=
  ⟨fun q e m => by
    show ((q • e : E) : K) • m = q • ((e : K) • m)
    rw [IntermediateField.coe_smul, smul_assoc]⟩

theorem exists_tower_basis (E : IntermediateField F K) {r : ℕ} (bω : Module.Basis (Fin r) F E)
    (n : Type) [Fintype n] [DecidableEq n] (v : n × Fin r → M) (hv : LinearIndependent F v)
    (hst : ∀ e ∈ E, ∀ c, e • v c ∈ Submodule.span F (Set.range v)) :
    ∃ a : n → M, (∀ j, a j ∈ Submodule.span F (Set.range v)) ∧
      LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • a jk.1) ∧
      Submodule.span F (Set.range fun jk : n × Fin r => ((bω jk.2 : E) : K) • a jk.1) =
        Submodule.span F (Set.range v) := by
  haveI := isScalarTower_sub (M := M) E
  set V := Submodule.span F (Set.range v) with hVdef
  have hstab : ∀ e ∈ E, ∀ x ∈ V, e • x ∈ V := by
    intro e he x hx
    have hle : V ≤ V.comap ((LinearMap.lsmul K M e).restrictScalars F) := by
      rw [hVdef, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact hst e he c
    exact hle hx
  let VE : Submodule E M :=
    { carrier := V
      add_mem' := fun hx hy => V.add_mem hx hy
      zero_mem' := V.zero_mem
      smul_mem' := fun e x hx => hstab (e : K) e.2 x hx }
  have hfinV : Module.finrank F V = Fintype.card n * r := by
    rw [hVdef, finrank_span_eq_card hv, Fintype.card_prod, Fintype.card_fin]
  let e1 : VE ≃ₗ[F] V :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hfinVE : Module.finrank F VE = Fintype.card n * r := by
    rw [← hfinV]; exact e1.finrank_eq
  haveI : Module.Finite F V := by
    rw [hVdef]; exact FiniteDimensional.span_of_finite F (Set.finite_range v)
  haveI : Module.Finite F VE := Module.Finite.equiv e1.symm
  haveI : Module.Finite E VE := Module.Finite.of_restrictScalars_finite F E VE
  have hE : Module.finrank F E = r := by
    rw [Module.finrank_eq_card_basis bω, Fintype.card_fin]
  haveI : Module.Finite F E := Module.Finite.of_basis bω
  have hrpos : 0 < r := by
    rw [← hE]; exact Module.finrank_pos
  have htower := Module.finrank_mul_finrank F E VE
  rw [hE, hfinVE] at htower
  have hnE : Module.finrank E VE = Fintype.card n := by
    have : Module.finrank E VE * r = Fintype.card n * r := by rw [mul_comm]; exact htower
    exact Nat.eq_of_mul_eq_mul_right hrpos this
  let b : Module.Basis n E VE := (Module.finBasisOfFinrankEq E VE hnE).reindex (Fintype.equivFin n).symm
  let bt : Module.Basis (Fin r × n) F VE := bω.smulTower b
  let f : VE →ₗ[F] M := (VE.subtype).restrictScalars F
  have hf : Function.Injective f := Subtype.val_injective
  refine ⟨fun j => (b j : M), fun j => (b j).2, ?_, ?_⟩
  · have h1 : LinearIndependent F (f ∘ bt) := bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
    have h2 := h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)
    convert h2 using 1
    ext jk
    simp [bt, f, Module.Basis.smulTower_apply, ← algebraMap_smul K]
  · have hli : LinearIndependent F (fun jk : n × Fin r => ((bω jk.2 : E) : K) • (b jk.1 : M)) := by
      have h1 : LinearIndependent F (f ∘ bt) := bt.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
      have h2 := h1.comp (Equiv.prodComm n (Fin r)) (Equiv.injective _)
      convert h2 using 1
      ext jk
      simp [bt, f, Module.Basis.smulTower_apply, ← algebraMap_smul K]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨jk, rfl⟩
      exact hstab _ (bω jk.2).2 _ (b jk.1).2
    · rw [finrank_span_eq_card hli, hfinV, Fintype.card_prod, Fintype.card_fin]

end GlobalTheory.FrobeniusFixedBasis

namespace GlobalTheory.FrobeniusFixedBasis

def frFixed (l : ℕ) [Fact l.Prime] (r : ℕ) : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) where
  carrier := {c | fr l r c = c}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add (f := _), ha, hb]
  algebraMap_mem' := fun q => by
    show (frobUr l ^ r) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = _
    exact AlgHom.commutes _ q
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv₀, hx]

end GlobalTheory.FrobeniusFixedBasis

namespace GlobalTheory


open GlobalTheory.FrobeniusFixedBasis in
theorem exists_frFixed_tower_basis : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) →
    LinearIndependent ℚ_[l] ω → (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) →
    ∀ (M : Type) [AddCommGroup M] [Module ↥(MaximalUnramifiedExtension l) M] [Module ℚ_[l] M] [IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) M] (n : Type)
      [Fintype n] [DecidableEq n] (v : n × Fin r → M), LinearIndependent ℚ_[l] v →
      (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c, e • v c ∈ Submodule.span ℚ_[l] (Set.range v)) →
      ∃ a : n → M, (∀ j, a j ∈ Submodule.span ℚ_[l] (Set.range v)) ∧
        LinearIndependent ℚ_[l] (fun jk : n × Fin r => ω jk.2 • a jk.1) ∧
        Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range v) := by
  intro l _ r ω hω hli hsp M _ _ _ _ n _ _ v hv hst
  let E := frFixed l r
  let ω' : Fin r → E := fun k => ⟨ω k, hω k⟩
  have hli' : LinearIndependent ℚ_[l] ω' := by
    apply LinearIndependent.of_comp (E.val.toLinearMap)
    exact hli
  have hsp' : ⊤ ≤ Submodule.span ℚ_[l] (Set.range ω') := by
    rintro ⟨c, hc⟩ _
    obtain ⟨a, ha⟩ := hsp c hc
    have : (⟨c, hc⟩ : E) = ∑ k, a k • ω' k := by
      apply Subtype.ext
      show c = ((∑ k, a k • ω' k : E) : ↥(MaximalUnramifiedExtension l))
      rw [ha]
      simp [ω']
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bω : Module.Basis (Fin r) ℚ_[l] E := Module.Basis.mk hli' hsp'
  obtain ⟨a, ha1, ha2, ha3⟩ := exists_tower_basis E bω n v hv (fun e he c => hst e he c)
  have hb : ∀ k, ((bω k : E) : ↥(MaximalUnramifiedExtension l)) = ω k := fun k => by
    simp [bω, ω', Module.Basis.mk_apply]
  simp only [hb] at ha2 ha3
  exact ⟨a, ha1, ha2, ha3⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedUnramifiedTowerBasisStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusFixed_unramified_tower_basis : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → LinearIndependent ℚ_[l] ω → (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) → ∀ (M : Type) [AddCommGroup M] [Module ↥(MaximalUnramifiedExtension l) M] [Module ℚ_[l] M] [IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) M] (n : Type) [Fintype n] [DecidableEq n] (v : n × Fin r → M), LinearIndependent ℚ_[l] v → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c, e • v c ∈ Submodule.span ℚ_[l] (Set.range v)) → ∃ a : n → M, (∀ j, a j ∈ Submodule.span ℚ_[l] (Set.range v)) ∧ LinearIndependent ℚ_[l] (fun jk : n × Fin r => ω jk.2 • a jk.1) ∧ Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range v) := by
  first | exact @GlobalTheory.exists_frFixed_tower_basis | exact GlobalTheory.exists_frFixed_tower_basis | (intros; apply GlobalTheory.exists_frFixed_tower_basis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocks
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem exists_cols_isUnit {F : Type} [CommRing F] (hF : IsField F) {b n : Type} [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] (X : Matrix b n F) (Z : Matrix n b F) (h : X * Z = 1) :
    ∃ e : b → n, IsUnit (X.submatrix id e) := by
  letI : Field F := hF.toField
  have h1 : X.rank = Fintype.card b := by
    apply le_antisymm (Matrix.rank_le_card_height X)
    have := Matrix.rank_mul_le_left X Z
    rw [h, Matrix.rank_one] at this
    exact this
  have h2 : Module.finrank F (Submodule.span F (Set.range X.col)) = Fintype.card b := by
    rw [← Matrix.rank_eq_finrank_span_cols, h1]
  obtain ⟨κ, e, he, hspan, hli⟩ := exists_linearIndependent' F X.col
  haveI : Finite κ := Finite.of_injective e he
  letI : Fintype κ := Fintype.ofFinite κ
  have h3 : Fintype.card κ = Fintype.card b := by
    rw [← finrank_span_eq_card hli, hspan, h2]
  let τ : b ≃ κ := Fintype.equivOfCardEq h3.symm
  refine ⟨e ∘ τ, ?_⟩
  have h4 : LinearIndependent F (X.submatrix id (e ∘ τ)).col := hli.comp τ τ.injective
  exact Matrix.linearIndependent_cols_iff_isUnit.mp h4

end GlobalTheory.PMon.SubquotientAlgEquiv

end

noncomputable section

namespace GlobalTheory.PMon.SubquotientAlgEquiv

theorem map_mul_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p q s : Type}
    [Fintype q] (M : Matrix p q R) (N : Matrix q s R) : (M * N).map σ = M.map σ * N.map σ :=
  Matrix.map_mul (f := (σ : R →+* R))

theorem map_one_algEquiv {R S : Type} [CommRing R] [CommRing S] [Algebra S R] (σ : R ≃ₐ[S] R) {p : Type}
    [DecidableEq p] : (1 : Matrix p p R).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

end GlobalTheory.PMon.SubquotientAlgEquiv

namespace GlobalTheory.PMon

open scoped Matrix


open SubquotientAlgEquiv in
theorem subQuot : SubQuot := by
  intro l _ P AI T a b _ _ _ _ K r ρ ρ₁ ρ₂ c _ hblk hdr
  have hF := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1
  have e11 : ∀ m g (i j : a), matD P ρ m g (Sum.inl i) (Sum.inl j) = matD P ρ₁ m g i j := by
    intro m g i j; simp [matD, hblk g]
  have e21 : ∀ m g (i : b) (j : a), matD P ρ m g (Sum.inr i) (Sum.inl j) = 0 := by
    intro m g i j; simp [matD, hblk g]
  have e22 : ∀ m g (i j : b), matD P ρ m g (Sum.inr i) (Sum.inr j) = matD P ρ₂ m g i j := by
    intro m g i j; simp [matD, hblk g]
  refine ⟨fun m => ?_, fun m => ?_⟩
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.mul_inv Q
    have hQiQ : ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.inv_mul Q
    have hinv : ∀ g : ↥(GK K), ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) =
        ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g := by
      intro g
      have hs : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) = 1 := by
        rw [← map_mul_algEquiv, hQQi, map_one_algEquiv]
      calc ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))
          = (((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) := by
            rw [hQiQ, Matrix.one_mul]
        _ = ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
              (matD P ρ m g * (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) := by
            rw [hQ g]
        _ = ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * matD P ρ m g *
              ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l)) *
              ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).map (P.actQdR (g : GQ l))) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hs, Matrix.mul_one]
    let Y : Matrix (a ⊕ b) a P.R.BdR := ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inl
    let W : Matrix a (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inl id
    have hWY : W * Y = 1 := by
      rw [show W * Y = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inl Sum.inl from
        (Matrix.submatrix_mul _ _ Sum.inl id Sum.inl Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inl_injective
    have hYW : Yᵀ * Wᵀ = 1 := by rw [← Matrix.transpose_mul, hWY, Matrix.transpose_one]
    obtain ⟨e, he⟩ := exists_cols_isUnit hF Yᵀ Wᵀ hYW
    have hY' : IsUnit (Y.submatrix e id) := by
      have := (Matrix.isUnit_transpose _).2 he
      simpa [Matrix.transpose_submatrix] using this
    have hσY : ∀ g : ↥(GK K), (Y.submatrix e id).map (P.actQdR (g : GQ l)) = Y.submatrix e id * matD P ρ₁ m g := by
      intro g; ext i j
      have := congrFun (congrFun (hinv g) (e i)) (Sum.inl j)
      simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e11, e21, mul_zero,
        Finset.sum_const_zero, add_zero] at this
      simpa [Y, Matrix.mul_apply] using this
    refine ⟨hY'.unit⁻¹, fun g => ?_⟩
    have hu : ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR) = Y.submatrix e id := hY'.unit_spec
    have hs : ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) *
        ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) = 1 := by
      rw [← map_mul_algEquiv, Units.mul_inv, map_one_algEquiv]
    calc matD P ρ₁ m g * ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l))
        = (((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) * ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR)) *
            matD P ρ₁ m g * ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          rw [Units.inv_mul, Matrix.one_mul]
      _ = ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) *
            (((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR) * matD P ρ₁ m g) *
            ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          simp only [Matrix.mul_assoc]
      _ = ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR) *
            ((hY'.unit : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) *
            ((hY'.unit⁻¹ : GL a P.R.BdR) : Matrix a a P.R.BdR).map (P.actQdR (g : GQ l)) := by
          rw [hu, hσY g]
      _ = _ := by rw [Matrix.mul_assoc, hs, Matrix.mul_one]
  · obtain ⟨Q, hQ⟩ := hdr m
    have hQQi : (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) * ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) = 1 :=
      Units.mul_inv Q
    let X : Matrix b (a ⊕ b) P.R.BdR := (Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix Sum.inr id
    let Z : Matrix (a ⊕ b) b P.R.BdR := ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR).submatrix id Sum.inr
    have hXZ : X * Z = 1 := by
      rw [show X * Z = ((Q : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR) *
          ((Q⁻¹ : GL (a ⊕ b) P.R.BdR) : Matrix (a ⊕ b) (a ⊕ b) P.R.BdR)).submatrix Sum.inr Sum.inr from
        (Matrix.submatrix_mul _ _ Sum.inr id Sum.inr Function.bijective_id).symm, hQQi]
      exact Matrix.submatrix_one _ Sum.inr_injective
    obtain ⟨e, he⟩ := exists_cols_isUnit hF X Z hXZ
    refine ⟨he.unit, fun g => ?_⟩
    rw [he.unit_spec]
    ext i j
    have := congrFun (congrFun (hQ g) (Sum.inr i)) (e j)
    simp only [Matrix.map_apply, Matrix.mul_apply, Fintype.sum_sum_type, e21, e22, zero_mul,
      Finset.sum_const_zero, zero_add] at this
    simpa [X, Matrix.mul_apply] using this

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamBlockTriangularDiagonalBlocksStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_blockTriangular_diagonal_blocks : SubQuot := by
  first | exact @GlobalTheory.PMon.subQuot | exact GlobalTheory.PMon.subQuot | (intros; apply GlobalTheory.PMon.subQuot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueUnramifiedIntegersCoordsBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueUnramifiedIntegersCoordsBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS

noncomputable section

namespace GlobalTheory.PrismSplit

theorem isUnit_sub_of_pow_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {m : ℕ}
    (hm0 : 0 < m) (hm : IsUnit (m : O)) {a b : O} (ha : a ^ m = 1) (hb : b ^ m = 1) (h : a ≠ b) :
    IsUnit (a - b) := by
  by_contra hn
  have h1 := (Commute.all a b).geom_sum₂_mul m
  rw [ha, hb, sub_self] at h1
  have h2 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr h)
  have h3 : IsLocalRing.residue O a = IsLocalRing.residue O b := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hn
  have h4 := congrArg (IsLocalRing.residue O) h2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, h3, map_zero] at h4
  rw [geom_sum₂_self] at h4
  have hbu : IsUnit b := IsUnit.of_pow_eq_one hb hm0.ne'
  have h5 : IsUnit ((m : IsLocalRing.ResidueField O) * IsLocalRing.residue O b ^ (m - 1)) := by
    refine IsUnit.mul ?_ ((hbu.map _).pow _)
    simpa using hm.map (IsLocalRing.residue O)
  exact h5.ne_zero h4

theorem existsUnique_of_separated {R W O ι : Type} [CommRing R] [Nontrivial R] [CommRing W]
    [CommRing O] [Algebra R W] [Algebra R O] [Fintype ι] [Module.Free R W] [Module.Finite R W]
    (hr : Module.finrank R W = Fintype.card ι) (φ : ι → (W →ₐ[R] O))
    (hs : ∀ i j, i ≠ j → ∃ w, IsUnit (φ i w - φ j w)) {d : ℕ} (o : Module.Basis (Fin d) R O)
    (y : ι → O) : ∃! c : Fin d → W, ∀ k, y k = ∑ i, o i * φ k (c i) := by
  classical
  let F : (Fin d → W) →ₗ[R] (ι → O) :=
    { toFun := fun c k => ∑ i, o i * φ k (c i)
      map_add' := fun c c' => by
        funext k; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext k; simp [Finset.smul_sum] }
  let Φ : O ⊗[R] W →ₐ[O] (ι → O) :=
    Algebra.TensorProduct.lift (Algebra.ofId O (ι → O)) (AlgHom.pi φ)
      (fun _ _ => Commute.all _ _)
  have hΦ : ∀ (a : O) (w : W) (k : ι), Φ (a ⊗ₜ w) k = a * φ k w := by
    intro a w k
    simp [Φ]
  have h1 : ∀ t, Φ t ∈ LinearMap.range F := by
    intro t
    induction t with
    | add s t hs ht => rw [map_add]; exact add_mem hs ht
    | tmul a w =>
      refine ⟨fun i => o.repr a i • w, ?_⟩
      funext k
      rw [hΦ]
      conv_rhs => rw [← o.sum_repr a]
      rw [Finset.sum_mul]
      simp [F]
  have h2 : ∀ i, Pi.single i (1 : O) ∈ Φ.range := by
    intro i
    choose w hw using hs i
    have : (Pi.single i (1 : O) : ι → O) = ∏ j : {j // i ≠ j}, (((hw j.1 j.2).unit⁻¹ : Oˣ) : O) •
        (Φ (1 ⊗ₜ w j.1 j.2) - algebraMap O (ι → O) (φ j.1 (w j.1 j.2))) := by
      funext k
      rw [Finset.prod_apply]
      by_cases hk : i = k
      · subst hk
        rw [Pi.single_eq_same, eq_comm]
        refine Finset.prod_eq_one fun j _ => ?_
        simp [hΦ]
      · rw [Pi.single_eq_of_ne (Ne.symm hk), eq_comm]
        refine Finset.prod_eq_zero (Finset.mem_univ ⟨k, hk⟩) ?_
        simp [hΦ]
    rw [this]
    refine Subalgebra.prod_mem _ fun j _ => Subalgebra.smul_mem _ (sub_mem (AlgHom.mem_range_self Φ _) ?_) _
    exact Subalgebra.algebraMap_mem _ _
  have h3 : Function.Surjective F := by
    intro y
    have : y ∈ Φ.range := by
      rw [← Finset.univ_sum_single y]
      refine sum_mem fun i _ => ?_
      have : (Pi.single i (y i) : ι → O) = y i • (Pi.single i (1 : O) : ι → O) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      exact Subalgebra.smul_mem _ (h2 i) _
    obtain ⟨t, rfl⟩ := this
    exact h1 t
  have : Module.Free R O := Module.Free.of_basis o
  have : Module.Finite R O := Module.Finite.of_basis o
  have e : (Fin d → W) ≃ₗ[R] (ι → O) := LinearEquiv.ofFinrankEq _ _ (by
    simp [Module.finrank_pi_fintype, hr, Module.finrank_eq_card_basis o, mul_comm])
  have h4 : Function.Injective F :=
    OrzechProperty.injective_of_surjective_of_injective e.toLinearMap F e.injective h3
  obtain ⟨c, hc⟩ := h3 y
  refine ⟨c, fun k => (congrFun hc k).symm, fun c' hc' => h4 ?_⟩
  rw [hc]
  exact funext fun k => (hc' k).symm

theorem exists_root_ne {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    {e e' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1} (h : e ≠ e') :
    ∃ (ω : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ ω ^ m = 1 ∧ e ω ≠ e' ω := by
  by_contra hn
  push Not at hn
  apply h
  ext1 x
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm ℚ_[l] ‖(x : Om l)‖
  have ha0 : 0 < ‖a‖ := (norm_nonneg _).trans_lt ha
  have ha1 : a ≠ 0 := norm_pos_iff.mp ha0
  obtain ⟨n, z, ω, hω, hx⟩ := GlobalTheory.UnramSpan.exists_sum_rootsOfUnity l K
    (algebraMap ℚ_[l] (Om l) a⁻¹ * x) (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x).2 (by
      rw [← Algebra.smul_def, norm_smul, norm_inv, inv_mul_le_iff₀ ha0, mul_one]
      exact ha.le)
  have hx' : algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x =
      ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * (⟨ω i, (hω i).1⟩ : ↥(K0 K)) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact hx
  have : e (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x) = e' (algebraMap ℚ_[l] ↥(K0 K) a⁻¹ * x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨m, hm, hl, h1⟩ := (hω i).2
    rw [map_mul, map_mul, e.commutes, e'.commutes, hn _ m hm hl (Subtype.ext (by simpa using h1))]
  rw [map_mul, map_mul, e.commutes, e'.commutes] at this
  exact mul_left_cancel₀ ((_root_.map_ne_zero _).mpr (inv_ne_zero ha1)) this

theorem isUnit_natCast {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {m : ℕ}
    (hl : ¬ l ∣ m) : IsUnit (m : O) := by
  have hu : IsUnit (m : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hl ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := l) (m : ℤ)).mp (by simpa using h)
    exact_mod_cast this
  simpa using hu.map (algebraMap ℤ_[l] O)

theorem exists_isUnit_sub {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    {e e' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1} (h : e ≠ e') : ∃ w, IsUnit (embW e w - embW e' w) := by
  obtain ⟨_, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  obtain ⟨ω, m, hm, hl, h1, hne⟩ := exists_root_ne h
  have hi : IsIntegral ℤ_[l] ω := IsIntegral.of_pow hm (by rw [h1]; exact isIntegral_one)
  have hp : ∀ f : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1, embW f ⟨ω, hi⟩ ^ m = 1 := by
    intro f
    apply Subtype.ext
    change f ω ^ m = 1
    rw [← map_pow, h1, map_one]
  exact ⟨⟨ω, hi⟩, isUnit_sub_of_pow_eq_one hm (isUnit_natCast _ hl) (hp e) (hp e')
    fun h => hne (congrArg Subtype.val h)⟩

theorem existsUnique_coords : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)), Function.Injective emb → ∀ (d : ℕ) (o : Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) (y : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)), ∃! c : Fin d → WK K, ∀ k, y k = ∑ i, o i * embW (emb k) (c i) := by
  intro l _ K LL emb hemb d o y
  have hfd : FiniteDimensional ℚ_[l] ↥(K0 K) := (unr K).2
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨_, -, -, -, hfree, hfin, -⟩ := GlobalTheory.Per.integers_completeDVR l (unr K)
  have : Module.IsTorsionFree ℤ_[l] ↥(K0 K) := by
    rw [Module.isTorsionFree_iff_faithfulSMul, faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥(K0 K)]
    exact (algebraMap ℚ_[l] ↥(K0 K)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  refine existsUnique_of_separated ?_ (fun k => embW (emb k)) ?_ o y
  · rw [ZMod.card]
    exact IsIntegralClosure.rank ℤ_[l] ℚ_[l] ↥(K0 K) (integralClosure ℤ_[l] ↥(K0 K))
  · exact fun i j hij => exists_isUnit_sub (hemb.ne hij)

end GlobalTheory.PrismSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueUnramifiedIntegersCoordsBasisStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism GlobalTheory.PrismS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_unramifiedIntegers_coords_basis : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)), Function.Injective emb → ∀ (d : ℕ) (o : Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) (y : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)), ∃! c : Fin d → WK K, ∀ k, y k = ∑ i, o i * embW (emb k) (c i) := by
  first | exact @GlobalTheory.PrismSplit.existsUnique_coords | exact GlobalTheory.PrismSplit.existsUnique_coords | (intros; apply GlobalTheory.PrismSplit.existsUnique_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiAdicFiltrationModEll
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPiPowEllOfNearPi
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPiPowEllOfNearPi
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl
section Gen
variable {O A R : Type} [CommRing O] [CommRing A] [CommRing R] [Algebra O R] {n : ℕ}

theorem letφ_smul_letE (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (o : O) (i : ZMod n) :
    letφ φ₀ (o • letE i : LetA O n) = o • letE (i + 1) := by
  rw [map_smul]
  congr 1
  funext k
  change φ₀ (letE i (k - 1)) = letE (i + 1) k
  by_cases hk : k = i + 1
  · subst hk
    simp [letE]
  · have : k - 1 ≠ i := fun h => hk (by rw [← h]; ring)
    simp [letE, hk, this]

theorem near_one_split [NeZero n] {ι : A →+* R} {p : ℕ} (j : LetA O n →ₐ[O] R)
    (hj : ∀ a, ∃ b, j a = ι b) (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (φR : R → R)
    (hφj : ∀ b, φR (j b) = j (letφ φ₀ b))
    (hφ : ∀ x, Near ι p (j letπ) 1 x → Near ι p (j letπ) 1 (φR x))
    (hO : ∀ o : O, Near ι p (j letπ) 1 (algebraMap O R o) → ∃ o' : O, o = (p : O) * o')
    (a : LetA O n) (ha : Near ι p (j letπ) 1 (j a)) :
    ∃ a1 a2 : LetA O n, a = letπ * a1 + (p : LetA O n) * a2 := by
  obtain ⟨a', ha'⟩ : ∃ a' : LetA O n,
      a = letπ * a' + fun i => PowerSeries.C (PowerSeries.constantCoeff (a i)) :=
    ⟨fun i => PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (a i),
      funext fun i => PowerSeries.eq_X_mul_shift_add_const (a i)⟩
  set c : LetA O n := fun i => PowerSeries.C (PowerSeries.constantCoeff (a i)) with hc
  have h1 : Near ι p (j letπ) 1 (j c) := by
    obtain ⟨b, hb⟩ := hj a'
    have h2 : j c = j a - j letπ ^ 1 * ι b := by
      rw [pow_one, ← hb, ← map_mul, ← map_sub]
      congr 1
      exact eq_sub_of_add_eq' ha'.symm
    rw [h2]
    exact ha.sub (Near.pow_mul 1 b)
  have h3 : ∀ i, ∃ o' : O, PowerSeries.constantCoeff (a i) = (p : O) * o' := by
    intro i
    set o := PowerSeries.constantCoeff (a i) with ho
    have h4 : Near ι p (j letπ) 1 (j (o • letE i)) := by
      obtain ⟨b, hb⟩ := hj (letE i)
      have h5 : (o • letE i : LetA O n) = letE i * c := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp [letE, hc, ho, PowerSeries.smul_eq_C_mul]
        · simp [letE, hk]
      rw [h5, map_mul, hb]
      exact h1.mul_ι b
    have h6 : ∀ k : ℕ, Near ι p (j letπ) 1 (j (o • letE (i + (k : ZMod n)))) := by
      intro k
      induction k with
      | zero => simpa using h4
      | succ k ih =>
        have := hφ _ ih
        rwa [hφj, letφ_smul_letE, add_assoc, ← Nat.cast_succ] at this
    have h7 : ∀ k : ZMod n, Near ι p (j letπ) 1 (j (o • letE k)) := by
      intro k
      have := h6 (k - i).val
      rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this
    apply hO
    have h8 : ∑ k : ZMod n, (letE k : LetA O n) = 1 := by
      funext k
      simp [letE, Finset.sum_apply, Pi.single_apply]
    have h9 : algebraMap O R o = ∑ k : ZMod n, j (o • letE k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← Finset.smul_sum, h8, map_smul, map_one, Algebra.algebraMap_eq_smul_one]
    rw [h9]
    exact Near.sum _ fun k _ => h7 k
  choose o' ho' using h3
  refine ⟨a', fun i => PowerSeries.C (o' i), ha'.trans ?_⟩
  congr 1
  funext i
  simp [hc, ho']

theorem near_split [NeZero n] {ι : A →+* R} {p : ℕ} {t : R} (j : LetA O n →ₐ[O] R)
    (hj : ∀ a, ∃ b, j a = ι b) (ht : j letπ = t) (hu : IsUnit t)
    (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (φR : R → R)
    (hφj : ∀ b, φR (j b) = j (letφ φ₀ b))
    (hφ : ∀ x, Near ι p t 1 x → Near ι p t 1 (φR x))
    (hO : ∀ o : O, Near ι p t 1 (algebraMap O R o) → ∃ o' : O, o = (p : O) * o')
    (m : ℕ) (a : LetA O n) (ha : Near ι p t m (j a)) :
    ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2 := by
  subst ht
  induction m with
  | zero => exact ⟨a, 0, by simp⟩
  | succ m ih =>
    obtain ⟨τ, hτ⟩ := hj letπ
    obtain ⟨a1, a2, h⟩ := ih (ha.mono hτ.symm (Nat.le_succ m))
    have h1 : j letπ ^ m * j a1 = j a - (p : R) * j a2 := by
      rw [h, map_add (f := _), map_mul, map_mul, map_pow, map_natCast, add_sub_cancel_right]
    have h2 : Near ι p (j letπ) (m + 1) (j letπ ^ m * j a1) := by
      rw [h1]
      exact ha.sub (Near.of_mul _ _)
    obtain ⟨b1, b2, hb⟩ := near_one_split j hj φ₀ φR hφj hφ hO a1 (h2.cancel hu)
    exact ⟨b1, letπ ^ m * b2 + a2, by rw [h, hb]; ring⟩
end Gen


set_option maxHeartbeats 1000000 in
theorem mem_pow_pi_of_nearPi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (m : ℕ) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), NearPi AI LL s m (inclR LL (E.tie.io a)) → ∃ a1 a2 : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a = letπ ^ m * a1 + (l : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) * a2 := by
  intro l _ P AI K s LL h W E m a ha
  obtain ⟨c1, -, c3, -⟩ := GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E
  obtain ⟨-, -, p3, p4⟩ := GlobalTheory.DecomplFrob.frobenius_and_constants l P AI LL s
  have := (P.PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hu : IsUnit (piR AI LL s) := c3 ▸ W.EE_π.map E.tie.ioE
  refine near_split (ι := (inclR LL : RA LL →+* RW LL)) ((inclR LL).comp E.tie.io)
    (fun b => ⟨E.tie.io b, rfl⟩) ((E.tie.ioE_ext letπ).symm.trans c3) hu W.φ₀ (fun x => φRW LL x)
    (fun b => ?_) (p3 1) p4 m a ha
  have h1 := c1 (algebraMap _ W.EE b)
  exact (congrArg (fun x => φRW LL x) (E.tie.ioE_ext b)).symm.trans (h1.symm.trans
    ((congrArg (fun e => E.tie.ioE e) (W.φE_ext b)).trans (E.tie.ioE_ext _)))

end GlobalTheory.Decompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPiPowEllOfNearPiStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_pi_pow_ell_of_nearPi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W) (m : ℕ) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), NearPi AI LL s m (inclR LL (E.tie.io a)) → ∃ a1 a2 : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), a = letπ ^ m * a1 + (l : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) * a2 := by
  first | exact @GlobalTheory.Decompl.mem_pow_pi_of_nearPi | exact GlobalTheory.Decompl.mem_pow_pi_of_nearPi | (intros; apply GlobalTheory.Decompl.mem_pow_pi_of_nearPi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiAdicFiltrationModEll
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

section Abstract

variable {O : Type} [CommRing O] {n : ℕ} {EE RA R : Type} [CommRing EE] [CommRing RA] [CommRing R]

theorem letA_dvd_of_forall_pow (p : ℕ) (a : LetA O n)
    (h : ∀ m : ℕ, ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2) :
    ∃ b : LetA O n, a = (p : LetA O n) * b := by
  have h1 : ∀ (i : ZMod n) (k : ℕ), ∃ c : O, PowerSeries.coeff k (a i) = (p : O) * c := by
    intro i k
    obtain ⟨a1, a2, h2⟩ := h (k + 1)
    refine ⟨PowerSeries.coeff k (a2 i), ?_⟩
    have h3 : a i = PowerSeries.X ^ (k + 1) * a1 i + PowerSeries.C (p : O) * a2 i := by
      rw [h2, map_natCast]; rfl
    rw [h3, map_add (f := _), PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
      PowerSeries.coeff_C_mul]
  choose c hc using h1
  refine ⟨fun i => PowerSeries.mk (c i), funext fun i => PowerSeries.ext fun k => ?_⟩
  have h3 : ((p : LetA O n) * fun i => PowerSeries.mk (c i)) i =
      PowerSeries.C (p : O) * PowerSeries.mk (c i) := by
    rw [map_natCast]; rfl
  rw [h3, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem near_abstract (p : ℕ) (f : LetA O n →+* EE) (io : EE →+* R) (ι : RA →+* R) (t : R)
    (τ : RA) (hτ : ι τ = t) (ht : io (f letπ) = t) (hu : IsUnit (f letπ))
    (hd : ∀ x : EE, ∃ (a : LetA O n) (m : ℕ), x * f (letπ ^ m) - f a ∈ Ideal.span {(p : EE) ^ 1})
    (hs : ∀ a : LetA O n, f a ∈ Ideal.span {(p : EE) ^ 1} →
      ∃ b : LetA O n, a = (p : LetA O n) ^ 1 * b)
    (key : ∀ (m : ℕ) (a : LetA O n), Near ι p t m (io (f a)) →
      ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2) :
    (∀ (m : ℕ) (e : EE), Near ι p t m (io e) →
      ∃ (a : LetA O n) (e' : EE), e = f (letπ ^ m * a) + (p : EE) * e') ∧
    ∀ (e : EE) (r : R), io e = (p : R) * r → ∃ e' : EE, e = (p : EE) * e' := by
  have H1 : ∀ (m : ℕ) (e : EE), Near ι p t m (io e) →
      ∃ (a : LetA O n) (e' : EE), e = f (letπ ^ m * a) + (p : EE) * e' := by
    intro m e he
    obtain ⟨a, N, h1⟩ := hd e
    rw [pow_one, Ideal.mem_span_singleton] at h1
    obtain ⟨e1, h1⟩ := h1
    have h2 : f a = f letπ ^ N * e - p * e1 := by
      rw [map_pow] at h1; linear_combination -h1
    have h3 : Near ι p t (N + m) (io (f a)) := by
      rw [h2, map_sub, map_mul, map_mul, map_pow, ht, map_natCast]
      refine Near.sub (Near.mul ?_ he) (Near.of_mul _ _)
      simpa using Near.pow_mul (ι := ι) (p := p) (t := t) N 1
    obtain ⟨a1, a2, h4⟩ := key _ _ h3
    obtain ⟨u, hu'⟩ := hu.exists_right_inv
    have h5 : f letπ ^ N * u ^ N = 1 := by rw [← mul_pow, hu', one_pow]
    refine ⟨a1, u ^ N * (e1 + f a2), ?_⟩
    rw [h4, map_add (f := _), map_mul, map_mul, map_pow, map_natCast, pow_add] at h2
    rw [map_mul, map_pow]
    linear_combination (-u ^ N) * h2 - (e - f letπ ^ m * f a1) * h5
  refine ⟨H1, fun e r he => ?_⟩
  have h1 := fun m => H1 m e (he ▸ Near.of_mul m r)
  choose a e' h2 using h1
  obtain ⟨b, hb⟩ := letA_dvd_of_forall_pow p (a 0) fun m => by
    obtain ⟨b, hb⟩ := hs (a 0 - letπ ^ m * a m) (by
      rw [pow_one, Ideal.mem_span_singleton]
      refine ⟨e' m - e' 0, ?_⟩
      have h3 := h2 0
      rw [pow_zero, one_mul] at h3
      rw [map_sub]
      linear_combination h2 m - h3)
    exact ⟨a m, b, by linear_combination hb⟩
  refine ⟨f b + e' 0, ?_⟩
  have h3 := h2 0
  rw [pow_zero, one_mul, hb, map_mul, map_natCast] at h3
  linear_combination h3

end Abstract


set_option maxHeartbeats 1000000 in
theorem near_ioE : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (m : ℕ) (e : W.EE), NearPi AI LL s m (E.tie.ioE e) → ∃ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) (e' : W.EE), e = algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE (letπ ^ m * a) + (l : W.EE) * e') ∧ ∀ (e : W.EE) (r : RW LL), E.tie.ioE e = (l : RW LL) * r → ∃ e' : W.EE, e = (l : W.EE) * e' := by
  intro l _ P AI K s LL h W E
  have hd := W.EE_dense
  have hs := W.EE_sat
  rw [P.PD_p K] at hd hs
  exact near_abstract l (algebraMap _ W.EE) (E.tie.ioE : W.EE →+* RW LL)
    (inclR LL : RA LL →+* RW LL) (piR AI LL s) _ rfl (GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E).2.2.1
    W.EE_π (fun x => hd x 1) (fun a => hs a 1)
    (fun m a ha => GlobalTheory.T.mem_pi_pow_ell_of_nearPi l P AI K s LL h W E m a (E.tie.ioE_ext a ▸ ha))

end GlobalTheory.Decompl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiAdicFiltrationModEllStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleComparison_piAdic_filtration_mod_ell : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (m : ℕ) (e : W.EE), NearPi AI LL s m (E.tie.ioE e) → ∃ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) (e' : W.EE), e = algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE (letπ ^ m * a) + (l : W.EE) * e') ∧ ∀ (e : W.EE) (r : RW LL), E.tie.ioE e = (l : RW LL) * r → ∃ e' : W.EE, e = (l : W.EE) * e' := by
  first | exact @GlobalTheory.Decompl.near_ioE | exact GlobalTheory.Decompl.near_ioE | (intros; apply GlobalTheory.Decompl.near_ioE <;> assumption)
end
end
