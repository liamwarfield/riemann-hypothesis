module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvRegaugedSecondLawFamily
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalDiscPointsValuationIntegers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTranspose
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTranspose
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigAdd

private theorem trace_eq (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)]
    (V : Type) [AddCommGroup V] [Module C V] [Module.Finite C V] (ρ : OE →+* Module.End C V) (a : OE) :
    LinearMap.trace C V (ρ a) = ∑ τ : OE →+* C,
      (Module.finrank C ↥(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) : C) * τ a := by
  classical
  obtain ⟨h1, h2⟩ := (GlobalTheory.order_rep_diagonalisable C OE).2 V ρ
  have hI := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h1 h2
  have hv : ∀ (τ : OE →+* C) (v : V), v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) → ρ a v = τ a • v :=
    fun τ v hv => Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  have hf : ∀ τ : OE →+* C, Set.MapsTo (ρ a) ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b))
      ↑(⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := fun τ v h => by
    have h' : v ∈ (⨅ b : OE, Module.End.eigenspace (ρ b) (τ b)) := h
    have := Submodule.smul_mem _ (τ a) h'
    rw [← hv τ v h'] at this
    exact this
  rw [LinearMap.trace_eq_sum_trace_restrict hI hf]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have : (ρ a).restrict (hf τ) = τ a • LinearMap.id := by
    ext v
    exact hv τ v.1 v.2
  rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

private theorem trace_mat (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    (OE : Type) [CommRing OE] [IsDomain OE]
    [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [Fintype (OE →+* C)] (d : ℕ)
    (ρ : OE →+* Matrix (Fin d) (Fin d) O) (a : OE) :
    algebraMap O C (ρ a).trace = ∑ τ : OE →+* C, (eigDim C ρ τ : C) * τ a := by
  have := trace_eq C OE (Fin d → C)
    ((Matrix.toLinAlgEquiv' (R := C) (n := Fin d)).toRingEquiv.toRingHom.comp
      ((algebraMap O C).mapMatrix.comp ρ)) a
  refine Eq.trans ?_ this
  change _ = LinearMap.trace C _ (Matrix.toLin' ((ρ a).map (algebraMap O C)))
  rw [Matrix.trace_toLin'_eq, ← AddMonoidHom.map_trace]

private theorem coeff_eq (C : Type) [Field C] [CharZero C] (OE : Type) [CommRing OE] [Fintype (OE →+* C)]
    (m n : (OE →+* C) → ℕ) (h : ∀ a, ∑ τ : OE →+* C, (m τ : C) * τ a = ∑ τ : OE →+* C, (n τ : C) * τ a)
    (τ : OE →+* C) : m τ = n τ := by
  have li : LinearIndependent C (fun τ : OE →+* C => (τ : OE → C)) :=
    (linearIndependent_monoidHom OE C).comp (fun τ : OE →+* C => (τ : OE →* C))
      RingHom.coe_monoidHom_injective
  have := Fintype.linearIndependent_iffₛ.1 li (fun τ => (m τ : C)) (fun τ => (n τ : C))
    (by funext a; simpa [Finset.sum_apply] using h a) τ
  exact_mod_cast this

private def trHom {O OE : Type} [CommRing O] [CommRing OE] {d : ℕ} (ρ : OE →+* Matrix (Fin d) (Fin d) O) :
    OE →+* Matrix (Fin d) (Fin d) O where
  toFun a := (ρ a)ᵀ
  map_one' := by simp
  map_mul' a b := by rw [mul_comm a b, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp

theorem eigDim_add_transpose : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (d r g : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O), SplitEx A B → ∀ (ρ : OE →+* Matrix (Fin d) (Fin d) O) (ρA : OE →+* Matrix (Fin r) (Fin r) O) (ρB : OE →+* Matrix (Fin g) (Fin g) O), (∀ a, B * ρ a = ρB a * B) → (∀ a, ρ a * A = A * ρA a) → ∀ τ : OE →+* C, eigDim C ρ τ = eigDim C ρA τ + eigDim C ρB τ ∧ eigDim C (fun a => (ρ a)ᵀ) τ = eigDim C ρ τ := by
  intro C _ _ _ O _ _ OE _ _ _ _ _ d r g A B hS ρ ρA ρB hB hA τ
  haveI : Finite (OE →+* C) := (GlobalTheory.order_rep_diagonalisable C OE).1
  letI : Fintype (OE →+* C) := Fintype.ofFinite _
  obtain ⟨-, A', B', h1, h2, h3⟩ := hS
  constructor
  · refine coeff_eq C OE (fun τ => eigDim C ρ τ) (fun τ => eigDim C ρA τ + eigDim C ρB τ) (fun a => ?_) τ
    have ht : (ρ a).trace = (ρA a).trace + (ρB a).trace := by
      have e1 : (ρ a * (A * A')).trace = (ρA a).trace := by
        rw [← Matrix.mul_assoc, hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
      have e2 : (ρ a * (B' * B)).trace = (ρB a).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hB, Matrix.mul_assoc, h2,
          Matrix.mul_one]
      rw [← e1, ← e2, ← Matrix.trace_add, ← Matrix.mul_add, h3, Matrix.mul_one]
    simp only [Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [← trace_mat, ← trace_mat, ← trace_mat, ht, map_add (f := _)]
  · refine coeff_eq C OE (fun τ => eigDim C (trHom ρ) τ) (fun τ => eigDim C ρ τ) (fun a => ?_) τ
    rw [← trace_mat, ← trace_mat]
    exact congrArg _ (Matrix.trace_transpose _)

end GlobalTheory.EigAdd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTransposeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspaceDim_add_split_exact_transpose : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (OE : Type) [CommRing OE] [IsDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (d r g : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O), SplitEx A B → ∀ (ρ : OE →+* Matrix (Fin d) (Fin d) O) (ρA : OE →+* Matrix (Fin r) (Fin r) O) (ρB : OE →+* Matrix (Fin g) (Fin g) O), (∀ a, B * ρ a = ρB a * B) → (∀ a, ρ a * A = A * ρA a) → ∀ τ : OE →+* C, eigDim C ρ τ = eigDim C ρA τ + eigDim C ρB τ ∧ eigDim C (fun a => (ρ a)ᵀ) τ = eigDim C ρ τ := by
  first | exact @GlobalTheory.EigAdd.eigDim_add_transpose | exact GlobalTheory.EigAdd.eigDim_add_transpose | (intros; apply GlobalTheory.EigAdd.eigDim_add_transpose <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFreeGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFreeGenerators
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocalFactorFree

private theorem aux {R S M I : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Module.Finite R M] [Module.Free R M]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) :
    ∃ (h : ℕ) (y : Fin h → M), LinearIndependent R (fun q : I × Fin h => (b q.1 : S) • y q.2) ∧
      ∀ m : M, m ∈ Submodule.span R (Set.range fun q : I × Fin h => (b q.1 : S) • y q.2) ↔ (1 - e) • m = 0 := by
  classical
  let f : LinearMap.range (LinearMap.mulLeft R e) →ₗ[R] (S ⧸ Ideal.span {1 - e}) :=
    (Ideal.Quotient.mkₐ R (Ideal.span {1 - e})).toLinearMap ∘ₗ (Submodule.subtype _)
  have hf : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨_, s, rfl⟩ hs
      have h1 : e * s ∈ Ideal.span {1 - e} := Ideal.Quotient.eq_zero_iff_mem.1 hs
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
      apply Subtype.ext
      change e * s = 0
      have h2 : e * (e * s) = e * s := by rw [← _root_.mul_assoc, he.eq]
      rw [← h2, ← ht]
      linear_combination t * he.mul_one_sub_self
    · intro a
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
      refine ⟨⟨e * s, s, rfl⟩, ?_⟩
      change Ideal.Quotient.mk _ (e * s) = Ideal.Quotient.mk _ s
      rw [Ideal.Quotient.eq]
      exact Ideal.mem_span_singleton'.2 ⟨-s, by ring⟩
  let bA : Module.Basis I R (S ⧸ Ideal.span {1 - e}) := b.map (LinearEquiv.ofBijective f hf)
  haveI : Module.Finite R (S ⧸ Ideal.span {1 - e}) := Module.Finite.of_basis bA
  haveI : Module.Free R (S ⧸ Ideal.span {1 - e}) := Module.Free.of_basis bA
  let N : Submodule S M := Submodule.torsionBy S M (1 - e)
  haveI : Module.Finite R N := Module.Finite.of_injective (N.subtype.restrictScalars R) Subtype.val_injective
  letI : Module (S ⧸ Ideal.span {1 - e}) N := inferInstanceAs (Module (S ⧸ Submodule.span S {1 - e}) (Submodule.torsionBy S M (1 - e)))
  have hsm : ∀ (s : S) (n : N), (Ideal.Quotient.mk (Ideal.span {1 - e}) s) • n = s • n := fun _ _ => rfl
  haveI : IsScalarTower R (S ⧸ Ideal.span {1 - e}) N := ⟨fun r a n => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : r • Ideal.Quotient.mk (Ideal.span {1 - e}) s = Ideal.Quotient.mk (Ideal.span {1 - e}) (r • s) := rfl
    rw [this, hsm, hsm, smul_assoc]⟩
  haveI : Module.Finite (S ⧸ Ideal.span {1 - e}) N := Module.Finite.of_restrictScalars_finite R _ _
  haveI : Module.IsTorsionFree (S ⧸ Ideal.span {1 - e}) N := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a n han
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    obtain ⟨r, hr, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
    have h1 : r • n = 0 := by
      rw [← algebraMap_smul (S ⧸ Ideal.span {1 - e}) r n, hc, mul_comm, mul_smul, han, smul_zero]
    have h2 : r • (n : M) = 0 := congrArg Subtype.val h1
    exact Subtype.ext ((smul_eq_zero.1 h2).resolve_left hr)
  let y := Module.finBasis (S ⧸ Ideal.span {1 - e}) N
  let B := bA.smulTower y
  have hB : (fun q : I × Fin _ => (b q.1 : S) • (y q.2 : M)) = (N.subtype.restrictScalars R) ∘ B := by
    funext q
    simp only [B, Function.comp, Module.Basis.smulTower_apply]
    rfl
  refine ⟨_, fun j => (y j : M), ?_, fun m => ?_⟩
  · rw [hB]
    exact B.linearIndependent.map' _ (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · rw [hB, Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top]
    constructor
    · rintro ⟨n, rfl⟩
      exact n.2
    · intro hm
      exact ⟨⟨m, hm⟩, rfl⟩

private theorem aux2 {R S I κ : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S] [Algebra R S]
    [Fintype κ] [DecidableEq κ]
    [Finite I] (e : S) (he : IsIdempotentElem e) [IsDomain (S ⧸ Ideal.span {1 - e})]
    [IsPrincipalIdealRing (S ⧸ Ideal.span {1 - e})]
    (b : Module.Basis I R (LinearMap.range (LinearMap.mulLeft R e))) (ρ : S →ₐ[R] Matrix κ κ R) :
    ∃ (h : ℕ) (y : Fin h → κ → R), LinearIndependent R (fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) ∧
      Submodule.span R (Set.range fun q : I × Fin h => ρ (b q.1 : S) *ᵥ y q.2) =
        LinearMap.range (Matrix.mulVecLin (ρ e)) := by
  letI : Module S (κ → R) := Module.compHom (κ → R) (ρ : S →+* Matrix κ κ R)
  have hsm : ∀ (s : S) (v : κ → R), s • v = ρ s *ᵥ v := fun _ _ => rfl
  haveI : IsScalarTower R S (κ → R) := ⟨fun r s v => by
    rw [hsm, hsm, map_smul, Matrix.smul_mulVec]⟩
  obtain ⟨h, y, h1, h2⟩ := aux (M := κ → R) e he b
  refine ⟨h, y, h1, ?_⟩
  ext m
  refine (h2 m).trans ⟨fun hm => ⟨m, ?_⟩, ?_⟩
  · change e • m = m
    rw [sub_smul, one_smul, sub_eq_zero] at hm
    exact hm.symm
  · rintro ⟨v, rfl⟩
    change (1 - e) • e • v = 0
    rw [← mul_smul, he.one_sub_mul_self, zero_smul]

theorem exists_free_generators : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]), ∃ (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) ∧ Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) := by
  intro p _ OE _ _ _ _ _ w b κ _ _ ρ
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.padic_unit_quotient_principal_basis p OE w
  exact aux2 w.e w.idem b ρ

end GlobalTheory.LocalFactorFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFreeGeneratorsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIndependent_spanning_range_mulVec : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]), ∃ (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) ∧ Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) := by
  first | exact @GlobalTheory.LocalFactorFree.exists_free_generators | exact GlobalTheory.LocalFactorFree.exists_free_generators | (intros; apply GlobalTheory.LocalFactorFree.exists_free_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinMulFAndCompAndSpanLeAndMemPow
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinMulFAndCompAndSpanLeAndMemPow
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChF

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.Regauge

variable {R : Type} [CommRing R] {d : ℕ}

private theorem gp_mulF (F : FGLaw R d) (N : ℕ) : GP (mulF F.F N) :=
  FormalMul.constantCoeff_mulF F.F F.const N

private theorem nsum_add (F : FGLaw R d) (a b : ℕ) :
    mulF F.F (a + b) = addOf F.F (mulF F.F a) (mulF F.F b) := by
  induction b with
  | zero => exact (addOf_zero F (gp_mulF F a)).symm
  | succ b ih =>
    change addOf F.F (mulF F.F (a + b)) (pt R d 0) = addOf F.F _ (addOf F.F (mulF F.F b) (pt R d 0))
    rw [ih, addOf_assoc F (gp_mulF F a) (gp_mulF F b) (gp_pt 0)]

private theorem nsum_mul (F : FGLaw R d) (N M : ℕ) :
    mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M) := by
  have hV := single_point_zero_constant (gp_mulF F M)
  induction N with
  | zero =>
    rw [Nat.zero_mul]
    exact (evP_zero _ hV).symm
  | succ N ih =>
    rw [Nat.succ_mul, nsum_add, ih]
    change _ = evP ![mulF F.F M] (addOf F.F (mulF F.F N) (pt R d 0))
    rw [evP_addOf _ hV _ _ _ (gp_mulF F N) (gp_pt 0), evP_pt _ hV]
    rfl

private theorem ev_mem_pow {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {K : Ideal (PS R n d)} (hK : ∀ j i, a j i ∈ K) {N : ℕ} {f : PS R m d}
    (hf : f ∈ germIdeal (Fin m × Fin d) R ^ N) : ev a f ∈ K ^ N := by
  have h : (germIdeal (Fin m × Fin d) R ^ N).map (substAlgHom (R := R) (gt_hasSubst a ha)) ≤ K ^ N := by
    rw [Ideal.map_pow, germIdeal_eq_span]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    rw [substAlgHom_X]
    exact hK _ _
  have := h (Ideal.mem_map_of_mem _ hf)
  rwa [substAlgHom_apply] at this

private theorem mem_sq_iff {σ : Type} [Finite σ] {g : MvPowerSeries σ R} :
    g ∈ germIdeal σ R ^ 2 ↔ constantCoeff g = 0 ∧ ∀ s, coeff (Finsupp.single s 1) g = 0 := by
  rw [mem_germIdeal_pow_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by simp), fun s => h _ (by simp)⟩
  · rintro ⟨h0, h1⟩ e he
    rcases (by omega : e.degree = 0 ∨ e.degree = 1) with h | h
    · obtain rfl := (Finsupp.degree_eq_zero_iff e).1 h
      simpa using h0
    · obtain ⟨s, rfl⟩ : e ∈ Set.range (fun s : σ => Finsupp.single s 1) := by
        rw [Finsupp.range_single_one]; exact h
      exact h1 s

private theorem coeff_single_X' {σ : Type} [DecidableEq σ] (s t : σ) :
    coeff (Finsupp.single s 1) (X t : MvPowerSeries σ R) = if s = t then 1 else 0 := by
  rw [coeff_X]
  simp [Finsupp.single_left_inj]

private theorem sub_lin_mem {σ : Type} [Fintype σ] {g : MvPowerSeries σ R} (hg : constantCoeff g = 0) :
    g - ∑ s, coeff (Finsupp.single s 1) g • X s ∈ germIdeal σ R ^ 2 := by
  classical
  refine mem_sq_iff.2 ⟨by simp [hg], fun s => ?_⟩
  simp [coeff_single_X']

private theorem ev_sub_lin_mem {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j, GP (a j))
    {f : PS R m d} (hf : constantCoeff f = 0) :
    ev a f - ∑ s : Fin m × Fin d, coeff (Finsupp.single s 1) f • a s.1 s.2 ∈
      germIdeal (Fin n × Fin d) R ^ 2 := by
  have h := ev_mem_pow ha (K := germIdeal (Fin n × Fin d) R) (fun j i => ha j i) (sub_lin_mem hf)
  unfold ev at h ⊢
  rw [← substAlgHom_apply (gt_hasSubst a ha)] at h ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sub, map_sum, map_smul, substAlgHom_X] using h

private theorem coeff_law (F : FGLaw R d) (i : Fin d) (l : Fin 2) (j : Fin d) :
    coeff (Finsupp.single (l, j) 1) (F.F i) = if j = i then 1 else 0 := by
  have hp : GP (pt R (n := 1) d 0) := gp_pt 0
  fin_cases l
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant hp gp_zero₂) (F.const i))).2 (0, j)
    have e : ev ![pt R (n := 1) d 0, 0] (F.F i) = X (0, i) := congrFun (addOf_zero F hp) i
    rw [e] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm
  · have h := (mem_sq_iff.1 (ev_sub_lin_mem (pair_points_zero_constant gp_zero₂ hp) (F.const i))).2 (0, j)
    rw [F.unit i] at h
    simp [Fintype.sum_prod_type, pt, coeff_single_X', sub_eq_zero] at h
    simpa using h.symm

private theorem nsum_sub_mem (F : FGLaw R d) (N : ℕ) (i : Fin d) :
    mulF F.F N i - (N : R) • X (0, i) ∈ germIdeal (Fin 1 × Fin d) R ^ 2 := by
  induction N with
  | zero => simp [mulF]
  | succ N ih =>
    have h := ev_sub_lin_mem (pair_points_zero_constant (gp_mulF F N) (gp_pt 0)) (F.const i)
    simp only [Fintype.sum_prod_type, coeff_law, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    convert add_mem h ih using 1
    change ev ![mulF F.F N, pt R d 0] (F.F i) - _ = _
    simp only [pt, Nat.cast_succ, add_smul, one_smul]
    abel

private theorem lin_nsum (F : FGLaw R d) (N : ℕ) :
    lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R) := by
  ext i j
  have h := (mem_sq_iff.1 (nsum_sub_mem F N i)).2 (0, j)
  rw [map_sub, sub_eq_zero, map_smul, coeff_single_X'] at h
  simp [lin, h, Matrix.one_apply, eq_comm]

private theorem span_nsum_le (F : FGLaw R d) (N M : ℕ) :
    Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M)) := by
  rw [Ideal.span_le, nsum_mul]
  rintro _ ⟨j, rfl⟩
  have := ev_mem_pow (single_point_zero_constant (gp_mulF F M)) (K := Ideal.span (Set.range (mulF F.F M))) (N := 1)
    (f := mulF F.F N j) (fun l i => by fin_cases l; exact Ideal.subset_span ⟨i, rfl⟩)
    (by rw [pow_one]; exact gp_mulF F N j)
  rwa [pow_one] at this

private theorem nsum_pow_mem (F : FGLaw R d) (p k : ℕ) (j : Fin d) :
    mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) := by
  set J := (Ideal.span {(p : R)}).map (C : R →+* PS R 1 d) ⊔
      Ideal.span (Set.range (X : Fin 1 × Fin d → PS R 1 d)) with hJ
  induction k generalizing j with
  | zero =>
    rw [zero_add, pow_one, hJ, ← germIdeal_eq_span]
    exact Ideal.mem_sup_right (gp_mulF F _ j)
  | succ k ih =>
    have hV := single_point_zero_constant (gp_mulF F (p ^ k))
    have h := ev_mem_pow hV (K := J ^ (k + 1)) (fun l i => by fin_cases l; exact ih i)
      (nsum_sub_mem F p j)
    rw [← pow_mul, gt_ev_sub _ hV, smul_eq_C_mul, gt_ev_mul _ hV, gt_ev_X _ hV] at h
    have h1 := Ideal.pow_le_pow_right (show k + 1 + 1 ≤ (k + 1) * 2 by omega) h
    have hC : ev ![mulF F.F (p ^ k)] (C (p : R) : PS R 1 d) = C (p : R) := subst_C _
    have h2 : C (p : R) * mulF F.F (p ^ k) j ∈ J ^ (k + 1 + 1) := by
      rw [pow_succ' J (k + 1)]
      exact Ideal.mul_mem_mul (Ideal.mem_sup_left (Ideal.mem_map_of_mem _
        (Ideal.subset_span rfl))) (ih j)
    rw [hC] at h1
    have h3 := add_mem h1 h2
    rw [pow_succ' p k, nsum_mul]
    simpa [comp1] using h3

end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF

theorem lin_mulF_and_comp_and_span_le_and_mem_pow : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d), (∀ N : ℕ, lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R)) ∧ (∀ N M : ℕ, mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M)) ∧ (∀ N M : ℕ, Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M))) ∧ ∀ (p k : ℕ) (j : Fin d), mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (MvPowerSeries.C : R →+* PS R 1 d) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) :=
  fun _ _ _ F => ⟨lin_nsum F, nsum_mul F, span_nsum_le F, nsum_pow_mem F⟩

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinMulFAndCompAndSpanLeAndMemPowStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow : ∀ (R : Type) [CommRing R] (d : ℕ) (F : FGLaw R d), (∀ N : ℕ, lin (mulF F.F N) = (N : R) • (1 : Matrix (Fin d) (Fin d) R)) ∧ (∀ N M : ℕ, mulF F.F (N * M) = comp1 (mulF F.F N) (mulF F.F M)) ∧ (∀ N M : ℕ, Ideal.span (Set.range (mulF F.F (N * M))) ≤ Ideal.span (Set.range (mulF F.F M))) ∧ ∀ (p k : ℕ) (j : Fin d), mulF F.F (p ^ k) j ∈ ((Ideal.span {(p : R)}).map (MvPowerSeries.C : R →+* PS R 1 d) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS R 1 d))) ^ (k + 1) := by
  first | exact @GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow | exact GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow | (intros; apply GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsAddCommMonoid
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsAddCommMonoid
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalPts

variable {O : Type} [CommRing O] {d : ℕ}

private theorem hasSub {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)

private def evA {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) : PS O m d →ₐ[O] PS O n d :=
  MvPowerSeries.substAlgHom (hasSub a ha)

private theorem evA_apply {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS O m d) : evA a ha f = ev a f := by
  unfold evA ev
  rw [MvPowerSeries.coe_substAlgHom]

private theorem ev_X {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (q : Fin m × Fin d) :
    ev a (MvPowerSeries.X q) = a q.1 q.2 := by
  unfold ev
  rw [MvPowerSeries.subst_X (hasSub a ha)]

private theorem const_ev {m n : ℕ} (a : Fin m → Pt O n d)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS O m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSub a ha) (fun q => ha q.1 q.2) hf

private theorem c1 {n : ℕ} {a : Pt O n d} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    ∀ i j, MvPowerSeries.constantCoeff ((![a] : Fin 1 → Pt O n d) i j) = 0 := by
  intro i j
  fin_cases i
  exact ha j

private theorem c2 {n : ℕ} {a b : Pt O n d} (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0)
    (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0) :
    ∀ i j, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → Pt O n d) i j) = 0 := by
  intro i j
  fin_cases i
  · exact ha j
  · exact hb j

private theorem cpt {n : ℕ} (i : Fin n) : ∀ j, MvPowerSeries.constantCoeff (pt O d i j) = 0 := by
  intro j
  simp [pt]

private def origin (O : Type) [CommRing O] (d : ℕ) : PS O 1 d →ₐ[O] O :=
  { (MvPowerSeries.constantCoeff : PS O 1 d →+* O) with
    commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }

private theorem general
    (hE : ∀ (n : ℕ) (c : Fin n × Fin d → O), (∀ q, ¬ IsUnit (c q)) →
      ∃! Φ : PS O n d →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q)
    (hN : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) (f : PS O n d), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f))
    (F : FGLaw O d) :
    ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst
      (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧
      (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧
      ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  have hX : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) q, ¬ IsUnit (Φ (MvPowerSeries.X q)) :=
    fun n Φ q => hN n Φ _ (by simp)
  have hext : ∀ (n : ℕ) (Φ Ψ : PS O n d →ₐ[O] O),
      (∀ i j, Φ (MvPowerSeries.X (i, j)) = Ψ (MvPowerSeries.X (i, j))) → Φ = Ψ :=
    fun n Φ Ψ h => (hE n _ (hX n Ψ)).unique (fun q => h q.1 q.2) (fun _ => rfl)
  have hext1 : ∀ (Φ Ψ : PS O 1 d →ₐ[O] O),
      (∀ j, Φ (MvPowerSeries.X (0, j)) = Ψ (MvPowerSeries.X (0, j))) → Φ = Ψ :=
    fun Φ Ψ h => hext 1 Φ Ψ (fun i j => by rw [Subsingleton.elim i 0]; exact h j)
  have hK : ∀ (m n : ℕ) (Φ : PS O n d →ₐ[O] O) (Ψ : PS O m d →ₐ[O] O) (a : Fin m → Pt O n d),
      (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) →
      (∀ i j, Ψ (MvPowerSeries.X (i, j)) = Φ (a i j)) → ∀ f, Ψ f = Φ (ev a f) := by
    intro m n Φ Ψ a ha h f
    have : Ψ = Φ.comp (evA a ha) := hext m _ _ (fun i j => by
      rw [AlgHom.comp_apply, evA_apply, ev_X a ha, h])
    rw [this, AlgHom.comp_apply, evA_apply]
  have hP : ∀ (n : ℕ) (φ : Fin n → (PS O 1 d →ₐ[O] O)), ∃ Φ : PS O n d →ₐ[O] O,
      ∀ i j, Φ (MvPowerSeries.X (i, j)) = φ i (MvPowerSeries.X (0, j)) := by
    intro n φ
    obtain ⟨Φ, h, -⟩ := hE n (fun q => φ q.1 (MvPowerSeries.X (0, q.2))) (fun q => hX 1 _ _)
    exact ⟨Φ, fun i j => h (i, j)⟩
  choose P hP using hP
  have cF : ∀ i j, MvPowerSeries.constantCoeff ((![F.F] : Fin 1 → Pt O 2 d) i j) = 0 := c1 F.const
  let add : (PS O 1 d →ₐ[O] O) → (PS O 1 d →ₐ[O] O) → (PS O 1 d →ₐ[O] O) :=
    fun φ φ' => (P 2 ![φ, φ']).comp (evA ![F.F] cF)
  have hadd : ∀ φ φ' f, add φ φ' f = P 2 ![φ, φ'] (ev (n := 2) ![F.F] f) := by
    intro φ φ' f
    simp only [add, AlgHom.comp_apply, evA_apply]
  have haddX : ∀ φ φ' j, add φ φ' (MvPowerSeries.X (0, j)) = P 2 ![φ, φ'] (F.F j) := by
    intro φ φ' j
    rw [hadd, ev_X _ cF]
    rfl
  have hS : ∀ (n : ℕ) (Φ : PS O n d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O) (a b : Pt O n d),
      (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (∀ j, MvPowerSeries.constantCoeff (b j) = 0) →
      (∀ j, φ (MvPowerSeries.X (0, j)) = Φ (a j)) → (∀ j, φ' (MvPowerSeries.X (0, j)) = Φ (b j)) →
      ∀ j, add φ φ' (MvPowerSeries.X (0, j)) = Φ (ev ![a, b] (F.F j)) := by
    intro n Φ φ φ' a b ha hb h h' j
    rw [haddX]
    refine hK 2 n Φ _ _ (c2 ha hb) (fun i k => ?_) _
    rw [hP]
    fin_cases i
    · exact h k
    · exact h' k
  have h0 : ∀ f, origin O d f = MvPowerSeries.constantCoeff f := fun _ => rfl
  have hcomm : ∀ φ φ', add φ φ' = add φ' φ := by
    intro φ φ'
    refine hext1 _ _ (fun j => ?_)
    rw [hS 2 (P 2 ![φ, φ']) φ' φ (pt O d 1) (pt O d 0) (cpt 1) (cpt 0)
      (fun k => (hP 2 ![φ, φ'] 1 k).symm) (fun k => (hP 2 ![φ, φ'] 0 k).symm), F.comm, haddX]
  have hzero : ∀ φ, add (origin O d) φ = φ := by
    intro φ
    refine hext1 _ _ (fun j => ?_)
    rw [hS 1 φ (origin O d) φ 0 (pt O d 0) (fun _ => by simp) (cpt 0)
      (fun k => by simp [h0]) (fun k => rfl), F.unit]
  have hassoc : ∀ φ φ' φ'', add (add φ φ') φ'' = add φ (add φ' φ'') := by
    intro φ φ' φ''
    refine hext1 _ _ (fun j => ?_)
    have e0 := fun k => (hP 3 ![φ, φ', φ''] 0 k).symm
    have e1 := fun k => (hP 3 ![φ, φ', φ''] 1 k).symm
    have e2 := fun k => (hP 3 ![φ, φ', φ''] 2 k).symm
    rw [hS 3 (P 3 ![φ, φ', φ'']) (add φ φ') φ'' (fun l => ev (n := 3) ![pt O d 0, pt O d 1] (F.F l)) (pt O d 2)
        (fun l => const_ev _ (c2 (cpt 0) (cpt 1)) _ (F.const l)) (cpt 2)
        (hS 3 _ φ φ' _ _ (cpt 0) (cpt 1) e0 e1) e2,
      hS 3 (P 3 ![φ, φ', φ'']) φ (add φ' φ'') (pt O d 0) (fun l => ev (n := 3) ![pt O d 1, pt O d 2] (F.F l))
        (cpt 0) (fun l => const_ev _ (c2 (cpt 1) (cpt 2)) _ (F.const l))
        e0 (hS 3 _ φ' φ'' _ _ (cpt 1) (cpt 2) e1 e2), F.assoc]
  letI : Add (PS O 1 d →ₐ[O] O) := ⟨add⟩
  letI : Zero (PS O 1 d →ₐ[O] O) := ⟨origin O d⟩
  letI inst : AddCommMonoid (PS O 1 d →ₐ[O] O) :=
    { add_assoc := hassoc
      zero_add := hzero
      add_zero := fun φ => (hcomm φ _).trans (hzero φ)
      add_comm := hcomm
      nsmul := nsmulRec }
  refine ⟨inst, ?_, h0, ?_⟩
  · intro φ φ' ψ
    change _ ↔ ψ = add φ φ'
    constructor
    · rintro ⟨Φ, h1, h2, h3⟩
      have : Φ = P 2 ![φ, φ'] := by
        refine hext 2 _ _ (fun i j => ?_)
        rw [hP]
        fin_cases i
        · have := h1 (MvPowerSeries.X (0, j))
          rw [ev_X _ (c1 (cpt 0))] at this
          exact this
        · have := h2 (MvPowerSeries.X (0, j))
          rw [ev_X _ (c1 (cpt 1))] at this
          exact this
      ext1 f
      rw [hadd, ← this, h3]
    · rintro rfl
      refine ⟨P 2 ![φ, φ'], fun f => ?_, fun f => ?_, fun f => (hadd φ φ' f).symm⟩
      · refine (hK 1 2 _ φ _ (c1 (cpt 0)) (fun i j => ?_) f).symm
        fin_cases i
        exact (hP 2 ![φ, φ'] 0 j).symm
      · refine (hK 1 2 _ φ' _ (c1 (cpt 1)) (fun i j => ?_) f).symm
        fin_cases i
        exact (hP 2 ![φ, φ'] 1 j).symm
  · intro N φ
    have hmul : ∀ (N : ℕ) j, (N • φ) (MvPowerSeries.X (0, j)) = φ (mulF F.F N j) := by
      intro N
      induction N with
      | zero =>
        intro j
        rw [zero_nsmul]
        change origin O d _ = φ 0
        simp [h0]
      | succ n ih =>
        intro j
        rw [succ_nsmul]
        exact hS 1 φ (n • φ) φ (mulF F.F n) (pt O d 0)
          (GlobalTheory.FormalMul.constantCoeff_mulF F.F F.const n) (cpt 0) ih (fun _ => rfl) j
    have hz : ∀ j, (0 : PS O 1 d →ₐ[O] O) (MvPowerSeries.X (0, j)) = 0 := by
      intro j
      change origin O d _ = 0
      simp [h0]
    constructor
    · intro h j
      rw [← hmul, h, hz]
    · intro h
      exact hext1 _ _ (fun j => by rw [hmul, hz, h j])

theorem points_addCommMonoid : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst; (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧ (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧ ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F
  exact general (fun n => (GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin n × Fin d)).1)
    (fun n => (GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin n × Fin d)).2.1) F

end GlobalTheory.FormalPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PointsAddCommMonoidStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), ∃ inst : AddCommMonoid (PS O 1 d →ₐ[O] O), letI := inst; (∀ φ φ' ψ, IsSum F.F φ φ' ψ ↔ ψ = φ + φ') ∧ (∀ f, (0 : PS O 1 d →ₐ[O] O) f = MvPowerSeries.constantCoeff f) ∧ ∀ (N : ℕ) (φ : PS O 1 d →ₐ[O] O), N • φ = 0 ↔ Killed F.F N φ := by
  first | exact @GlobalTheory.FormalPts.points_addCommMonoid | exact GlobalTheory.FormalPts.points_addCommMonoid | (intros; apply GlobalTheory.FormalPts.points_addCommMonoid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotent
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_eps {C B OE : Type} [Field C] [CommRing B] [Algebra C B] [CommRing OE]
    (σ : B →ₐ[C] C) (j : OE →+* B) (hj : Submodule.span C (Set.range j) = ⊤)
    (hsup : (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) = ⊤) :
    ∃ ε : B, σ ε = 1 ∧ ∀ z, z * ε = σ z • ε := by
  have key : ∀ z : B, ∃ ε : B, σ ε = σ z ∧ ∀ a, j a * ε = σ (j a) • ε := by
    intro z
    have hz : z ∈ (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) := by
      rw [hsup]; trivial
    induction hz using Submodule.iSup_induction' with
    | mem τ x hx =>
      have hx' : ∀ a, j a * x = τ a • x := fun a => by
        have := (Submodule.mem_iInf _).1 hx a
        rw [Module.End.mem_eigenspace_iff] at this
        exact this
      by_cases h0 : σ x = 0
      · exact ⟨0, by simp [h0], by simp⟩
      · refine ⟨x, rfl, fun a => ?_⟩
        have h1 := congrArg σ (hx' a)
        rw [map_mul, map_smul, smul_eq_mul] at h1
        rw [hx' a, mul_right_cancel₀ h0 h1]
    | zero => exact ⟨0, rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, by simp [ha, hb], fun c => by rw [mul_add, smul_add, ha', hb']⟩
  obtain ⟨ε, h1, h2⟩ := key 1
  refine ⟨ε, by simpa using h1, fun z => ?_⟩
  have hz : z ∈ Submodule.span C (Set.range j) := by rw [hj]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h2 a
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, hx, hy, map_add (f := _), add_smul]
  | smul c x _ hx => rw [smul_mul_assoc, hx, map_smul, smul_eq_mul, mul_smul]

private theorem core {C B OE κ I H : Type} [Field C] [CommRing B] [Algebra C B] [CommRing OE]
    [Fintype κ] [DecidableEq κ] [Fintype I] [Fintype H]
    (σ : B →ₐ[C] C) (j : OE →+* B) (hj : Submodule.span C (Set.range j) = ⊤)
    (hsup : (⨆ τ : OE →+* C, ⨅ a : OE,
      Module.End.eigenspace (((Algebra.lmul C B).toRingHom.comp j) a) (τ a)) = ⊤)
    (ρ : B →ₐ[C] Matrix κ κ C) (e : B) (he : σ e = 1) (b : I → B)
    (hb : ∀ z, z * e ∈ Submodule.span C (Set.range b)) (y : H → κ → C)
    (hli : LinearIndependent C (fun q : I × H => ρ (b q.1) *ᵥ y q.2))
    (hsp : ∀ x, ρ e *ᵥ x ∈ Submodule.span C (Set.range fun q : I × H => ρ (b q.1) *ᵥ y q.2)) :
    Module.finrank C ↥(⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) =
      Fintype.card H := by
  obtain ⟨ε, h1, h2⟩ := exists_eps σ j hj hsup
  have hεe : ε * e = ε := by rw [mul_comm, h2, he, one_smul]
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 (hb ε)
  rw [hεe] at ht
  have hmul : ∀ (z : B) (x : κ → C), ρ z *ᵥ (ρ ε *ᵥ x) = σ z • (ρ ε *ᵥ x) := fun z x => by
    rw [Matrix.mulVec_mulVec, ← map_mul, h2, map_smul, Matrix.smul_mulVec]
  have hmul' : ∀ (z : B) (x : κ → C), ρ ε *ᵥ (ρ z *ᵥ x) = σ z • (ρ ε *ᵥ x) := fun z x => by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_comm, h2, map_smul, Matrix.smul_mulVec]
  have hli' : LinearIndependent C (fun l : H => ρ ε *ᵥ y l) := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro c hc l
    have h3 := hli (fun q => c q.2 * t q.1) (by
      rw [← hc, Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun l _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← ht, map_sum, Matrix.sum_mulVec, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Matrix.smul_mulVec, mul_smul])
    by_contra hl
    have h4 : ∀ i, t i = 0 := fun i => (mul_eq_zero.1 (h3 (i, l))).resolve_left hl
    have h5 : ε = 0 := by rw [← ht]; simp [h4]
    rw [h5, map_zero] at h1
    exact zero_ne_one h1
  have hE : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρ (j a))) (σ (j a))) =
      Submodule.span C (Set.range fun l : H => ρ ε *ᵥ y l) := by
    apply le_antisymm
    · intro x hx
      have hx' : ∀ a, ρ (j a) *ᵥ x = σ (j a) • x := fun a => by
        have := (Submodule.mem_iInf _).1 hx a
        rw [Module.End.mem_eigenspace_iff] at this
        simpa using this
      have hx2 : ∀ z, ρ z *ᵥ x = σ z • x := fun z => by
        have hz : z ∈ Submodule.span C (Set.range j) := by rw [hj]; trivial
        induction hz using Submodule.span_induction with
        | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hx' a
        | zero => simp
        | add x y _ _ hx hy => rw [map_add (f := _), Matrix.add_mulVec, hx, hy, map_add (f := _), add_smul]
        | smul c x _ hx => rw [map_smul, Matrix.smul_mulVec, hx, map_smul, smul_eq_mul, mul_smul]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 (hsp x)
      have : x = ρ ε *ᵥ (ρ e *ᵥ x) := by rw [hx2 e, he, one_smul, hx2, h1, one_smul]
      rw [this, ← hc, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun q _ => ?_
      rw [Matrix.mulVec_smul, hmul']
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨q.2, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      refine (Submodule.mem_iInf _).2 fun a => ?_
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
      exact hmul _ _
  rw [hE, finrank_span_eq_card hli']

theorem eigDim_eq_of_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]) (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) → Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) → ∀ τ ∈ Emb (O := O) w.e, eigDim C (fun a : OE => (ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) ((algebraMap O C).comp τ) = h := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ _ _ _ w b κ _ _ ρ h y hli hsp τ hτ
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra
  haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap ℤ_[p] C) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h1 | h1
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero h1
    · exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) (pow_eq_zero_iff'.1 h1).1
  haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let σ : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] C := Algebra.TensorProduct.lift (AlgHom.id C C)
    ((IsScalarTower.toAlgHom ℤ_[p] O C).comp (tauExt τ)) (fun _ _ => Commute.all _ _)
  let ρB : (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) →ₐ[C] Matrix κ κ C :=
    Algebra.TensorProduct.lift (Algebra.ofId C (Matrix κ κ C))
    ((Algebra.ofId ℤ_[p] C).mapMatrix.comp ρ) (fun _ _ => Algebra.commutes _ _)
  let j : OE →+* (C ⊗[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE)) :=
    (Algebra.TensorProduct.includeRight (R := ℤ_[p]) (A := C) (B := ℤ_[p] ⊗[ℤ] OE)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom
  have hj : ∀ a, j a = 1 ⊗ₜ (1 ⊗ₜ a) := fun a => rfl
  have hσ : ∀ a, σ (1 ⊗ₜ a) = algebraMap O C (tauExt τ a) := fun a => by simp [σ]
  have hρ : ∀ a, ρB (1 ⊗ₜ a) = (ρ a).map (algebraMap ℤ_[p] C) := fun a => by
    refine (Algebra.TensorProduct.lift_tmul _ _ _ _ _).trans ?_
    rw [map_one, _root_.one_mul]
    rfl
  have hmv : ∀ a x, ρB (1 ⊗ₜ a) *ᵥ (algebraMap ℤ_[p] C ∘ x) = algebraMap ℤ_[p] C ∘ (ρ a *ᵥ x) := by
    intro a x
    funext i
    rw [hρ]
    exact (RingHom.map_mulVec _ _ _ _).symm
  have hs : ∀ (c : C) (r : ℤ_[p]) (a : ℤ_[p] ⊗[ℤ] OE),
      (c ⊗ₜ[ℤ_[p]] (r • a)) = (r • c) • ((1 : C) ⊗ₜ[ℤ_[p]] a) := fun c r a => by
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have H := core (I := Fin w.n) (H := Fin h) σ j ?_ ((GlobalTheory.order_rep_diagonalisable C OE).2 _ _).2 ρB (1 ⊗ₜ w.e)
    (by rw [hσ, show tauExt τ w.e = 1 from hτ, map_one])
    (fun i => 1 ⊗ₜ (b i : ℤ_[p] ⊗[ℤ] OE)) ?_ (fun l => algebraMap ℤ_[p] C ∘ y l) ?_ ?_
  · rw [Fintype.card_fin] at H
    have h1 : ∀ a, ρB (j a) = ((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C) := by
      intro a
      rw [hj, hρ, Matrix.map_map]
      rfl
    have h2 : ∀ a, σ (j a) = ((algebraMap O C).comp τ) a := by
      intro a
      rw [hj, hσ]
      simp [tauExt]
    have h3 : (⨅ a : OE, Module.End.eigenspace (Matrix.toLin' (ρB (j a))) (σ (j a))) = ⨅ a : OE,
        Module.End.eigenspace (Matrix.toLin' (((ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)).map (algebraMap O C)))
          (((algebraMap O C).comp τ) a) := iInf_congr fun a => by rw [h1, h2]
    rw [h3] at H
    exact H
  · rw [eq_top_iff]
    rintro z -
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul c a =>
      induction a using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hx hy
      | tmul r a =>
        have : r ⊗ₜ[ℤ] a = r • ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        rw [this, hs]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | tmul c a =>
      have h1 := congrArg Subtype.val (b.sum_repr ⟨w.e * a, a, rfl⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, mul_comm a, ← h1, TensorProduct.tmul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · simp only [hmv]
    exact linearIndependent_algebraMap_comp_iff.2 hli
  · intro x
    simp only [hmv]
    rw [← Finset.univ_sum_single x, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    have h1 : (Pi.single k (x k) : κ → C) = x k • (algebraMap ℤ_[p] C ∘ (Pi.single k 1 : κ → ℤ_[p])) := by
      funext i
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    rw [h1, Matrix.mulVec_smul, hmv]
    refine Submodule.smul_mem _ _ ?_
    have h2 : ρ w.e *ᵥ (Pi.single k 1 : κ → ℤ_[p]) ∈ LinearMap.range (Matrix.mulVecLin (ρ w.e)) := ⟨_, rfl⟩
    rw [← hsp] at h2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun q => algebraMap ℤ_[p] C (c q), ?_⟩
    rw [← hc]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul]

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotentStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_place_basis_of_idempotent : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]) (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) → Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) → ∀ τ ∈ Emb (O := O) w.e, eigDim C (fun a : OE => (ρ (1 ⊗ₜ[ℤ] a)).map (algebraMap ℤ_[p] O)) ((algebraMap O C).comp τ) = h := by
  first | exact @GlobalTheory.ChF.eigDim_eq_of_basis | exact GlobalTheory.ChF.eigDim_eq_of_basis | (intros; apply GlobalTheory.ChF.eigDim_eq_of_basis <;> assumption)
end
end
