module

public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogISupInt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.RankOne

variable {K : Type} [Field K] [NumberField K]

theorem finsum_log_iSup_int {ι : Type} [Finite ι] {x : ι → 𝓞 K} (hx : x ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (⨆ i, v (x i)) = -Real.log (Ideal.absNorm (Ideal.span (Set.range x))) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  have hi : (x i₀ : K) ≠ 0 := by exact_mod_cast hi₀
  have hz : (fun i => (x i : K)) ≠ 0 := Function.ne_iff.2 ⟨i₀, hi⟩
  have hpos : ∀ v : FinitePlace K, 0 < ⨆ i, v (x i) := fun v =>
    lt_of_lt_of_le (FinitePlace.pos_iff.2 hi) (le_ciSup (f := fun i => v (x i)) (Set.finite_range _).bddAbove i₀)
  have h := NumberField.absNorm_mul_finprod_finitePlace_eq_one hx
  rw [← Real.log_finprod hpos, eq_inv_of_mul_eq_one_right h, Real.log_inv]

theorem finsum_log_iSup_div {n : ℕ} {b : Fin n → 𝓞 K} (hb : b ≠ 0) {d : 𝓞 K} (hd : d ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v ((b k : K) / d)) =
      Real.log (Ideal.absNorm (Ideal.span {d})) - Real.log (Ideal.absNorm (Ideal.span (Set.range b))) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hb
  have hi : (b i₀ : K) ≠ 0 := by exact_mod_cast hi₀
  have hd' : (d : K) ≠ 0 := by exact_mod_cast hd
  have hz : (fun i => (b i : K)) ≠ 0 := Function.ne_iff.2 ⟨i₀, hi⟩
  have hdz : (fun _ : Unit => d) ≠ 0 := Function.ne_iff.2 ⟨(), hd⟩
  have hdz' : (fun _ : Unit => (d : K)) ≠ 0 := Function.ne_iff.2 ⟨(), hd'⟩
  have h1 := finsum_log_iSup_int hb
  have h2 := finsum_log_iSup_int hdz
  have f1 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hz
  have f2 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hdz'
  rw [Set.range_const] at h2
  have e : ∀ v : FinitePlace K, Real.log (⨆ k, v ((b k : K) / d)) =
      Real.log (⨆ k, v (b k : K)) - Real.log (⨆ _ : Unit, v (d : K)) := fun v => by
    have hpos : 0 < ⨆ i, v (b i : K) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.2 hi) (le_ciSup (f := fun i => v (b i : K)) (Set.finite_range _).bddAbove i₀)
    have hv : 0 < v (d : K) := FinitePlace.pos_iff.2 hd'
    rw [ciSup_const, ← Real.log_div hpos.ne' hv.ne']
    congr 1
    simp only [div_eq_mul_inv, map_mul, map_inv₀]
    exact (Real.iSup_mul_of_nonneg (inv_nonneg.2 hv.le) _).symm
  simp only [e]
  rw [finsum_sub_distrib f1 f2, h1, h2]
  ring

end GlobalTheory.HSCore.RankOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndex
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.GaussFrac

variable {F : Type} [Field F] [NumberField F]

private theorem gaussAbs_eq_iSup_local {K ι : Type} [Field K] [NumberField K]
    (v : FinitePlace K) (g : MvPolynomial ι K) (s : Finset (ι →₀ ℕ))
    (hs : g.support ⊆ s) (hne : s.Nonempty) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs v g = ⨆ k : s, v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ)) := by
  classical
  have : Nonempty s := hne.to_subtype
  have hsup : (g.support.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) =
      s.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal := by
    refine le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)
    by_cases hm' : m ∈ g.support
    · exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) hm'
    · rw [MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]
      exact bot_le
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  rw [hsup]
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup s hne fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal
  rw [hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]
  refine le_antisymm (le_ciSup (f := fun k : s => v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ)))
    (Set.finite_range _).bddAbove ⟨k, hk⟩) (ciSup_le fun m => ?_)
  have h1 : (v (AddMonoidAlgebra.coeff g (m : ι →₀ ℕ))).toNNReal ≤ (v (AddMonoidAlgebra.coeff g k)).toNNReal := by
    rw [← hkeq]
    exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) m.2
  exact (Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1

def scaledIdeal (c : 𝓞 F) (I : Submodule (𝓞 F) F) : Ideal (𝓞 F) :=
  (I.map (LinearMap.lsmul (𝓞 F) F c)).comap (Algebra.linearMap (𝓞 F) F)

theorem absNorm_span_eq (c : 𝓞 F) (hc : c ≠ 0) (I : Submodule (𝓞 F) F) (h1I : 1 ≤ I)
    (hcI : ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) :
    Ideal.absNorm (Ideal.span {c}) =
      (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup * Ideal.absNorm (scaledIdeal c I) := by
  set ι : 𝓞 F →+ F := (Algebra.linearMap (𝓞 F) F).toAddMonoidHom
  set φ : F →+ F := (LinearMap.lsmul (𝓞 F) F c).toAddMonoidHom
  set A := (1 : Submodule (𝓞 F) F).toAddSubgroup
  set B := I.toAddSubgroup
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc
  have hφ : Function.Injective φ := fun x y h => by
    simp only [φ, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply] at h
    have h' : (c : F) * x = (c : F) * y := by simpa [Algebra.smul_def] using h
    exact mul_left_cancel₀ hc' h'
  have hA : (⊤ : AddSubgroup (𝓞 F)).map ι = A := by
    ext x; simp [ι, A, Submodule.mem_one]
  have hAB : A ≤ B := h1I
  have hBA : B.map φ ≤ A := by
    rintro _ ⟨y, hy, rfl⟩; exact hcI y hy
  have hAA : A.map φ ≤ B.map φ := AddSubgroup.map_mono hAB
  have e1 : (A.map φ).comap ι = (Ideal.span {c}).toAddSubgroup := by
    ext a
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, A, Submodule.mem_one, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, h⟩
      refine ⟨y, ?_⟩
      apply FaithfulSMul.algebraMap_injective (𝓞 F) F
      simp only [φ, ι, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply, Algebra.linearMap_apply, Algebra.smul_def] at h
      rw [map_mul, ← h, mul_comm]
    · rintro ⟨y, rfl⟩
      refine ⟨_, ⟨y, rfl⟩, ?_⟩
      simp only [φ, ι, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply, Algebra.linearMap_apply, Algebra.smul_def]
      rw [map_mul, mul_comm]
  have e2 : (B.map φ).comap ι = (scaledIdeal c I).toAddSubgroup := by
    ext a; rfl
  have k := AddSubgroup.relIndex_mul_relIndex _ _ _ hAA hBA
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hφ] at k
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot, Submodule.cardQuot, ← e1, ← e2,
    ← AddSubgroup.relIndex_top_right, ← AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_comap,
    AddSubgroup.relIndex_comap, hA, ← k]

theorem finsum_log_gaussAbs_le : ∀ (F : Type) [Field F] [NumberField F] (τ : Type) (g : MvPolynomial τ F), g ≠ 0 →
    ∀ (I : Submodule (𝓞 F) F) (δ : F), δ ≠ 0 → 1 ≤ I →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (∀ m, AddMonoidAlgebra.coeff g m / δ ∈ I) →
    ∑ᶠ q : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs q g) ≤
      Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup) +
        ∑ᶠ q : FinitePlace F, Real.log (q δ) := by
  intro F _ _ τ g hg I δ hδ h1I ⟨c, hc, hcI⟩ hcoef
  classical
  have hne : g.support.Nonempty := MvPolynomial.support_nonempty.2 hg
  set n := g.support.card
  set e := g.support.equivFin
  have hz : ∀ i : Fin n, ∃ z : 𝓞 F, algebraMap (𝓞 F) F z = c • (AddMonoidAlgebra.coeff g (e.symm i : τ →₀ ℕ) / δ) :=
    fun i => Submodule.mem_one.1 (hcI _ (hcoef _))
  choose b hb using hz
  have hc' : (c : F) ≠ 0 := by exact_mod_cast hc
  have hb' : ∀ i, (b i : F) = (c : F) * (AddMonoidAlgebra.coeff g (e.symm i : τ →₀ ℕ) / δ) := fun i => by
    simpa [Algebra.smul_def] using hb i
  have hcoeff : ∀ i : Fin n, AddMonoidAlgebra.coeff g (e.symm i : τ →₀ ℕ) = δ * ((b i : F) / c) := by
    intro i
    rw [hb' i]
    field_simp
  obtain ⟨m₀, hm₀⟩ := hne
  set i₀ := e ⟨m₀, hm₀⟩
  have hbi₀ : (b i₀ : F) ≠ 0 := by
    rw [hb' i₀]
    refine mul_ne_zero hc' (div_ne_zero ?_ hδ)
    simpa [i₀] using MvPolynomial.mem_support_iff.1 hm₀
  have hb0 : b ≠ 0 := Function.ne_iff.2 ⟨i₀, fun h => hbi₀ (by rw [h]; rfl)⟩
  have hz0 : (fun i => (b i : F) / c) ≠ 0 := Function.ne_iff.2 ⟨i₀, div_ne_zero hbi₀ hc'⟩
  have hloc : ∀ q : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs q g) =
      Real.log (q δ) + Real.log (⨆ i, q ((b i : F) / c)) := by
    intro q
    have hpos : 0 < ⨆ i, q ((b i : F) / c) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.2 (div_ne_zero hbi₀ hc'))
        (le_ciSup (f := fun i => q ((b i : F) / c)) (Set.finite_range _).bddAbove i₀)
    have hqδ : 0 < q δ := FinitePlace.pos_iff.2 hδ
    rw [← Real.log_mul hqδ.ne' hpos.ne', gaussAbs_eq_iSup_local q g g.support subset_rfl ⟨m₀, hm₀⟩,
      ← e.symm.iSup_comp, Real.mul_iSup_of_nonneg hqδ.le]
    congr 1
    refine iSup_congr fun i => ?_
    rw [hcoeff i, map_mul]
  have hs1 : (Function.support fun q : FinitePlace F => Real.log (q δ)).Finite :=
    (FinitePlace.hasFiniteMulSupport hδ).subset (by
      intro v hv h1; apply hv; simp only at h1 ⊢; rw [h1, Real.log_one])
  have hs2 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hz0
  rw [finsum_congr hloc, finsum_add_distrib hs1 hs2, GlobalTheory.HSCore.RankOne.finsum_log_iSup_div hb0 hc,
    GlobalTheory.GaussFrac.absNorm_span_eq c hc I h1I hcI]
  have hcN : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  rw [GlobalTheory.GaussFrac.absNorm_span_eq c hc I h1I hcI] at hcN
  have hR : (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0 := left_ne_zero_of_mul hcN
  have hJ : Ideal.absNorm (GlobalTheory.GaussFrac.scaledIdeal c I) ≠ 0 := right_ne_zero_of_mul hcN
  have hle : Ideal.span (Set.range b) ≤ GlobalTheory.GaussFrac.scaledIdeal c I := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    show algebraMap (𝓞 F) F (b i) ∈ I.map (LinearMap.lsmul (𝓞 F) F c)
    exact ⟨_, hcoef _, (hb i).symm⟩
  have hN : Ideal.absNorm (Ideal.span (Set.range b)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_eq_bot]
    intro h
    exact hbi₀ (by rw [h _ ⟨i₀, rfl⟩]; rfl)
  have hdvd := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (Ideal.absNorm_dvd_absNorm_of_le hle)
  push_cast
  rw [Real.log_mul (by exact_mod_cast hR) (by exact_mod_cast hJ)]
  have := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hJ) (show (Ideal.absNorm (GlobalTheory.GaussFrac.scaledIdeal c I) : ℝ) ≤ Ideal.absNorm (Ideal.span (Set.range b)) by exact_mod_cast hdvd)
  linarith

end GlobalTheory.GaussFrac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogGaussAbsLeFractionalIdealIndexStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_log_gaussAbs_le_fractionalIdeal_index : ∀ (F : Type) [Field F] [NumberField F] (τ : Type) (g : MvPolynomial τ F), g ≠ 0 → ∀ (I : Submodule (𝓞 F) F) (δ : F), δ ≠ 0 → 1 ≤ I → (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ I, c • y ∈ (1 : Submodule (𝓞 F) F)) → (∀ m, AddMonoidAlgebra.coeff g m / δ ∈ I) → ∑ᶠ q : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs q g) ≤ Real.log ((1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex I.toAddSubgroup) + ∑ᶠ q : FinitePlace F, Real.log (q δ) := by
  first | exact @GlobalTheory.GaussFrac.finsum_log_gaussAbs_le | exact GlobalTheory.GaussFrac.finsum_log_gaussAbs_le | (intros; apply GlobalTheory.GaussFrac.finsum_log_gaussAbs_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizati
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacFactor

open Matrix GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

@[reducible] def invTwoE : Invertible (2 : AE F E) :=
  (Invertible.map (algebraMap (AF F) (AE F E)) (2 : AF F)).copy 2 (map_ofNat _ 2).symm

theorem invOf_two_eq [Invertible (2 : AE F E)] :
    (⅟(2 : AE F E)) = algebraMap (AF F) (AE F E) (⅟(2 : AF F)) :=
  invOf_eq_right_inv (by rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, mul_invOf_self, map_one])

theorem valued_two {v : Pl (F := F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Valued.v (2 : Fv F v) = 1 := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (2 : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 h2] at this
  convert this using 2
  exact (map_ofNat _ 2).symm

theorem evFin_half_mem {v : Pl (F := F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) :
    evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := by
  have e : evFin F v (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h := congrArg Valued.v e
  rw [map_mul, valued_two h2, mul_one, map_one] at h
  rw [h]

theorem half_smul_mem {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {y : Fin d → AE F E}
    (hy : y ∈ GlobalTheory.InertSph.latAt W v) : (⅟(2 : AF F)) • y ∈ GlobalTheory.InertSph.latAt W v := by
  have hle : GlobalTheory.InertSph.latAt W v ≤ (GlobalTheory.InertSph.latAt W v).comap
      (DistribSMul.toAddMonoidHom (Fin d → AE F E) (⅟(2 : AF F))) := by
    show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro z ⟨a, ha, hint, y, hy, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply, smul_smul]
    refine AddSubgroup.subset_closure ⟨⅟(2 : AF F) * a, fun u hu => ?_, ?_, y, hy, rfl⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]; exact mul_mem (evFin_half_mem h2) hint
  exact hle hy

section Lat

variable {d : ℕ} {W : Spc F E d} {v : Pl (F := F)}

theorem latD_add {z w : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) (hw : w ∈ latD W v) : z + w ∈ latD W v :=
  ⟨add_mem hz.1 hw.1, add_mem hz.2 hw.2⟩

theorem latD_sub {z w : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) (hw : w ∈ latD W v) : z - w ∈ latD W v :=
  ⟨sub_mem hz.1 hw.1, sub_mem hz.2 hw.2⟩

theorem latD_half [Invertible (2 : AE F E)] (h2 : (2 : 𝓞 F) ∉ v.asIdeal) {z : Fin d ⊕ Fin d → AE F E}
    (hz : z ∈ latD W v) : (⅟(2 : AE F E)) • z ∈ latD W v := by
  rw [invOf_two_eq, algebraMap_smul]
  exact ⟨half_smul_mem h2 hz.1, half_smul_mem h2 hz.2⟩

theorem latD_diag {y : Fin d → AE F E} (hy : y ∈ GlobalTheory.InertSph.latAt W v) :
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1) *ᵥ y ∈ latD W v := by
  rw [fromRows_mulVec, one_mulVec]
  exact ⟨hy, hy⟩

theorem latD_anti {y : Fin d → AE F E} (hy : y ∈ GlobalTheory.InertSph.latAt W v) :
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1)) *ᵥ y ∈ latD W v := by
  rw [fromRows_mulVec, one_mulVec, neg_mulVec, one_mulVec]
  exact ⟨hy, neg_mem hy⟩

theorem lat_diagT {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [fromCols_mulVec, one_mulVec, one_mulVec]
  exact add_mem hz.1 hz.2

theorem lat_antiT {z : Fin d ⊕ Fin d → AE F E} (hz : z ∈ latD W v) :
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1)) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  rw [fromCols_mulVec, one_mulVec, neg_mulVec, one_mulVec]
  exact add_mem hz.1 (neg_mem hz.2)

end Lat

section Group

variable {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)}

theorem KD_mul {a b : UD σ W} (ha : a ∈ KD σ W v) (hb : b ∈ KD σ W v) : a * b ∈ KD σ W v := by
  have hm : matD (a * b) = matD a * matD b := rfl
  have hi : matD (a * b)⁻¹ = matD b⁻¹ * matD a⁻¹ := by rw [_root_.mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · rw [hm, show matD a * matD b - 1 = (matD a - 1) * matD b + (matD b - 1) by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel, smul_add, ← Matrix.smul_mul, ha.1 u hu, hb.1 u hu,
      Matrix.zero_mul, add_zero]
  · rw [hm, hi, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(ha.2 _ (hb.2 z hz).1).1, (hb.2 _ (ha.2 z hz).2).2⟩

theorem KD_inv {a : UD σ W} (ha : a ∈ KD σ W v) : a⁻¹ ∈ KD σ W v := by
  have h1 : matD a⁻¹ * matD a = 1 := by
    rw [show matD a⁻¹ * matD a = matD (a⁻¹ * a) from rfl, inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · rw [show matD a⁻¹ - 1 = -(matD a⁻¹ * (matD a - 1)) by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel,
      smul_neg, ← Matrix.mul_smul, ha.1 u hu, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(ha.2 z hz).2, (ha.2 z hz).1⟩

end Group

end GlobalTheory.DblVacFactor

namespace GlobalTheory.DblVacFactor

open Matrix GlobalTheory.DblVac GlobalTheory.BigCell

theorem factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  intro F E _ _ _ _ _ σ d W v h2 g hg hdet hC
  letI : Invertible (2 : AE F E) := invTwoE
  have hNt : (antiCols (F := F) (E := E) d)ᵀ = fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) := by
    rw [antiCols, transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  rw [hNt] at hdet hC
  unfold antiCols at hdet hC
  set G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := matD g with hGdef
  set f : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hf
  set J : Matrix (Fin d) (Fin d) (AE F E) := incM F W.J with hJ
  have hG : Gᵀ * dbl J * G.map f = dbl J := g.2
  have h1 : (1 : Matrix (Fin d) (Fin d) (AE F E)).map f = 1 := Matrix.map_one f (map_zero f) (map_one f)
  have hm1 : (-1 : Matrix (Fin d) (Fin d) (AE F E)).map f = -1 := by rw [Matrix.map_neg _ (map_neg f), h1]
  have hΔT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 1 := by
    rw [transpose_fromRows, transpose_one]
  have hNT : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))ᵀ =
      fromCols 1 (-1) := by
    rw [transpose_fromRows, transpose_one, transpose_neg, transpose_one]
  have hΔf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 1 := by rw [fromRows_map, h1]
  have hNf : (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)).map f =
      fromRows 1 (-1) := by rw [fromRows_map, h1, hm1]
  have hΔtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 1 := by rw [fromCols_map, h1]
  have hNtf : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)).map f =
      fromCols 1 (-1) := by rw [fromCols_map, h1, hm1]
  set D : Matrix (Fin d) (Fin d) (AE F E) := (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) :
    Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) with hDdef
  have hD : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hD' : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ hdet
  set M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) :=
    (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *
    ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹) *
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) with hMdef
  have hinv := mul_inv_eq (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E))
    (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) e1
    ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹)
  have hmem := mem_unitary f J (dbl J) G _ _ _ _ D⁻¹ hG hΔT hNT hΔf hΔtf hNf hNtf (e3 J) (e4 J) (e5 J) (e6 J) (e7 J) hD
  let P : GL (Fin d ⊕ Fin d) (AE F E) := ⟨1 + ⅟(2 : AE F E) • M, 1 - ⅟(2 : AE F E) • M, hinv.1, hinv.2⟩
  let p : UD σ W := ⟨P, hmem⟩
  have hdetS : IsUnit (⅟(2 : AE F E) • D).det := by
    rw [det_smul]
    exact ((isUnit_of_invertible (⅟(2 : AE F E))).pow _).mul hdet
  let s : GL (Fin d) (AE F E) := ((Matrix.isUnit_iff_isUnit_det _).mpr hdetS).unit

  have hΔtN : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) *
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = 0 := by
    simp [fromCols_mul_fromRows]
  have hMu : ∀ u : AF F, evFin F v u = 0 → u • M = 0 := by
    intro u hu
    have hE : (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * G *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
        (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * (G - 1) *
        (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hΔtN, sub_zero]
    have hu' : u • (G - 1) = 0 := hg.1 u hu
    calc u • M = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) * (u • (G - 1)) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * D⁻¹) * (fromCols (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d) (Fin d ⊕ Fin d) (AE F E)) := by
          rw [hMdef, hE]; simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = 0 := by rw [hu']; simp
  have hpK : p ∈ KD σ W v := by
    refine ⟨fun u hu => ?_, fun z hz => ⟨?_, ?_⟩⟩
    · show u • ((1 + ⅟(2 : AE F E) • M) - 1) = 0
      rw [add_sub_cancel_left, smul_comm, hMu u hu, smul_zero]
    · show (1 + ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_add hz (latD_half h2 (latD_diag (lat_diagT (hg.2 _ (latD_anti (hC _ (lat_antiT hz)))).1)))
    · show (1 - ⅟(2 : AE F E) • M) *ᵥ z ∈ latD W v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hMdef]
      simp only [← Matrix.mulVec_mulVec]
      exact latD_sub hz (latD_half h2 (latD_diag (lat_diagT (hg.2 _ (latD_anti (hC _ (lat_antiT hz)))).1)))
  refine ⟨p, p⁻¹ * g, hpK, ⟨1, ?_⟩, KD_mul (KD_inv hpK) hg, ⟨s, ?_⟩, (mul_inv_cancel_left p g).symm⟩
  · have key : ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hMdef, Matrix.mul_assoc _ _ (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)), e1, Matrix.mul_zero,
        smul_zero, add_zero]
    show ((1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) + ⅟(2 : AE F E) • M) * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) =
      (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) 1 : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * ((1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E))
    rw [Units.val_one, Matrix.mul_one]
    exact key
  · show (1 - ⅟(2 : AE F E) • M) * G * (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) = (fromRows (1 : Matrix (Fin d) (Fin d) (AE F E)) (-1) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) * (s : Matrix (Fin d) (Fin d) (AE F E))
    rw [IsUnit.unit_spec]
    exact q_col G _ _ _ _ D⁻¹ e2 hD'

end GlobalTheory.DblVacFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumLatticeStabilizerBigCellFactorizatiStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuumLatticeStabilizer_bigCell_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (W : Spc F E d) (v : Pl (F := F)), (2 : 𝓞 F) ∉ v.asIdeal → ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
    IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d).det →
    (∀ z ∈ GlobalTheory.InertSph.latAt W v,
      ((GlobalTheory.DblVac.antiCols (F := F) (E := E) d)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols d)⁻¹ *ᵥ z ∈
        GlobalTheory.InertSph.latAt W v) →
    ∃ p q : GlobalTheory.DblVac.UD σ W, p ∈ GlobalTheory.DblVac.KD σ W v ∧ p ∈ GlobalTheory.DblVac.PDiag σ W ∧
      q ∈ GlobalTheory.DblVac.KD σ W v ∧ q ∈ GlobalTheory.DblVac.PAnti σ W ∧ g = p * q := by
  first | exact @GlobalTheory.DblVacFactor.factor | exact GlobalTheory.DblVacFactor.factor | (intros; apply GlobalTheory.DblVacFactor.factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatum
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.RowSpace

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]


variable (p O) in
def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by
    show WittVector.fontaineTheta O p (_ ^[n] 1) = 1
    rw [iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

theorem ghostHom_apply (n : ℕ) (a : Ainf p O) : ghostHom p O n a = ghost p O n a := rfl

def dotLin {R : Type} [CommRing R] {h : ℕ} (v : Fin h → R) : (Fin h → R) →ₗ[R] R where
  toFun w := v ⬝ᵥ w
  map_add' := dotProduct_add v
  map_smul' c w := by simp [dotProduct_smul]

theorem dotLin_apply {R : Type} [CommRing R] {h : ℕ} (v w : Fin h → R) : dotLin v w = v ⬝ᵥ w := rfl

def toA {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (t : G.Tate) :
    Fin h → Ainf p O := fun i => ofPadic p O (e t i)

theorem toA_add {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (t t' : G.Tate) : toA e (t + t') = toA e t + toA e t' := by
  ext i; simp [toA]

theorem toA_smul {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (c : ℤ_[p]) (t : G.Tate) : toA e (c • t) = ofPadic p O c • toA e t := by
  ext i; simp [toA]

theorem toA_single {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (i : Fin h) : toA e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
  ext j; by_cases hij : j = i <;> simp [toA, Pi.single_apply, hij]

theorem toO_single {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (i : Fin h) : toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
  ext j; by_cases hij : j = i <;> simp [toO, Pi.single_apply, hij]

def rowMap {G : PDivGroup p O} {h : ℕ} (F : Matrix (Fin h) (Fin h) (Ainf p O))
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) : (Fin h → Ainf p O) →ₗ[Ainf p O] TDual G where
  toFun r :=
    { toFun := fun t => r ⬝ᵥ (F *ᵥ toA e t)
      map_add' := fun t t' => by rw [toA_add, mulVec_add, dotProduct_add]
      map_smul' := fun c t => by
        rw [toA_smul, mulVec_smul, dotProduct_smul] }
  map_add' r r' := LinearMap.ext fun t => add_dotProduct r r' _
  map_smul' a r := LinearMap.ext fun t => smul_dotProduct a r _

theorem rowMap_apply {G : PDivGroup p O} {h : ℕ} (F : Matrix (Fin h) (Fin h) (Ainf p O))
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (r : Fin h → Ainf p O) (t : G.Tate) :
    rowMap F e r t = r ⬝ᵥ (F *ᵥ toA e t) := rfl

theorem F_map_ghost {ε : PreTilt O p} {h : ℕ} (D : Datum ε h ℤ_[p])
    (hphi : ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a) (n : ℕ) :
    ∃ X : Matrix (Fin h) (Fin h) O,
      D.F.map (ghostHom p O n) = X * D.F.map (WittVector.fontaineTheta O p) := by
  induction n with
  | zero => exact ⟨1, by rw [Matrix.one_mul]; rfl⟩
  | succ n ih =>
    obtain ⟨X, hX⟩ := ih
    refine ⟨D.Ψ.map (ghostHom p O (n + 1)) * X, ?_⟩
    have e1 : D.F.map (ghostHom p O (n + 1)) =
        D.Ψ.map (ghostHom p O (n + 1)) * D.F.map (ghostHom p O n) := by
      conv_lhs => rw [D.F_eq]
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hphi n _
    rw [e1, hX, Matrix.mul_assoc]

theorem G_map_ghost {ε : PreTilt O p} {h : ℕ} (D : Datum ε h ℤ_[p])
    (hG : D.G = D.G.map (phiInv p O) * D.Ψ')
    (hphi : ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a) (n : ℕ) :
    ∃ Y : Matrix (Fin h) (Fin h) O,
      D.G.map (ghostHom p O n) = D.G.map (WittVector.fontaineTheta O p) * Y := by
  induction n with
  | zero => exact ⟨1, by rw [Matrix.mul_one]; rfl⟩
  | succ n ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨Y * D.Ψ'.map (ghostHom p O (n + 1)), ?_⟩
    have e1 : D.G.map (ghostHom p O (n + 1)) =
        D.G.map (ghostHom p O n) * D.Ψ'.map (ghostHom p O (n + 1)) := by
      conv_lhs => rw [hG]
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hphi n _
    rw [e1, hY, Matrix.mul_assoc]

end SlopeTestRemainingChoices

theorem latt_eq_rowSpace : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (h : ℕ) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (fil : G.dual.omega ≃ₗ[O] D.Fil), (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O)) → ∃ L : (Fin h → Ainf p O) ≃ₗ[Ainf p O] latt G, ∀ r t, (L r).1 t = r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G h D e fil hal
  obtain ⟨-, hofP, hmu, -, -, hphi⟩ := GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  haveI := hdom
  have hμ : Sandwich.mu ε ≠ 0 := by
    rw [← xi_mul_nu]
    exact mul_ne_zero hξ fun h0 => hν (by rw [h0, map_zero])
  have hFG : D.F * D.G = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    GlobalTheory.SelfDualFil.mul_eq_smul_comm hμ D.G_mul_F
  have hGeq := GlobalTheory.SelfDualFil.G_eq hμ hξ D
  have hθμ : WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 := hmu 0

  have hzero : ∀ X Y : Matrix (Fin h) (Fin h) (Ainf p O), X * Y = Sandwich.mu ε • 1 →
      ∀ w : Fin h → O, X.map (WittVector.fontaineTheta O p) *ᵥ
        (Y.map (WittVector.fontaineTheta O p) *ᵥ w) = 0 := by
    intro X Y hXY w
    rw [mulVec_mulVec, ← Matrix.map_mul, hXY]
    ext i
    simp [Matrix.mulVec, dotProduct, hθμ]
  have halFil : ∀ w, D.al w ∈ D.Fil := fun w => by
    rw [Datum.Fil, LinearMap.mem_ker, Datum.bb, Datum.al, toLin'_apply, toLin'_apply]
    exact hzero _ _ D.G_mul_F w
  have halbb : ∀ u, D.al (D.bb u) = 0 := fun u => by
    rw [Datum.bb, Datum.al, toLin'_apply, toLin'_apply]
    exact hzero _ _ hFG u

  have hghostA : ∀ n t, (ghostHom p O n) ∘ toA e t = toO e t := fun n t =>
    funext fun i => hofP n _
  have hmem : ∀ r, rowMap D.F e r ∈ latt G := by
    intro r n
    obtain ⟨X, hX⟩ := F_map_ghost D hphi n
    refine ⟨dotLin ((ghostHom p O n ∘ r) ᵥ* X) ∘ₗ (D.Fil.subtype ∘ₗ fil.toLinearMap),
      fun t => ?_⟩
    rw [rowMap_apply, ← ghostHom_apply, RingHom.map_dotProduct]
    have e1 : (ghostHom p O n) ∘ (D.F *ᵥ toA e t) = X *ᵥ D.al (toO e t) := by
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hghostA, hX, ← mulVec_mulVec, Datum.al,
        toLin'_apply]
    rw [e1, hal, dotProduct_mulVec]
    rfl
  let Φ := (rowMap D.F e).codRestrict (latt G) hmem
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : ∀ t, r ⬝ᵥ (D.F *ᵥ toA e t) = 0 := fun t =>
      congrArg (fun y : latt G => y.1 t) hr
    have h2 : r ᵥ* D.F = 0 := by
      funext i
      have := h1 (e.symm (Pi.single i 1))
      rw [toA_single, dotProduct_mulVec] at this
      simpa using this
    have h3 : Sandwich.mu ε • r = 0 := by
      have := congrArg (fun z => z ᵥ* D.G) h2
      simp only [vecMul_vecMul, hFG, vecMul_smul, vecMul_one, zero_vecMul] at this
      exact this
    exact (smul_eq_zero.1 h3).resolve_left hμ
  have hsurj : Function.Surjective Φ := by
    intro y
    set s : Fin h → Ainf p O := fun i => y.1 (e.symm (Pi.single i 1)) with hs
    have hy : ∀ t, y.1 t = s ⬝ᵥ toA e t := by
      intro t
      have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
        apply e.injective
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [ht]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [LinearMap.map_smulₛₗ, dotProduct, toA, smul_eq_mul, s]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hdiv : ∀ j, Sandwich.mu ε ∣ (s ᵥ* D.G) j := by
      intro j
      refine GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero p C v O hv ε hε _ fun n => ?_
      obtain ⟨x, hx⟩ := y.2 n
      set gs : Fin h → O := ghostHom p O n ∘ s with hgs
      have hgt : ∀ t, gs ⬝ᵥ toO e t = x (hodgeTate G t) := by
        intro t
        rw [← hx, hy, ← ghostHom_apply, RingHom.map_dotProduct, hghostA]
      have hl : dotLin gs = x ∘ₗ fil.symm.toLinearMap ∘ₗ D.al.codRestrict D.Fil halFil := by
        refine (Pi.basisFun O (Fin h)).ext fun i => ?_
        rw [Pi.basisFun_apply, ← toO_single e i, dotLin_apply, hgt]
        have e2 : D.al.codRestrict D.Fil halFil (toO e (e.symm (Pi.single i 1))) =
            fil (hodgeTate G (e.symm (Pi.single i 1))) := Subtype.ext (hal _)
        simp only [LinearMap.comp_apply, e2, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      have hbb : gs ᵥ* D.G.map (WittVector.fontaineTheta O p) = 0 := by
        funext k
        have e3 := LinearMap.congr_fun hl (D.bb (Pi.single k 1))
        have e4 : D.al.codRestrict D.Fil halFil (D.bb (Pi.single k 1)) = 0 :=
          Subtype.ext (halbb _)
        rw [LinearMap.comp_apply, LinearMap.comp_apply, e4, map_zero, map_zero] at e3
        simp only [dotLin_apply, Datum.bb, toLin'_apply, dotProduct_mulVec] at e3
        simpa using e3
      obtain ⟨Y, hY⟩ := G_map_ghost D hGeq hphi n
      rw [← ghostHom_apply, RingHom.map_vecMul, hY, ← vecMul_vecMul, ← hgs, hbb, zero_vecMul]
      rfl
    choose r hr using hdiv
    have h1 : s ᵥ* D.G = Sandwich.mu ε • r := funext fun j => hr j
    have h2 : r ᵥ* D.F = s := by
      apply smul_right_injective (Fin h → Ainf p O) hμ
      change Sandwich.mu ε • (r ᵥ* D.F) = Sandwich.mu ε • s
      rw [← smul_vecMul, ← h1, vecMul_vecMul, D.G_mul_F, vecMul_smul, vecMul_one]
    refine ⟨r, Subtype.ext (LinearMap.ext fun t => ?_)⟩
    change r ⬝ᵥ (D.F *ᵥ toA e t) = y.1 t
    rw [hy, dotProduct_mulVec, h2]
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun r t => rfl⟩

end GlobalTheory.PDivLat.RowSpace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatumStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_lattice_eq_rowSpace_of_sandwich_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (h : ℕ) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (fil : G.dual.omega ≃ₗ[O] D.Fil), (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O)) → ∃ L : (Fin h → Ainf p O) ≃ₗ[Ainf p O] latt G, ∀ r t, (L r).1 t = r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i)) := by
  first | exact @GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace | exact GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace | (intros; apply GlobalTheory.PDivLat.RowSpace.latt_eq_rowSpace <;> assumption)
end
end
