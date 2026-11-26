module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic.HeightExists

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Twist GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.QCoh

attribute [local instance] MvPolynomial.gradedAlgebra

section Algebra

variable {k K σ : Type} [Field k] [Field K] [Algebra k K]

def coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) : MvPolynomial σ k :=
  ∑ a ∈ g.support, monomial a (l (AddMonoidAlgebra.coeff g a))

theorem coeff_coeffMap (l : K →ₗ[k] k) (g : MvPolynomial σ K) (a : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (coeffMap l g) a = l (AddMonoidAlgebra.coeff g a) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem isHomogeneous_coeffMap (l : K →ₗ[k] k) {g : MvPolynomial σ K} {d : ℕ} (hg : g.IsHomogeneous d) :
    (coeffMap l g).IsHomogeneous d := fun a ha =>
  hg fun h => ha (by rw [coeff_coeffMap, h, map_zero])

theorem mem_map_of_coeffMap {I : Ideal (MvPolynomial σ k)} {g : MvPolynomial σ K}
    (h : ∀ l : K →ₗ[k] k, coeffMap l g ∈ I) :
    g ∈ I.map (MvPolynomial.map (algebraMap k K) : MvPolynomial σ k →+* MvPolynomial σ K) := by
  classical
  let b := Module.Basis.ofVectorSpace k K
  let s := g.support.biUnion fun a => (b.repr (AddMonoidAlgebra.coeff g a)).support
  have e : g = ∑ i ∈ s, C (b i) * map (algebraMap k K) (coeffMap (b.coord i) g) := by
    ext a
    simp only [coeff_sum, coeff_C_mul, coeff_map, coeff_coeffMap]
    have hs : (b.repr (AddMonoidAlgebra.coeff g a)).support ⊆ s := by
      by_cases ha : a ∈ g.support
      · exact Finset.subset_biUnion_of_mem (fun a => (b.repr (AddMonoidAlgebra.coeff g a)).support) ha
      · simp [notMem_support_iff.1 ha]
    conv_lhs => rw [← b.linearCombination_repr (AddMonoidAlgebra.coeff g a),
      Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hs _ (by simp)]
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl
  rw [e]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (h _))

theorem le_of_ringKrullDim_coneIdeal {N D e : ℕ} (y : Fin N → K) (hD : Algebra.trdeg k K = D)
    (he : ringKrullDim (MvPolynomial (Fin N) k ⧸ coneIdeal k y) = (e + 1 : ℕ)) : e ≤ D := by
  have := isPrime_coneIdeal (K := k) y
  obtain ⟨d, h1, h2⟩ := exists_ringKrullDim_eq_and_trdeg_eq k (MvPolynomial (Fin N) k ⧸ coneIdeal k y)
  obtain rfl : d = e + 1 := by exact_mod_cast h1.symm.trans he
  have h3 := trdeg_le_of_injective (Ideal.kerLiftAlg (coneMap k y)) (Ideal.kerLiftAlg_injective _)
  rw [← trdeg_add_eq k K (A := Polynomial K), Polynomial.trdeg_of_isDomain, hD] at h3
  have h4 : ((e + 1 : ℕ) : Cardinal.{0}) ≤ ((D + 1 : ℕ) : Cardinal.{0}) := by
    rw [← h2, Nat.cast_add, Nat.cast_one]; exact h3
  have : e + 1 ≤ D + 1 := by exact_mod_cast h4
  omega

end Algebra

variable {k : Type} [Field k] (S : LinSys k)

theorem chartEval_eq_zero {g : MvPolynomial (Fin S.N) k} {d : ℕ} (hg : g.IsHomogeneous d) (h : g ∈ S.imageIdeal)
    (i : S.L.ι) {W : S.Y.Opens} (hle : W ≤ S.L.U i) : chartEval k S.b i hle g = 0 := by
  have e : resG _ hle (zfun (S.form hg) i) = 0 := by
    rw [(S.mem_imageIdeal_iff hg).1 h]
    exact (congrArg _ (zfun_zero i)).trans (map_zero _)
  rwa [LinSys.form, zfun_formSec, resG_chartEval] at e

theorem coeffMap_mem_imageIdeal (E : Type) [Field E] [Algebra k E] {g : MvPolynomial (Fin S.N) E} {d : ℕ}
    (hg : g.IsHomogeneous d) (h : g ∈ (S.baseChange E).imageIdeal) (l : E →ₗ[k] k) :
    coeffMap l g ∈ S.imageIdeal := by
  refine (S.mem_imageIdeal_iff (isHomogeneous_coeffMap l hg)).2 (zglobal_ext fun i => ?_)
  rw [zfun_zero, LinSys.form, zfun_formSec]
  refine S.Y.sheaf.eq_of_locally_eq' (fun W : {W : S.Y.affineOpens // W.1 ≤ S.L.U i} => W.1.1) _
    (fun W => homOfLE W.2) (fun y hy => ?_) _ _ fun W => ?_
  · obtain ⟨V, hV, hx, hle⟩ := exists_isAffineOpen_mem_and_subset (U := S.L.U i) (x := y) hy
    exact Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hle⟩, hx⟩
  obtain ⟨⟨W, hW⟩, hle⟩ := W
  have H := S.isPullback_baseChange E
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := W) le_top le_top
    (UY := S.bcFst E ⁻¹ᵁ W) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hW)
  have po' : IsPushout ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ S.str.appLE ⊤ W le_top)
      (CommRingCat.ofHom (algebraMap k E)) ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl)
      ((Scheme.ΓSpecIso (CommRingCat.of E)).inv ≫
        (S.baseChange E).str.appLE ⊤ (S.bcFst E ⁻¹ᵁ W) le_top) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _)
      (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  obtain ⟨Λ, hΛ⟩ := IndepBaseChange.exists_contract po' l
  have hle' : S.bcFst E ⁻¹ᵁ W ≤ (S.baseChange E).L.U fun _ => i :=
    fun y hy => Set.mem_iInter.2 fun _ => hle hy
  have e := (eval₂_eq _ _ _).symm.trans (chartEval_eq_zero (S.baseChange E) hg h (fun _ => i) hle')
  have e' : ∀ j, resG (S.baseChange E).Y hle' (((S.baseChange E).b j).f fun _ => i) =
      ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom (resG S.Y hle ((S.b j).f i)) := fun j => by
    have a := (S.bcFst E).appLE_map (U := S.L.U i) (V := (S.baseChange E).L.U fun _ => i)
      (fun y hy => Set.mem_iInter.1 hy PUnit.unit) (homOfLE hle').op
    have b := (S.bcFst E).map_appLE (U := W) (V := S.bcFst E ⁻¹ᵁ W) le_rfl (homOfLE hle).op
    exact congrArg (fun g => g.hom ((S.b j).f i)) (a.trans b.symm)
  have e₂ := congrArg Λ e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at e₂
  refine (resG_chartEval k S.b i le_rfl hle _).trans (Eq.trans ?_ (e₂.trans (map_zero _).symm))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeffMap, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chartEval, eval₂Hom_monomial]
  refine Eq.trans (hΛ (AddMonoidAlgebra.coeff g a) (a.prod fun j n => resG S.Y hle ((S.b j).f i) ^ n)).symm (congrArg Λ ?_)
  refine congrArg₂ (· * ·) rfl ?_
  refine (map_prod ((S.bcFst E).appLE W (S.bcFst E ⁻¹ᵁ W) le_rfl).hom _ _).trans
    (Finset.prod_congr rfl fun j _ => ?_)
  exact (map_pow _ _ _).trans (congrArg (· ^ _) (e' j).symm)

theorem del_eq_zero (hp : IsProjOver S.str) (s : Fin S.D → S.L.Sec) (hs : ∀ y, ∃ i, y ∈ nonzeroLocus (s i)) :
    S.del = 0 := by
  have := isNoetherian_of_isProjOver hp
  have key := CutDegree.interNum_eq_sum_length S.str hp S.isLB S.chartAt S.mem_chartAt ∅ (by simp) (List.ofFn s)
    (structureModule S.Y) (fun x _ hx => by
      obtain ⟨i, hi⟩ := hs x
      exact (hx _ (List.mem_ofFn.2 ⟨i, rfl⟩) hi).elim) (by simp)
  have e : topSelfIntersection k S.L S.D = topSelfIntersection k S.L (List.ofFn s).length := by rw [List.length_ofFn]
  rw [LinSys.del, e, topSelf_def]
  exact key

variable {S}

theorem isIntegral (h : S.IsVariety) : IsIntegral S.Y := by
  have := h.smooth
  have := h.conn
  have : Smooth S.str := SmoothOfRelativeDimension.smooth S.D S.str
  have := geometricallyIntegral_of_smooth S.str
  exact GeometricallyIntegral.isIntegral_of_subsingleton S.str

theorem exists_generic (h : S.IsVariety) : ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra k Ω) (x : S.Pt Ω),
    IsGenericPoint (ptOf x.1) Set.univ ∧ Algebra.trdeg k Ω = S.D := by
  have := isIntegral h
  have hg := genericPoint_spec S.Y
  refine ⟨S.Y.residueField (genericPoint S.Y), inferInstance, (S.baseHom (resPt _)).toAlgebra,
    ⟨resPt _, S.comp_str _⟩, by rw [ptOf_resPt]; exact hg, ?_⟩
  exact (residueField_fg_trdeg_of_smoothOfRelativeDimension S.str S.D h.smooth _
    fun y hy => (hy.antisymm (hg.specializes trivial)).eq).2

theorem map_imageIdeal (h : S.IsVariety) (E : Type) [Field E] [Algebra k E] :
    S.imageIdeal.map (MvPolynomial.map (algebraMap k E) : MvPolynomial (Fin S.N) k →+* MvPolynomial (Fin S.N) E) =
      (S.baseChange E).imageIdeal := by
  refine le_antisymm ?_ (Ideal.span_le.2 ?_)
  · have := isIntegral (h.baseChange E)
    obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic (h.baseChange E)
    let : Algebra k Ω := ((algebraMap E Ω).comp (algebraMap k E)).toAlgebra
    have : IsScalarTower k E Ω := .of_algebraMap_eq' rfl
    obtain ⟨c, hc, e⟩ := S.exists_coords_baseChange E x.1
    rw [imageIdeal_eq_coneIdeal_of_generic E Ω _ x hx c _ hc e]
    refine Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)
    rintro g ⟨d, hg, h0⟩
    refine (mem_coneIdeal_of_isHomogeneous _ (hg.map (algebraMap k E))).2 ?_
    have h1 := S.eval₂_coords_eq_zero (LinSys.toBase x).1 ((S.mem_imageIdeal_iff hg).2 h0)
    rw [LinSys.baseHom_ptOver] at h1
    exact (aeval_map_algebraMap E _ g).trans h1
  · rintro g ⟨d, hg, h0⟩
    exact mem_map_of_coeffMap
      (coeffMap_mem_imageIdeal S E hg (((S.baseChange E).mem_imageIdeal_iff hg).2 h0))

theorem isPrime_imageIdeal (h : S.IsVariety) : S.imageIdeal.IsPrime := by
  have := isIntegral h
  obtain ⟨Ω, _, _, x, hx, -⟩ := exists_generic h
  rw [imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm]
  exact isPrime_coneIdeal _

theorem del_eq_zero_of_lt [Infinite k] (hp : IsProjOver S.str) (hb : S.BasePointFree) {e δ : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin S.N) k} (hf : IsChowFormInt S.imageIdeal e δ f) (he : e < S.D) :
    S.del = 0 := by
  obtain ⟨u, hu⟩ : ∃ u, eval u f ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hf.ne_zero (MvPolynomial.funext fun u => by rw [hc, map_zero])
  refine del_eq_zero S hp (fun i => if hi : (i : ℕ) < e + 1 then S.comb fun j => u (⟨i, hi⟩, j) else 0) fun y => ?_
  by_contra hc
  push Not at hc
  let Ω := AlgebraicClosure (S.Y.residueField y)
  let x : Sp Ω ⟶ S.Y := spMap (algebraMap (S.Y.residueField y) Ω) ≫ resPt y
  have hx : ptOf x = y := (ptOf_spMap_comp _ _).trans (ptOf_resPt y)
  let : Algebra k Ω := (S.baseHom x).toAlgebra
  have h1 := (hf.zero_iff_of_isAlgClosed S.isHomogeneous_imageIdeal fun p => algebraMap k Ω (u p)).2
    ⟨S.coords x, hb.coords_ne_zero x, fun g hg => S.eval₂_coords_eq_zero x hg, fun i => by
      have h2 := hc ⟨i, by omega⟩
      rw [dite_eq_left i.2, ← hx, ← S.val_ne_zero_iff, not_not, S.val_comb] at h2
      exact h2⟩
  exact hu ((map_eq_zero (algebraMap k Ω)).1 ((aeval_algebraMap_apply Ω u f).symm.trans h1))

theorem ringKrullDim_imageIdeal [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ringKrullDim (MvPolynomial (Fin S.N) k ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  have := isIntegral h
  have hp := isPrime_imageIdeal h
  obtain ⟨Ω, _, _, x, hx, hD⟩ := exists_generic h
  have hI := imageIdeal_eq_coneIdeal_of_generic k Ω S x hx 1 _ one_ne_zero (one_smul _ _).symm
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (hb.coords_ne_zero x.1)
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ S.isHomogeneous_imageIdeal (i := j)
    fun hX => hj (by simpa using S.eval₂_coords_eq_zero x.1 hX)
  obtain ⟨f, hf⟩ := ChowExists.exists_isChowFormInt hp S.isHomogeneous_imageIdeal he
  obtain rfl : e = S.D := le_antisymm (le_of_ringKrullDim_coneIdeal _ hD (hI ▸ he))
    (not_lt.1 fun hlt => hd (del_eq_zero_of_lt h.proj hb hf hlt))
  exact he

theorem exists_isChowForm [CharZero k] (h : S.IsVariety) (hb : S.BasePointFree) (hd : S.del ≠ 0) :
    ∃ f, IsChowForm S.imageIdeal S.D (hilbertDegree S.imageIdeal) f :=
  ChowExists.exists_isChowForm S.isHomogeneous_imageIdeal
    (by rw [map_imageIdeal h]; exact isPrime_imageIdeal (h.baseChange _)) (ringKrullDim_imageIdeal h hb hd)

theorem exists_isHeight : ∀ (F : Type) [Field F] [NumberField F] (T : HermSys F),
    T.IsAlgebraicData → 0 < T.del → ∃ h, T.IsHeight h := fun _ _ _ T h hd =>
  have ⟨_, hf⟩ := exists_isChowForm h.variety h.bpf hd.ne'
  ⟨_, T.isHeight_of_isChowForm hf⟩

end GlobalTheory.Adelic.HeightExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChiDetSplitCentre
noncomputable section

open NumberField MeasureTheory Matrix Polynomial Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspRep.Central
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume

namespace GlobalTheory.CuspQuot

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem commute_Zalg {T : Module.End ℂ (Sm E a)} (hT : ∀ X, Commute T (lie E a X)) {z : Module.End ℂ (Sm E a)}
    (hz : z ∈ Zalg E a) : Commute T z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {T}
  have hS : ∀ {z}, z ∈ S ↔ Commute T z := by
    intro z
    simp [S, Subalgebra.mem_centralizer_iff, Commute, SemiconjBy]
  have hV : ∀ X, lie E a X ∈ S := fun X => hS.2 (hT X)
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hV _) (S.smul_mem (hV _) _)) _
  refine hS.1 ((Algebra.adjoin_le (S := S) ?_) hz)
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem


variable (E) in
def cpowChar (s : ℂ) : HChar E :=
  ⟨MonoidHom.toHomUnits
      { toFun := fun x => Complex.exp (s * Real.log (ideleNorm (E := E) x))
        map_one' := by simp
        map_mul' := fun x y => by
          rw [map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _), ← Complex.exp_add]
          push_cast; ring_nf },
    Units.isEmbedding_val₀.continuous_iff.2 (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ideleNorm.log fun _ => ideleNorm_ne_zero _)))),
    fun k => Units.ext (by
      have h := ideleNorm_principalIdele (E := E) k
      exact (congrArg (fun r : ℝ => Complex.exp (s * Real.log r)) h).trans (by simp))⟩

theorem exists_chiDet_splitCentre (ha : 0 < a) (c : ℂ) :
    ∃ χ : HChar E, ∀ t : ℝ, ((chiDet a χ (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (c * t) := by
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a t)))) fun x y => by
      rw [splitCentre_add, map_mul, map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (continuous_ideleNorm.comp (GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a 1)))
    rw [det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast ha) (Real.log_pos (one_lt_ideleNorm_eIdele E))
  refine ⟨cpowChar E (c / D 1), fun t => ?_⟩
  change Complex.exp (c / D 1 * (D t : ℝ)) = _
  have : (D 1 : ℂ) ≠ 0 := by exact_mod_cast hD1.ne'
  rw [hDt t]; push_cast
  congr 1; field_simp

end GlobalTheory.CuspQuot

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
set_option autoImplicit false

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open GlobalTheory.FlagTan GlobalTheory.FlatLine
open scoped ENNReal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem fChart_exists_val {h : GenFrEx Xo c} (C : Reg.FChart h) {e : Formalism.L2.Pj.Ix Dw → ℤ} {f : Rul Xo c}
    (hf : f ∈ secZ Xo c e) : ∃ b : C.R, (b : Om C.Z) = ((∏ i, C.t i ^ e i : (Om C.Z)ˣ) : Om C.Z) * genVal C.Z f ∧
      ∀ (S : Type) [CommRing S] [Algebra c.F S] (ψ : C.R →ₐ[c.F] S) (z : FrPt Xo c S), FrMap ψ C.y z →
        evR Xo c f z = ψ b := by
  have hL : Reg.EvLaws Xo c := (Reg.evLaws_genFr_atlas E H Dw l Xo c).1
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test C.R C.y
  refine ⟨χ (f q y₀), ?_, fun S _ _ ψ z hz => ?_⟩
  · rw [genVal_apply h, evC, ← evR_frBor hf C.bor,
      evR_eq hf.1 (frMap_comp (χ := C.R.val.comp χ) hy₀ C.gen fun _ => rfl)]
    rfl
  · rw [evR_eq hf.1 (frMap_comp (χ := ψ.comp χ) hy₀ hz fun _ => rfl), AlgHom.comp_apply]

theorem genVal_idem_self (Z : Comp Xo c) : genVal Z (idem Z) = 1 := by
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  rw [genVal_apply h, evC]
  exact evR_idem (liesOn_genFr h Z) (fromTest_of_isLocalRing _)

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem fChart_evR_idem {h : GenFrEx Xo c} (C : Reg.FChart h) {S : Type} [CommRing S] [Algebra c.F S]
    {ψ : C.R →ₐ[c.F] S} {z : FrPt Xo c S} (hz : FrMap ψ C.y z) : evR Xo c (idem C.Z) z = 1 := by
  obtain ⟨b, hb, hb'⟩ := fChart_exists_val C (idem_mem_secZ C.Z)
  have : b = 1 := Subtype.ext (by simpa [genVal_idem_self] using hb)
  rw [hb' S ψ z hz, this, map_one]

theorem exists_fChart (h : GenFrEx Xo c) (Z : Comp Xo c) : ∃ C : Reg.FChart h, C.Z = Z := by
  obtain ⟨C, ψ, z, t', hz, hb⟩ := (Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h (Om Z) (genFr h Z)
  refine ⟨C, by_contra fun hne => ?_⟩
  have h1 : evR Xo c (idem C.Z) (genFr h Z) = 0 := evC_eq_zero h (Ne.symm hne) (idem_mem_suppOn C.Z)
  rw [evR_frBor (idem_mem_secZ C.Z) hb, fChart_evR_idem C hz] at h1
  simp at h1

attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem exists_chart_read_at_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r), IsUnf U → ∀ Z : Comp Xo c, ∃ (R : Subalgebra c.F (Om Z)) (_ : Algebra.FiniteType c.F R) (t : Formalism.L2.Pj.Ix Dw → (Om Z)ˣ), (∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f ∈ R) ∧ ∀ φ : R →+* ℂ, φ.comp (algebraMap c.F R) = σ → ∃ z ∈ framesOn U Z, ∃ s : Formalism.L2.Pj.Ix Dw → ℂˣ, ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ∀ b : R, (b : Om Z) = ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f → φ b = ((∏ i, s i ^ e i : ℂˣ) : ℂ) * rdU U f z.1 z.2 := by
  intro E _ _ _ H Dw l Xo c r σ U hU Z
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨C, rfl⟩ := exists_fChart h Z
  haveI := C.sm
  refine ⟨C.R, inferInstance, C.t, fun e f hf => ?_, fun φ hφ => ?_⟩
  · obtain ⟨b, hb, -⟩ := fChart_exists_val C hf
    exact hb ▸ b.2
  · haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
    let ψ : C.R →ₐ[c.F] CAt σ := { (φ : C.R →+* CAt σ) with commutes' := fun a => DFunLike.congr_fun hφ a }
    obtain ⟨z, hz⟩ := exists_frMap ψ C.y
    obtain ⟨k, x, s, hs⟩ := hU.2.2.1 z
    have key : ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e,
        toC (σ := σ) (evR Xo c f z) = ((∏ i, (show ℂˣ from s i) ^ e i : ℂˣ) : ℂ) * rdU U f k x.1 := fun e f hf => by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_frBor (S := CAt σ) hf hs
    refine ⟨⟨k, x.1⟩, by_contra fun hn => ?_, s, fun e f hf b hb => ?_⟩
    · have h1 := key 0 _ (idem_mem_secZ C.Z)
      rw [rdU_eq_zero U (idem_mem_suppOn C.Z) hn, mul_zero, fChart_evR_idem C hz] at h1
      exact one_ne_zero (α := ℂ) h1
    · obtain ⟨b', hb', h2⟩ := fChart_exists_val C hf
      obtain rfl : b = b' := Subtype.ext (hb.trans hb'.symm)
      exact (h2 _ ψ z hz).symm.trans (key e f hf)

end GlobalTheory.DegCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSu
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.HintLevel

theorem finsum_prod_fst {A T : Type} [Finite T] [Nonempty T] (f : A → ℂ) :
    ∑ᶠ x : A × T, f x.1 = (Nat.card T : ℂ) * ∑ᶠ a : A, f a := by
  by_cases hf : (Function.support f).Finite
  · have hg : (Function.support fun x : A × T => f x.1).Finite := by
      refine (hf.prod (Set.finite_univ (α := T))).subset ?_
      intro x hx
      exact ⟨hx, Set.mem_univ _⟩
    rw [finsum_curry _ hg, mul_finsum]
    refine finsum_congr fun a => ?_
    haveI := Fintype.ofFinite T
    rw [finsum_eq_sum_of_fintype]
    show ∑ _i : T, f a = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · have hg : ¬ (Function.support fun x : A × T => f x.1).Finite := by
      intro hg
      apply hf
      refine (hg.image Prod.fst).subset ?_
      intro a ha
      exact ⟨(a, Classical.arbitrary T), ha, rfl⟩
    rw [finsum_of_infinite_support hg, finsum_of_infinite_support hf, mul_zero]

theorem sum_level (H : Type) [Group H] (S L : Subgroup H) (u : H → ℂ) (hLS : L ≤ S) (hS : S ≤ rStab u)
    (hfin : L.relIndex S ≠ 0) :
    ∑ᶠ q : H ⧸ L, u q.out = ((L.relIndex S : ℕ) : ℂ) * ∑ᶠ p : H ⧸ S, u p.out := by
  have hinv : ∀ g : H, u ((QuotientGroup.mk g : H ⧸ S).out) = u g := by
    intro g
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul S g
    rw [hk]
    exact hS k.2 g
  have hfst : ∀ q : H ⧸ L, u q.out = u ((Subgroup.quotientEquivProdOfLE hLS q).1.out) := by
    intro q
    have : (Subgroup.quotientEquivProdOfLE hLS q).1 = (QuotientGroup.mk q.out : H ⧸ S) := by
      simp only [Subgroup.quotientEquivProdOfLE, Subgroup.quotientEquivProdOfLE']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this, hinv]
  haveI : Finite (S ⧸ L.subgroupOf S) := Subgroup.index_ne_zero_iff_finite.1 hfin
  rw [finsum_congr hfst, finsum_comp_equiv (Subgroup.quotientEquivProdOfLE hLS)
    (f := fun x : (H ⧸ S) × (S ⧸ L.subgroupOf S) => u x.1.out)]
  exact finsum_prod_fst (fun p : H ⧸ S => u p.out)

theorem hint_level : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u →
    L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  intro H _ K L u hLK hLu hne
  have hLS : L ≤ rStab u ⊓ K := le_inf hLu hLK
  have hmul := Subgroup.relIndex_mul_relIndex L (rStab u ⊓ K) K hLS inf_le_right
  have h1 : L.relIndex (rStab u ⊓ K) ≠ 0 := by
    intro h0; apply hne; rw [← hmul, h0, zero_mul]
  have h2 : (rStab u ⊓ K).relIndex K ≠ 0 := by
    intro h0; apply hne; rw [← hmul, h0, mul_zero]
  rw [sum_level H (rStab u ⊓ K) L u hLS inf_le_left h1, hint, ← hmul]
  push_cast
  have h1' : ((L.relIndex (rStab u ⊓ K) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1
  field_simp

end GlobalTheory.BCT.HintLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralNormalizedOpenCompactEqFiniteLevelSuStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L ≤ rStab u → L.relIndex K ≠ 0 → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ L, u q.out := by
  first | exact @GlobalTheory.BCT.HintLevel.hint_level | exact GlobalTheory.BCT.HintLevel.hint_level | (intros; apply GlobalTheory.BCT.HintLevel.hint_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.BallFam

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {y : CxPts p σ} {f g : X.functionField}

theorem ratVal_sub (hf : RegAt (under y) f) (hg : RegAt (under y) g) :
    ratVal (f - g) y = ratVal f y - ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_sub,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_eq hy, ev_eq hy, ev_eq hy, map_sub]

theorem ratVal_zero : ratVal (0 : X.functionField) y = 0 := by
  have h0 : RegAt (under y) (0 : X.functionField) := ⟨0, map_zero _⟩
  simpa using ratVal_sub h0 h0

theorem ratVal_nsmul (hf : RegAt (under y) f) (n : ℕ) : ratVal (n • f) y = n • ratVal f y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  rw [← map_nsmul, ratVal_fnOf hy, ratVal_fnOf hy, ev_eq hy, ev_eq hy, map_nsmul]

namespace Pair

variable (P : Pair p) (a b : ℤ)

theorem regAt_loc {f : X.functionField} (hf : f ∈ P.H a b) (σ : k →+* ℂ) (y : CxPts p σ) :
    RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
  hf _ _ _ (mem_ptsIn.1 (mem_pick _ y)) (mem_ptsIn.1 (mem_pick _ y))

theorem loc_sub (f g : X.functionField) (i j) : P.loc a b (f - g) i j = P.loc a b f i j - P.loc a b g i j := by
  simp only [VolBr.Pair.loc]; ring

theorem loc_nsmul (n : ℕ) (f : X.functionField) (i j) : P.loc a b (n • f) i j = n • P.loc a b f i j := by
  simp only [VolBr.Pair.loc, nsmul_eq_mul]; ring

theorem nu_zero (σ : k →+* ℂ) (y : CxPts p σ) : P.nu a b σ y 0 = 0 := by
  simp only [VolBr.Pair.nu, VolBr.Pair.loc, zero_mul, ratVal_zero, norm_zero]

theorem nu_sub {f g : X.functionField} (hf : f ∈ P.H a b) (hg : g ∈ P.H a b) (σ : k →+* ℂ) (y : CxPts p σ) :
    P.nu a b σ (y) (f - g) ≤ P.nu a b σ y f + P.nu a b σ y g := by
  simp only [VolBr.Pair.nu]
  rw [loc_sub, ratVal_sub (regAt_loc P a b hf σ y) (regAt_loc P a b hg σ y), ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le

theorem nu_nsmul {f : X.functionField} (hf : f ∈ P.H a b) (n : ℕ) (σ : k →+* ℂ) (y : CxPts p σ) :
    P.nu a b σ y (n • f) = n * P.nu a b σ y f := by
  simp only [VolBr.Pair.nu]
  rw [loc_nsmul, ratVal_nsmul (regAt_loc P a b hf σ y), nsmul_eq_mul, norm_mul, Complex.norm_natCast, mul_assoc]

end Pair

end GlobalTheory.VolBr.BallFam


open GlobalTheory.VolBr.BallFam in
theorem GlobalTheory.VolBr.Pair.isBallFam : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ a b : ℤ, IsBallFam (P.H a b) (P.Bl a b) := by
  intro k _ X _ p P a b
  exact {
    subset := fun r f hf => hf.1
    zero_mem := fun r hr => ⟨zero_mem _, fun σ y => by rw [Pair.nu_zero]; exact hr⟩
    sub_mem := fun r r' f g hf hg => ⟨sub_mem hf.1 hg.1, fun σ y =>
      (Pair.nu_sub P a b hf.1 hg.1 σ y).trans (add_le_add (hf.2 σ y) (hg.2 σ y))⟩
    nsmul_iff := fun n r f hn hf => by
      have h0 : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [VolBr.Pair.Bl, Set.mem_setOf_eq, Pair.nu_nsmul P a b hf, mul_le_mul_iff_right₀ h0,
        and_iff_right (nsmul_mem hf n), and_iff_right hf] }
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSeminormBallFamily_sectionBalls : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ a b : ℤ, IsBallFam (P.H a b) (P.Bl a b) := by
  first | exact @GlobalTheory.VolBr.Pair.isBallFam | exact GlobalTheory.VolBr.Pair.isBallFam | (intros; apply GlobalTheory.VolBr.Pair.isBallFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPlacesPrimeToHostBaseTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPlacesPrimeToHostBaseTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRow

theorem primeToHost_base : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → PrimeToHost R A.μ0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h PP hP
  rcases hP with hP | hP
  · exact GlobalTheory.LiftScalarCompare.primeToHost h.lev PP hP
  · rw [GlobalTheory.LiftLower.Q_base h.lev] at hP
    simp at hP

end GlobalTheory.LowRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPlacesPrimeToHostBaseTupleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badPlacesPrimeToHost_baseTuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → PrimeToHost R A.μ0 := by
  first | exact @GlobalTheory.LowRow.primeToHost_base | exact GlobalTheory.LowRow.primeToHost_base | (intros; apply GlobalTheory.LowRow.primeToHost_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviProjectionMaximalCompact
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviFubini

theorem levH_fst_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin a) :
    ((levH h w p).1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inl i)) (GlobalTheory.SmGL.stdSum h (Sum.inl j)) := rfl

theorem levH_snd_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin b) :
    ((levH h w p).2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inr i)) (GlobalTheory.SmGL.stdSum h (Sum.inr j)) := rfl

theorem levH_mem_KGL_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (p : GlobalTheory.LeviFubini.parB h w), (p : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) →
      (GlobalTheory.LeviFubini.levH h w p).1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ (GlobalTheory.LeviFubini.levH h w p).2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  intro E _ _ _ a b n h w p hp
  have hp' := GlobalTheory.AdelicU.mem_GLint_iff.1 hp
  have hinv1 : ((levH h w p).1)⁻¹ = (levH h w p⁻¹).1 := by rw [map_inv, Prod.fst_inv]
  have hinv2 : ((levH h w p).2)⁻¹ = (levH h w p⁻¹).2 := by rw [map_inv, Prod.snd_inv]
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · rw [levH_fst_entry]; exact hp'.1 _ _
  · rw [hinv1, levH_fst_entry]; exact hp'.2 _ _
  · rw [levH_snd_entry]; exact hp'.1 _ _
  · rw [hinv2, levH_snd_entry]; exact hp'.2 _ _

end GlobalTheory.LeviFubini
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyVertices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridSpaces

variable {D : D7}

def IsSum (A B : LSp D) (c : ℕ) (ε : D.host.E) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Prop :=
  ∃ d : HermitianOrthogonalExtensionData A.sp B.sp c ε, B.lat = d.lat A.lat 𝔟

theorem exists_sum (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) (c : ℕ) (neg : Bool)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (h0 : ∀ p, 𝔟 p ≠ 0)
    (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) {ν' q' : ℕ} (h1 : ν + c = ν')
    (h2 : q + (if neg then (c + 1) / 2 else c / 2) = q') :
    ∃ Y : LSp D, Y.IsV ν' q' ∧ IsSum X Y c (if neg then -1 else 1) 𝔟 := by
  obtain ⟨B, ⟨d⟩, hB, hs⟩ := GlobalTheory.T.hermitian_space_add_signature_exists D X.sp (ν - q) q c neg hX.sigOK hX.sig
  refine ⟨⟨B, d.lat X.lat 𝔟⟩, ⟨?_, hB, fun τ => ?_, ?_⟩, d, rfl⟩
  · have := d.rank
    rw [hX.rank] at this
    exact this.symm.trans h1
  · rw [hs τ]
    cases neg <;> simp only [Bool.false_eq_true, if_true, if_false, Prod.mk.injEq] at h2 ⊢ <;> omega
  · exact GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D X.sp B c _ d X.lat 𝔟 (by cases neg <;> simp) hX.sd h0 hd

theorem exists_line (X : LSp D) {ν q : ℕ} (hX : X.IsV ν q) (hq : q ≤ ν) :
    ∃ Y : LSp D, Y.IsV (ν + 1) q ∧ IsSum X Y 1 1 fun _ => 1 := by
  refine exists_sum X hX hq 1 false (fun _ => 1) (fun _ => one_ne_zero) (fun _ x => ?_) rfl rfl
  rw [inv_one, FractionalIdeal.mem_one_iff, FractionalIdeal.mem_one_iff]
  have key : ∀ y : D.host.E, (∃ a : 𝓞 D.host.E, algebraMap _ _ a = y) → ∃ a : 𝓞 D.host.E, algebraMap _ _ a = star y := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨_, Examples₂.star_isIntegral _ a.2⟩, rfl⟩
  exact ⟨key x, fun h => by simpa using key _ h⟩

end GlobalTheory.GridSpaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompat
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeomFrobChar


open GlobalTheory.WeilDeligne Polynomial in
theorem charpoly_geomFrob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
      (rc : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    ∀ t : ℝ, GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw t →
    ∀ g : G E Ω, IsFrob (F := E) B (normV w) g →
      (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
        Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ)))).prod := by
  intro E Ω _ _ _ _ _ l _ ι a r hr w hl B h rc hrc σ S hS t hw g hg
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ S).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hS⟩)
  have e := ParLaws.rec_eq_diag hrc (σ := ParLaws.toRep σ) hα
  let φ : Weil h := ⟨g, mem_Weil_of_isFrob h hg⟩
  have hφ : deg φ = 1 := deg_eq_one_iff.mpr hg
  have h1 := charPol_wdOf hl ι (Units.continuous_val.comp hr) φ⁻¹
  have e' : rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := e
  have h2 : ((WDRep.diag h fun i => (α i)⁻¹).tw t).ρ φ⁻¹ =
      GlobalTheory.WeilDeligne.diagEnd fun i => (α i : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ) := by
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [WDRep.tw_ρ, WDRep.diag_ρ, deg_inv, hφ, Complex.ofReal_neg, Complex.cpow_neg]
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply, mul_assoc, mul_left_comm]
  rw [hw, e', WD.lpTw_mk, WD.charPol_mk, h2, charpoly_diagEnd] at h1
  apply Polynomial.map_injective ι.toRingHom ι.injective
  rw [zpow_neg_one]
  refine (show _ = _ from h1.symm).trans ?_
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun i _ => ?_
  simp

end GlobalTheory.GeomFrobChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusHalfLeviAbsDet
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AbsHalfLevi

theorem absHalf_det_div_eq_deltaHalf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) := by
  intro E _ _ _ a b w m
  rw [GlobalTheory.SmGL.deltaHalf_two, Units.val_mul]
  have e1 : m.1.val.det = ((GeneralLinearGroup.det m.1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  have e2 : m.2.val.det = ((GeneralLinearGroup.det m.2 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    simp [GeneralLinearGroup.val_det_apply]
  rw [e1, e2]
  generalize GeneralLinearGroup.det m.1 = d1
  generalize GeneralLinearGroup.det m.2 = d2
  have n1 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d1
  have n2 := GlobalTheory.LGrp.BorelCompletion.nabs_completion w d2
  have hb : ((Fintype.card (Fin b) : ℂ) / 2) = (((b : ℝ) / 2 : ℝ) : ℂ) := by simp
  have ha : (-(Fintype.card (Fin a) : ℂ) / 2) = ((-(a : ℝ) / 2 : ℝ) : ℂ) := by simp
  rw [hb, ha, GlobalTheory.SmGL.val_absPow_ofReal, GlobalTheory.SmGL.val_absPow_ofReal, n1, n2, ← Complex.ofReal_mul]
  unfold absHalf
  congr 1
  have hd1 : ((d1 : w.adicCompletion E)) ≠ 0 := d1.ne_zero
  have hd2 : ((d2 : w.adicCompletion E)) ≠ 0 := d2.ne_zero
  have hx : ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero _ hd1) (pow_ne_zero _ hd2)
  have hv1 : Valued.v (d1 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd1
  have hv2 : Valued.v (d2 : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr hd2
  have hord : ordL ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) =
      -((b : ℤ) * WithZero.log (Valued.v (d1 : w.adicCompletion E)) - (a : ℤ) * WithZero.log (Valued.v (d2 : w.adicCompletion E))) := by
    have hv : Valued.v ((d1 : w.adicCompletion E) ^ b / (d2 : w.adicCompletion E) ^ a) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    unfold ordL
    rw [dite_eq_right hv, WithZero.toAdd_unzero_eq_log, map_div₀, map_pow, map_pow,
      WithZero.log_div (pow_ne_zero _ hv1) (pow_ne_zero _ hv2), WithZero.log_pow, WithZero.log_pow]
    simp
  rw [hord, neg_neg]
  have hq : (0 : ℝ) < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV; exact (Ideal.absNorm_eq_zero_iff).not.mpr w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  generalize WithZero.log (Valued.v (d1 : w.adicCompletion E)) = l1
  generalize WithZero.log (Valued.v (d2 : w.adicCompletion E)) = l2
  generalize (qV E w : ℝ) = q at hq ⊢
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, ← Real.rpow_add hq]
  congr 1
  push_cast
  ring

end GlobalTheory.AbsHalfLevi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDualStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDual
open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.ConjDualTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ}

theorem opTriv_thetaOp (o : Op E m) : opTriv (thetaOp o) = opTriv o := by
  cases o <;> rfl

theorem act_mulChi_oneFn (ψ : HChar E) (o : Op E m) :
    act o (mulChi m ψ (oneFn E m)) = (((opMul ψ o : ℂˣ) : ℂ) * opTriv o + opAdd ψ o) • mulChi m ψ (oneFn E m) := by
  rw [act_mulChi, act_oneFn, smul_smul, ← add_smul, map_smul]

theorem pull_oneFn : GlobalTheory.ThetaPull.pull E m (oneFn E m) = oneFn E m := Subtype.ext rfl

theorem scalar_thetaOp (χ : HChar E) (o : Op E m) :
    ((opMul χ (thetaOp o) : ℂˣ) : ℂ) * opTriv o + opAdd χ (thetaOp o) =
      ((opMul (GlobalTheory.ThetaPull.thetaChar χ) o : ℂˣ) : ℂ) * opTriv o + opAdd (GlobalTheory.ThetaPull.thetaChar χ) o := by
  have h1 := GlobalTheory.ThetaPull.act_pull o (mulChi m χ (oneFn E m))
  simp only [act_mulChi_oneFn, map_smul, GlobalTheory.ThetaPull.pull_mulChi, pull_oneFn, opTriv_thetaOp] at h1
  have hF : mulChi m (GlobalTheory.ThetaPull.thetaChar χ) (oneFn E m) ≠ 0 :=
    (LinearEquiv.map_ne_zero_iff _).2 oneFn_ne_zero
  exact (smul_left_injective ℂ hF h1).symm

theorem isConjDualBy_twist_thetaChar : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ} {π : GlobalTheory.CuspRep.CuspSub E m}, π.IsCsd → ∀ χ : Formalism.L2.Host.HChar E, GlobalTheory.GalOfCusp.IsConjDualBy (π.twist χ) (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹) := by
  intro E _ _ _ m π hπ χ
  refine GlobalTheory.GalOfCusp.isConjDualBy_twist hπ fun o => ?_
  have e : χ * (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹)⁻¹ = GlobalTheory.ThetaPull.thetaChar χ := by
    rw [mul_inv_rev, inv_inv, mul_comm (GlobalTheory.ThetaPull.thetaChar χ), ← mul_assoc, mul_inv_cancel, one_mul]
  rw [e]
  have h := scalar_thetaOp χ o
  cases o with
  | fin k => exact ⟨Units.ext (by simpa [opTriv, opAdd, thetaOp] using h), rfl⟩
  | cpt k => exact ⟨Units.ext (by simpa [opTriv, opAdd, thetaOp] using h), rfl⟩
  | lie X => exact ⟨rfl, by simpa [opTriv, opMul, thetaOp] using h⟩

end GlobalTheory.ConjDualTwist

end
end

open NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConjugateDualTwistBy_twist_of_conjSelfDual : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {m : ℕ} {π : GlobalTheory.CuspRep.CuspSub E m}, π.IsCsd → ∀ χ : Formalism.L2.Host.HChar E, GlobalTheory.GalOfCusp.IsConjDualBy (π.twist χ) (χ * (GlobalTheory.ThetaPull.thetaChar χ)⁻¹) := by
  first | exact @GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar | exact GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar | (intros; apply GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefNumericsOfRiemannRoch
set_option autoImplicit false

namespace GlobalTheory.Published

theorem nefNumerics_of_product_of_riemannRoch
    (h₁ : NefProductNonneg) (h₂ : NefRiemannRoch) : NefNumerics :=
  ⟨h₁, h₂.nefBigIff, h₂⟩

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalMultipleAddQWeil
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem isLogCanonicalMultiple_add_qWeil : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Δ : X → ℚ) (m m' : ℕ) (G D₀ : CartierDiv X), 0 < m → 0 < m' → IsLogCanonicalMultiple p n Δ m G → IsLogCanonicalMultiple p n (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) := by
  intro X _ _ p n Δ m m' G D₀ hm hm' hG
  obtain ⟨η, hη, hG⟩ := hG
  refine ⟨η, hη, fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨a, ha⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((ha.nsmul m').add (hd.nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow] at h3
  have h4 := hG z a ha z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h2 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  rw [Pi.add_apply, qWeil, hd', h3]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory
end
