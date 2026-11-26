module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorISignatureConjApplyOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCartanInvOneSplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulMatrixMulVecCompletedSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormDegreeLeFieldDegreeAlgebraicPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionModuleStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrameLaws
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
namespace GlobalTheory.EtaConjExist

section General

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr hiding Ideles localIdele diagUnits ordF HChar unif unif_spec atFin

variable {L : Type} [Field L] [NumberField L]

theorem fin_supp {M : Type} [CommGroup M] (c : HeightOneSpectrum (𝓞 L) → M) {n : HeightOneSpectrum (𝓞 L) → ℤ}
    (h : {v | n v ≠ 0}.Finite) : (Function.mulSupport fun v => c v ^ n v).Finite :=
  h.subset fun v hv h0 => hv (by simp only [h0, zpow_zero])

noncomputable def idealChar (c : HeightOneSpectrum (𝓞 L) → ℂˣ) : Ideles L →* ℂˣ :=
  MonoidHom.mk' (fun a => ∏ᶠ v, c v ^ GlobalTheory.Idele.ord_vw (GlobalTheory.HeckeProduct.finPart L a) v) fun a b => by
    rw [← finprod_mul_distrib (fin_supp c (Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero _)))
      (fin_supp c (Filter.eventually_cofinite.1 (GlobalTheory.Idele.ord_vw_eventually_zero _)))]
    refine finprod_congr fun v => ?_
    rw [map_mul, GlobalTheory.Idele.ord_vw_mul, zpow_add]

theorem idealChar_apply (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (a : Ideles L) :
    idealChar c a = ∏ᶠ v, c v ^ (-WithZero.log (Valued.v ((a : AdeleRing (𝓞 L) L).2 v))) := rfl

theorem idealChar_unit (c : HeightOneSpectrum (𝓞 L) → ℂˣ) {a : Ideles L} (ha : a ∈ unitIdl L) : idealChar c a = 1 := by
  rw [idealChar_apply]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [ha v, WithZero.log_one, neg_zero, zpow_zero]

theorem idealChar_local (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    idealChar c (localIdele L v x) = c v ^ (-WithZero.log (Valued.v (x : v.adicCompletion L))) := by
  rw [idealChar_apply, finprod_eq_single _ v, GlobalTheory.HeckeProduct.localIdele_snd_self]
  intro w hw
  rw [GlobalTheory.HeckeProduct.localIdele_snd_ne L v w hw, map_one, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_classChar (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (h : ∀ k : Lˣ, ∏ᶠ v, c v ^ ordF v k = 1) :
    ∃ ξ : HChar L, ξ.IsUnitary ∧ (∀ v, ξ.UnrAt v) ∧ ∀ v, ξ.val v = c v := by
  have hd : ∀ k : Lˣ, idealChar c (diagUnits L k) = 1 := fun k => by
    rw [idealChar_apply, ← h k]
    refine finprod_congr fun v => ?_
    have hk : Valued.v ((diagUnits L k : AdeleRing (𝓞 L) L).2 v) = v.valuation L (k : L) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)
    rw [hk, ordF]
  have hc : Continuous (idealChar c) := by
    refine continuous_of_continuousAt_one _ ?_
    refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.mem_nhds (unitIdl L).one_mem] with a ha
    exact (idealChar_unit c ha).symm
  refine ⟨⟨idealChar c, hc, hd⟩, fun x => ?_, fun v x hx => ?_, fun v => ?_⟩
  · have := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup L
    obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((unitIdl L ⊔ (diagUnits L).range).pow_index_mem x)
    have e1 := congrArg (fun z => ((idealChar c z : ℂˣ) : ℂ)) e
    simp only [map_mul, map_pow, idealChar_unit c hu, hd, one_mul, Units.val_one, Units.val_pow_eq_pow_val] at e1
    exact Complex.norm_eq_one_of_pow_eq_one e1.symm this.index_ne_zero
  · refine (idealChar_local c v x).trans ?_
    rw [show Valued.v (x : v.adicCompletion L) = 1 from hx, WithZero.log_one, neg_zero, zpow_zero]
  · refine (idealChar_local c v _).trans ?_
    rw [show Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) = _ from unif_spec v,
      WithZero.log_exp, neg_neg, zpow_one]

theorem finprod_sqrt [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Lˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 L), ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k) *
      ∏ i, ‖φ i (k : L)‖ = 1 := by
  have h1 := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h1
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) (k : L) ^ (InfinitePlace.mk (φ i)).mult = ‖φ i (k : L)‖ * ‖φ i (k : L)‖ := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq, sq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 L), FinitePlace.equivHeightOneSpectrum.symm v (k : L) =
      ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k *
        ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k := fun v => by
    have h0 : v.valuation L (k : L) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
    rw [← mul_zpow, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), inv_zpow',
      FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def,
      WithZeroMulInt.toNNReal_neg_apply _ h0, ordF, neg_neg]
    push_cast
    congr 1
  have h4 : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) =>
      ((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) ^ ordF v k).Finite :=
    (GlobalTheory.HeckeProduct.finite_ordF k).subset fun v hv h0 => hv (by simp only [h0, zpow_zero])
  simp only [h2, h3] at h1
  rw [finprod_mul_distrib h4 h4, Finset.prod_mul_distrib] at h1
  refine (mul_self_eq_one_iff.1 (by linear_combination h1)).resolve_right fun h => ?_
  have : (0 : ℝ) ≤ -1 := h ▸ mul_nonneg (finprod_nonneg fun v => by positivity) (by positivity)
  linarith

theorem finprod_alg [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (hu : ∀ v, χ.UnrAt v)
    (hi : χ.HasInf φ fun _ => 1) (w : HeightOneSpectrum (𝓞 L) → ℂˣ)
    (hw : ∀ v, (w v : ℂ) = χ.val v * (((Real.sqrt (Ideal.absNorm v.asIdeal : ℕ))⁻¹ : ℝ) : ℂ)) (k : Lˣ) :
    ((∏ᶠ v, w v ^ ordF v k : ℂˣ) : ℂ) * ∏ i, φ i (k : L) = 1 := by
  have e5 := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at e5
  have e6 := finprod_sqrt φ hφ k
  have hs : ∀ {M : Type} [CommGroupWithZero M] (f : HeightOneSpectrum (𝓞 L) → M), ∏ᶠ v, f v ^ ordF v k =
      ∏ v ∈ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset, f v ^ ordF v k := fun f =>
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      exact fun h0 => hv (by simp only [h0, zpow_zero])
  have hs' : ∀ (f : HeightOneSpectrum (𝓞 L) → ℂˣ), ((∏ᶠ v, f v ^ ordF v k : ℂˣ) : ℂ) =
      ∏ v ∈ (GlobalTheory.HeckeProduct.finite_ordF k).toFinset, (f v : ℂ) ^ ordF v k := fun f => by
    rw [finprod_eq_prod_of_mulSupport_subset (s := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset) _ fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      exact fun h0 => hv (by simp only [h0, zpow_zero])]
    simp
  have e7 := congrArg Units.val e5
  have e8 := congrArg Complex.ofReal e6
  rw [Units.val_mul, hs', hi k, Units.val_one] at e7
  rw [hs] at e8
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_zpow, Complex.ofReal_one] at e8
  simp only [zpow_one, Finset.prod_div_distrib] at e7
  have h0 : ∏ i, ((‖φ i (k : L)‖ : ℝ) : ℂ) ≠ 0 := right_ne_zero_of_mul_eq_one e8
  rw [hs']
  simp only [hw, mul_zpow, Finset.prod_mul_distrib]
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq h0] at e7
  rw [mul_right_comm, mul_comm _ (∏ i, φ i (k : L)), e7, mul_comm, e8]

theorem finprod_quot {M : Type} [Field M] (e σ : M →+* ℂ) (y : HeightOneSpectrum (𝓞 L) → Mˣ) (k : Lˣ) (n : M)
    (h : ((∏ᶠ v, Units.map e.toMonoidHom (y v) ^ ordF v k : ℂˣ) : ℂ) * e n = 1) (hn : σ n = e n) :
    ∏ᶠ v, (Units.map σ.toMonoidHom (y v) / Units.map e.toMonoidHom (y v)) ^ ordF v k = 1 := by
  have hf := GlobalTheory.HeckeProduct.finite_ordF k
  have hm : ∀ f : M →+* ℂ, ∏ᶠ v, Units.map f.toMonoidHom (y v) ^ ordF v k =
      Units.map f.toMonoidHom (∏ᶠ v, y v ^ ordF v k) := fun f => by
    rw [MonoidHom.map_finprod _ (fin_supp y hf)]
    simp only [map_zpow]
  simp only [div_zpow]
  rw [finprod_div_distrib (fin_supp _ hf) (fin_supp _ hf), hm, hm, div_eq_one]
  rw [hm] at h
  have h1 : ((∏ᶠ v, y v ^ ordF v k : Mˣ) : M) * n = 1 := e.injective (by rw [map_mul, map_one]; exact h)
  have h2 := congrArg σ h1
  rw [map_mul, map_one, hn, ← h] at h2
  exact Units.ext (mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h) h2)

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem unram_of_chrEq {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ)
    (hu : ∀ P, χ.UnrAt P) : UnramEverywhere D c := by
  intro x hx h4 h5
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  apply Circle.ext
  rw [GlobalTheory.Mem.EtaTilde.val_finite D ι h1 h2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc hu x hx, Circle.coe_one,
    Units.val_eq_one]
  refine finprod_eq_one_of_forall_eq_one fun P => ?_
  have e := GlobalTheory.Mem.EtaTilde.val_mul_inv (RingHom.id _) P (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := e
  have e1 : Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    refine le_antisymm ((h2 _).1 h4 P) ?_
    rw [← e']
    exact mul_le_of_le_one_right' ((h2 _).1 h5 P)
  rw [e1, WithZero.log_one, neg_zero, zpow_zero]

theorem exists_norm (D : D7) (k : D.host.E) :
    ∃ n ∈ D.host.K, D.what₂.embLL (D.embE n) = ∏ g, Formalism.L2.Host.embPsi D.host g k := by
  have hE := D.host.hostE_isGalois
  have h := Algebra.norm_eq_prod_automorphisms D.host.K k
  refine ⟨_, (Algebra.norm D.host.K k).2, (DFunLike.congr_fun D.embE_φ₀ _).trans ?_⟩
  change D.host.φ₀ (algebraMap D.host.K D.host.E _) = _
  rw [h, map_prod]
  exact (Fintype.prod_bijective _ (GlobalTheory.InducedType.galK_bijective D.host) _ _ fun _ => rfl).symm

theorem exists_conj {D : D7} (η : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hc : ChrEq η χ)
    (hχ : Formalism.L2.Host.IsEtaT D.host χ)
    (hy : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ y : D.what₂.LL,
      D.what₂.embLL y = χ.val P * (((Real.sqrt (Ideal.absNorm P.asIdeal : ℕ))⁻¹ : ℝ) : ℂ))
    (σ : D.what₂.LL →+* ℂ) (hσ : OverK σ) : ∃ η', IsEtaConj σ η η' := by
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨_, -, hd, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  choose y hy using hy
  have hy0 : ∀ P, D.what₂.embLL (y P) ≠ 0 := fun P => by
    have : (0 : ℝ) < (Ideal.absNorm P.asIdeal : ℕ) :=
      Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
    rw [hy]
    exact mul_ne_zero (Units.ne_zero _) (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 this).ne'))
  let u : HeightOneSpectrum (𝓞 D.host.E) → D.what₂.LLˣ := fun P => Units.mk0 (y P) ((map_ne_zero _).1 (hy0 P))
  obtain ⟨ξ, x1, x2, x3⟩ := exists_classChar
    (fun P => Units.map σ.toMonoidHom (u P) / Units.map D.what₂.embLL.toMonoidHom (u P)) fun k => by
      obtain ⟨n, hn, hn'⟩ := exists_norm D k
      refine finprod_quot _ _ u k (D.embE n) ?_ (hσ n hn)
      rw [hn']
      exact finprod_alg _ hd.bij χ hχ.unr hχ.inf _ hy k
  obtain ⟨c, hc'⟩ := GlobalTheory.CharTransport.exists_chrEq D (χ * ξ) fun x => by
    change ‖((χ.1 x * ξ.1 x : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, hχ.unitary x, x1 x, one_mul]
  have hcard (P : HeightOneSpectrum (𝓞 D.host.E)) : Nat.card (kP P) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨c, hc'.1, unram_of_chrEq hc' fun P x hx => ?_, fun P e he x hx => ⟨y P, ?_, ?_⟩⟩
  · change χ.loc P x * ξ.loc P x = 1
    rw [hχ.unr P x hx, x2 P x hx, one_mul]
  · rw [hc.2 P e he _ x hx]
    rw [hcard]
    exact hy P
  · rw [hcard]
    have h1 : ((c x : Circle) : ℂ) = ((χ.val P * ξ.val P : ℂˣ) : ℂ) := hc'.2 P e he _ x hx
    rw [h1, x3, Units.val_mul, mul_right_comm, Units.val_div_eq_div_val]
    have h2 := hy P
    refine Eq.trans ?_ (congrArg (· * (σ (y P) / D.what₂.embLL (y P))) h2)
    exact (mul_div_cancel₀ _ (hy0 P)).symm

end GlobalTheory.EtaConjExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZero
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HatInt

noncomputable section

theorem omegaK_congr {D : D7} {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP))
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  refine if_congr (forall₂_congr fun PP hP => ?_) rfl rfl
  rw [h PP hP]

theorem omegaQ_congr {D : D7} {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP))
    (h : ∀ PP ∈ Q, y PP = y' PP) : omegaQ Q r ξ k y = omegaQ Q r ξ k y' := by
  unfold omegaQ
  refine dite_congr (propext (forall₂_congr fun PP hP => by rw [h PP hP])) (fun h1 => ?_) (fun _ => rfl)
  refine Finset.prod_congr rfl fun PP _ => ?_
  congr 3
  apply Units.ext
  simp only [IsUnit.unit_spec]
  rw [h PP.1 PP.2]

theorem matrix_map_ringHom_add_smul_sandwich {K S : Type} [CommRing K] [CommRing S] (f : K →+* S) {m n : Type} [Fintype m] [Fintype n]
    (B : Matrix m m S) (C : Matrix n n S) (P : Matrix m m K) (Q : Matrix n n K) (X Y : Matrix m n K) (d : K) :
    B * (P * (X + d • Y) * Q).map f * C = B * (P * X * Q).map f * C + f d • (B * (P * Y * Q).map f * C) := by
  have h2 : ∀ (P Q : Matrix m n K), (P + d • Q).map f = P.map f + f d • Q.map f := by
    intro P Q; ext b a; simp
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h2]

theorem uMat_add_smul {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X Y : Fin S.rank → Fin T.rank → D.host.E) (c : D.host.E) :
    FWT.uMat S T βS βT e (fun b => X b + c • Y b) =
      fun b a => FWT.uMat S T βS βT e X b a + eToEAf D (D.sp.cm.sig c) * FWT.uMat S T βS βT e Y b a := by
  have h1 : (Matrix.of fun b a => D.sp.cm.sig ((X b + c • Y b) a)) =
      (Matrix.of fun b a => D.sp.cm.sig (X b a)) + D.sp.cm.sig c • (Matrix.of fun b a => D.sp.cm.sig (Y b a)) := by
    ext b a; simp
  funext b a
  have h2 := congrFun (congrFun (matrix_map_ringHom_add_smul_sandwich (eToEAf D) (βS⁻¹).val βT.val S.gram⁻¹ T.gram
    (Matrix.of fun b a => D.sp.cm.sig (X b a)) (Matrix.of fun b a => D.sp.cm.sig (Y b a)) (D.sp.cm.sig c)) b) a
  rw [← h1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h2
  have h3 := congrArg (fun u => toEAf D e * u) h2
  simp only [mul_add] at h3
  rw [mul_left_comm] at h3
  exact h3

theorem subring_reduction_add_mul_killed {S k : Type} [CommRing S] [CommRing k] (O : Subring S) (f : O →+* k) (x y : S) (hx : x ∈ O) (hy : y ∈ O)
    (c : O) (hc : f c = 0) :
    (if h : x + (c : S) * y ∈ O then f ⟨x + (c : S) * y, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hmem : x + (c : S) * y ∈ O := add_mem hx (mul_mem c.2 hy)
  rw [dite_eq_left hmem, dite_eq_left hx]
  have : (⟨_, hmem⟩ : O) = ⟨x, hx⟩ + c * ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _), map_mul, hc, zero_mul, add_zero]

theorem redM_add_smul {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N N' : Matrix (Fin b) (Fin a) (EAf D))
    (hN : Datum.IsIntM N) (hN' : Datum.IsIntM N') (s : 𝓞 D.host.E) (hs : s ∈ PP.asIdeal) :
    Datum.redM PP (fun i j => N i j + eToEAf D (s : D.host.E) * N' i j) = Datum.redM PP N := by
  funext i j
  have h0 : ((Formalism.L2.DIV.oToS D.host.F D.host.E s : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      eToEAf D (s : D.host.E) := by
    unfold Formalism.L2.DIV.oToS eToEAf
    rw [RingHom.codRestrict_apply]
    rfl
  rw [← h0]
  unfold Datum.redM
  exact subring_reduction_add_mul_killed _ (Formalism.L2.DIV.resS D.host.F PP) _ _ (hN i j) (hN' i j) _
    (by rw [Formalism.L2.DIV.resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hs])

theorem sig_bar {D : D7} (H : Geo.Tor.Host D.host.E) (s : 𝓞 D.host.E) :
    D.sp.cm.sig ((H.bar s : 𝓞 D.host.E) : D.host.E) = (s : D.host.E) := by
  rw [H.bar_eq]
  exact IsCMField.complexConj_apply_apply D.host.E (s : D.host.E)

theorem dvd_of_invariant {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    (l : Geo.Tor.Level H) {n : ℕ} (φ : (Fin n → LevQc Dw l) → ℂ) (q : Fin n → LevQ Dw l) (hq : hatC l φ q ≠ 0)
    (z : Fin n → Dw.La) (hφ : ∀ x, φ (x + fun b => Submodule.Quotient.mk (z b)) = φ x) :
    (l.M : ℤ) ∣ Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hp := Complex.isPrimitiveRoot_exp l.M hM
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (l.M : ℂ)) with hζ
  have h0 : ζ ≠ 0 := hp.ne_zero hM
  have hrep : ∀ y : LevQc Dw l, Submodule.Quotient.mk (qRep y) = y := fun y =>
    Classical.choose_spec (Submodule.Quotient.mk_surjective _ y)
  have key : hatC l φ q = ζ ^ Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) * hatC l φ q := by
    unfold hatC
    rw [mul_finsum, ← finsum_comp_equiv (Equiv.addRight (fun b => (Submodule.Quotient.mk (z b) : LevQc Dw l)))]
    refine finsum_congr fun x => ?_
    simp only [Equiv.coe_addRight]
    rw [hφ, mul_left_comm, ← zpow_add₀ h0]
    congr 1
    have hd := LevelPairing.pairL_congr (l := l)
      (fun b => qRep ((x + fun b => (Submodule.Quotient.mk (z b) : LevQc Dw l)) b)) (fun b => z b + qRep (x b))
      (fun b => levRep (q b)) (fun b => levRep (q b))
      (fun b => (Submodule.Quotient.eq _).1 (by
        rw [hrep, Submodule.Quotient.mk_add, hrep, add_comm]; rfl)) (fun b => by simp)
    have ha : Formalism.L2.Pj.pairL (l := l) (fun b => z b + qRep (x b)) (fun b => levRep (q b)) =
        Formalism.L2.Pj.pairL (l := l) z (fun b => levRep (q b)) +
          Formalism.L2.Pj.pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b)) := by
      simp [Formalism.L2.Pj.pairL, Finset.sum_add_distrib]
    rw [← ha]
    have := (hp.zpow_eq_one_iff_dvd _).2 hd
    rwa [zpow_sub₀ h0, div_eq_one_iff_eq (zpow_ne_zero _ h0)] at this
  rw [← hp.zpow_eq_one_iff_dvd]
  exact (mul_left_eq_self₀.1 key.symm).resolve_right hq

theorem smul_eq_of_hatC_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i H Dw ι t l₂ φ hφ q hq s hs b
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by have := l₂.three_le; omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    have h1 := dvd_of_invariant l₂ φ q hq (fun b' => H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b') (by
      intro x
      obtain ⟨x, rfl⟩ : ∃ x' : Fin (Vc D i).rank → Dw.La, x = fun b => Submodule.Quotient.mk (x' b) :=
        ⟨fun b => qRep (x b), funext fun b => (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x b))).symm⟩
      have e1 := (he (fun b' => x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')).2
      have e2 := (he x).2
      simp only [RingHom.id_apply] at e1 e2
      have e3 : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t →
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b' => ι (x b')) := by
        intro PP hP
        have e4 : (fun b' => ι (x b' + H.bar s • (Pi.single b w : Fin (Vc D i).rank → Dw.La) b')) =
            fun b' => ι (x b') + ((H.bar s : 𝓞 D.host.E) : D.host.E) •
              ι ((Pi.single b w : Fin (Vc D i).rank → Dw.La) b') := by
          funext b'
          rw [map_add (f := _), map_smul]
          rfl
        rw [e4, uMat_add_smul, sig_bar]
        exact redM_add_smul PP _ _ (he x).1 (he _).1 s (hs PP hP)
      rw [omegaK_congr _ _ _ (fun PP hP => e3 PP (Or.inl hP)),
        omegaQ_congr _ _ _ _ _ _ (fun PP hP => e3 PP (Or.inr hP)), ← e2] at e1
      exact e1)
    unfold Formalism.L2.Pj.pairL at h1
    rw [Finset.sum_eq_single b] at h1
    · simpa [Dw.adj, LevelPairing.bar_bar] using h1
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have h2 := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt, zero_add, add_zero] at h2
    have h3 := hdvd y
    have : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by linarith
    rw [this]; exact h3.neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩

end

end GlobalTheory.HatInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointSmulIntegralOfFourierCoeffNeZeroStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HatInt in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoint_smul_integral_of_fourierCoeff_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (t : T0) (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), PhiIs R i (RingHom.id ℂ) t ι (Mfr l₂ • ⊤) φ → ∀ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q ≠ 0 → ∀ s : 𝓞 D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → s ∈ PP.asIdeal) → ∀ b, ∃ z : Dw.La, s • (cSep l₂ • levRep (q b)) = l₂.M • z := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i H Dw ι t l₂ φ hφ q hq s hs b
  obtain ⟨e, -, he⟩ := hφ
  have hM : l₂.M ≠ 0 := by
    have := l₂.three_le
    omega
  have hdvd : ∀ w : Dw.La, (l₂.M : ℤ) ∣ Dw.EF w (s • (cSep l₂ • levRep (q b))) := by
    intro w
    let single : Fin (Vc D i).rank → Dw.La := Pi.single b w
    let shift : Fin (Vc D i).rank → Dw.La := fun j => H.bar s • single j
    have hinv : ∀ x, φ (x + fun j => Submodule.Quotient.mk (shift j)) = φ x := by
      intro x
      obtain ⟨y, rfl⟩ : ∃ y : Fin (Vc D i).rank → Dw.La,
          x = fun j => Submodule.Quotient.mk (y j) :=
        ⟨fun j => qRep (x j), funext fun j =>
          (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (x j))).symm⟩
      have hshift := (he (fun j => y j + shift j)).2
      have horig := (he y).2
      simp only [RingHom.id_apply] at hshift horig
      have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t →
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun j => ι (y j + shift j)) =
          Datum.redM PP (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e
            fun j => ι (y j)) := by
        intro PP hP
        have hmap : (fun j => ι (y j + shift j)) =
            fun j => ι (y j) + ((H.bar s : 𝓞 D.host.E) : D.host.E) • ι (single j) := by
          funext j
          change ι (y j + H.bar s • single j) = _
          rw [map_add (f := _), map_smul]
          rfl
        rw [hmap, uMat_add_smul, sig_bar]
        exact redM_add_smul PP _ _ (he y).1 (he _).1 s (hs PP hP)
      rw [omegaK_congr _ _ _ (fun PP hP => hred PP (Or.inl hP)),
        omegaQ_congr _ _ _ _ _ _ (fun PP hP => hred PP (Or.inr hP)), ← horig] at hshift
      change φ (fun j => Submodule.Quotient.mk (y j) + Submodule.Quotient.mk (shift j)) = _
      simpa only [Submodule.Quotient.mk_add] using hshift
    have hpair := dvd_of_invariant l₂ φ q hq shift hinv
    unfold Formalism.L2.Pj.pairL at hpair
    rw [Finset.sum_eq_single b] at hpair
    · simpa [shift, single, Dw.adj, LevelPairing.bar_bar] using hpair
    · intro j _ hj
      simp [shift, single, Pi.single_eq_of_ne hj]
    · simp
  obtain ⟨z, hz⟩ := LevelPairing.exists_eq_smul_of_dvd (s • (cSep l₂ • levRep (q b))) l₂.M hM (fun y => by
    have halt := Dw.alt (y + s • (cSep l₂ • levRep (q b)))
    simp only [map_add (f := _), LinearMap.add_apply, Dw.alt, zero_add, add_zero] at halt
    have hskew : Dw.EF (s • (cSep l₂ • levRep (q b))) y = -Dw.EF y (s • (cSep l₂ • levRep (q b))) := by
      linarith
    rw [hskew]
    exact (hdvd y).neg_right)
  exact ⟨z, by rw [hz, natCast_zsmul]⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
set_option autoImplicit false

namespace GlobalTheory.ChowExists

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {N : ℕ}

theorem isHomogeneous_of_component {I : Ideal (MvPolynomial (Fin N) K)}
    (h : ∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) :
    I.IsHomogeneous (homogeneousSubmodule (Fin N) K) := fun d g hg => by
  have e : ((DirectSum.decompose (homogeneousSubmodule (Fin N) K) g d : _) : MvPolynomial (Fin N) K) =
      homogeneousComponent d g := MvPolynomial.decomposition.decompose'_apply g d
  rw [e]
  exact h g hg d

theorem aeval_eq_zero_of_block {P : Ideal (MvPolynomial (Fin N) K)} {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f)
    (t : Fin (D + 1) × Fin N → AlgebraicClosure K) (i : Fin (D + 1)) (ht : ∀ j, t (i, j) = 0) :
    aeval t f = 0 := _root_.GlobalTheory.ConeDeg.aeval_eq_zero_of_block (P := P) (D := D) (δ := δ) (f := f) h t i ht

theorem not_lt_of_isChowFormInt {P : Ideal (MvPolynomial (Fin N) K)} {D D' δ δ' : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} {f' : MvPolynomial (Fin (D' + 1) × Fin N) K}
    (h : IsChowFormInt P D δ f) (h' : IsChowFormInt P D' δ' f') : ¬ D < D' := fun hlt => by
  refine h.ne_zero (map_injective _ (algebraMap K (AlgebraicClosure K)).injective ?_)
  refine MvPolynomial.funext fun u => ?_
  rw [map_zero, map_zero, eval_map, ← aeval_def]
  obtain ⟨y, hy, hP, hu⟩ := (h'.zero_iff _).1 (aeval_eq_zero_of_block h'
    (fun v => if hv : (v.1 : ℕ) < D + 1 then u (⟨v.1, hv⟩, v.2) else 0) (Fin.last _)
    (fun j => dif_neg (by simp; omega)))
  refine (h.zero_iff u).2 ⟨y, hy, hP, fun i => ?_⟩
  have := hu ⟨i, by omega⟩
  simpa only [dif_pos i.2] using this

theorem exists_X_notMem {P : Ideal (MvPolynomial (Fin N) K)} {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) : ∃ j, X j ∉ P := by
  obtain ⟨y, hy, hyI⟩ := h.exists_point
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  exact ⟨j, fun hX => hj (by simpa using hyI _ hX)⟩

theorem ringKrullDim_of_isChowFormInt {P : Ideal (MvPolynomial (Fin N) K)} [hp : P.IsPrime]
    (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) :
    ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ) := by
  obtain ⟨j, hj⟩ := exists_X_notMem h
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ (isHomogeneous_of_component hP) hj
  obtain ⟨δ', f', h'⟩ := GlobalTheory.ChowHt.exists_isChowFormInt_of_ringKrullDim_eq K N e P hp hP he
  obtain rfl : e = D := le_antisymm (not_lt.1 (not_lt_of_isChowFormInt h h'))
    (not_lt.1 (not_lt_of_isChowFormInt h' h))
  exact he

theorem exists_eq_coneIdeal {P : Ideal (MvPolynomial (Fin N) K)} [hp : P.IsPrime]
    (hP : ∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) {δ : ℕ}
    {f : MvPolynomial (Fin (0 + 1) × Fin N) K} (h : IsChowFormInt P 0 δ f) :
    ∃ (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 ∧ P = coneIdeal K y := _root_.GlobalTheory.ConeDeg.exists_eq_coneIdeal (P := P) (δ := δ) (f := f) hP h

theorem coeff_sub_comp {H : Polynomial ℚ} {D : ℕ} (h : H.natDegree ≤ D + 1) :
    (H - H.comp (Polynomial.X - Polynomial.C ((1 : ℕ) : ℚ))).coeff D = (D + 1) * H.coeff (D + 1) := by
  have e : H.comp (Polynomial.X - Polynomial.C ((1 : ℕ) : ℚ)) = Polynomial.taylor (-1) H := by
    rw [Polynomial.taylor_apply]; simp [sub_eq_add_neg]
  have h1 : (Polynomial.hasseDeriv D H).natDegree ≤ 1 :=
    (Polynomial.natDegree_hasseDeriv_le _ _).trans (by omega)
  rw [e, Polynomial.coeff_sub, Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]
  simp [Polynomial.hasseDeriv_coeff, add_comm 1 D]

theorem degree_eq_coeff (D : ℕ) : ∀ (K : Type) [Field K] [CharZero K] (P : Ideal (MvPolynomial (Fin N) K))
    [P.IsPrime], (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → ∀ (δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) K), IsChowFormInt P D δ f →
    (δ : ℚ) = (D.factorial : ℚ) * (idealHilbertPoly P).coeff D := by
  induction D with
  | zero =>
    intro K _ _ P _ hP δ f h
    obtain ⟨y, j, hy, rfl⟩ := exists_eq_coneIdeal hP h
    rw [GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin K N y j hy, le_antisymm (GlobalTheory.CompHt.PointUp.le_finrank_of_isChowFormInt K N δ y j f hy h) (GlobalTheory.CompHt.PointLow.finrank_le_of_isChowFormInt K N δ y j f hy h)]
    simp
  | succ D ih =>
    intro K _ _ P hp hP δ f h
    let L := FractionRing (MvPolynomial (Fin N) K)
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    obtain ⟨hE, hEH⟩ := GlobalTheory.HilbBaseChange.idealHilbertPoly_map K L N P hP
    obtain ⟨hEp, hl⟩ := GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem K L N P hp
    obtain ⟨Q, hQ, hIQ, hsat⟩ := GlobalTheory.Chow.exists_prime_saturation_generic_section K L N P hp fun u => by
      obtain ⟨y, hy, h1, h2⟩ := (h.zero_iff _).1 (aeval_eq_zero_of_block h
        (fun v => if v.1 = 0 then u v.2 else 0) (Fin.last _) (fun j => if_neg (by simp)))
      exact ⟨y, hy, h1, by simpa using h2 0⟩
    obtain ⟨f', hf'⟩ := GlobalTheory.ChowSpec.exists_isChowFormInt_generic_section K L N P D δ f hP h
    have hlin : (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
        MvPolynomial (Fin N) L).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X L j).C_mul _
    have hI := isHomogeneous_sup_span_singleton (isHomogeneous_of_component hE) hlin
    obtain ⟨hQh, hQH⟩ := GlobalTheory.prime_saturation_homogeneous_and_hilbertPoly_eq L N _ Q (fun g hg n => homogeneousComponent_mem_of_mem hI hg n) hQ hIQ hsat
    have hf'' : IsChowFormInt Q D δ f' := ⟨hf'.homog, hf'.irred, fun u => (hf'.zero_iff u).trans
      (exists_congr fun y => and_congr_right fun hy => and_congr_left fun _ =>
        ⟨fun h1 g hg => by
          obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
          obtain ⟨m, hm⟩ := hsat g hg j
          have := h1 _ hm
          rw [map_mul, map_pow, aeval_X] at this
          exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hj), fun h1 g hg => h1 g (hIQ hg)⟩)⟩
    have hdeg := degree_idealHilbertPoly_eq_of_isPrime (isHomogeneous_of_component hP)
      (ringKrullDim_of_isChowFormInt hP h)
    rw [ih L Q hQh δ f' hf'', hQH,
      idealHilbertPoly_sup_of_isPrime (isHomogeneous_of_component hE) hlin (hl (exists_X_notMem h)), hEH,
      coeff_sub_comp (Polynomial.natDegree_le_of_degree_le hdeg.le), Nat.factorial_succ]
    push_cast
    ring

theorem degree_eq_hilbertDegree [CharZero K] {P : Ideal (MvPolynomial (Fin N) K)} [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin N) K)) {D δ : ℕ}
    {f : MvPolynomial (Fin (D + 1) × Fin N) K} (h : IsChowFormInt P D δ f) : δ = hilbertDegree P := by
  have hP' := fun g hg n => homogeneousComponent_mem_of_mem hP (p := g) hg n
  have h1 := degree_eq_coeff D K P hP' δ f h
  rw [← cast_hilbertDegree_of_degree_eq hP
    (degree_idealHilbertPoly_eq_of_isPrime hP (ringKrullDim_of_isChowFormInt hP' h))] at h1
  exact_mod_cast h1

theorem exists_isChowFormInt [CharZero K] {P : Ideal (MvPolynomial (Fin N) K)} (hp : P.IsPrime)
    (hP : P.IsHomogeneous (homogeneousSubmodule (Fin N) K)) {D : ℕ}
    (hD : ringKrullDim (MvPolynomial (Fin N) K ⧸ P) = (D + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) K, IsChowFormInt P D (hilbertDegree P) f := by
  obtain ⟨δ, f, hf⟩ := exists_isChowFormInt_of_ringKrullDim_eq K N D P hp
    (fun g hg n => homogeneousComponent_mem_of_mem hP hg n) hD
  exact ⟨f, degree_eq_hilbertDegree hP hf ▸ hf⟩

theorem comap_map_eq {L σ : Type} [Field L] [Algebra K L] (I : Ideal (MvPolynomial σ K)) :
    (I.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L)).comap
      (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L) = I := by
  obtain ⟨r, hr⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  have hr' : ∀ c : K, r (algebraMap K L c) = c := fun c => LinearMap.congr_fun hr c
  let ρ : MvPolynomial σ L → MvPolynomial σ K := fun p => ∑ s ∈ p.support, monomial s (r (AddMonoidAlgebra.coeff p s))
  have hρ : ∀ p s, AddMonoidAlgebra.coeff (ρ p) s = r (AddMonoidAlgebra.coeff p s) := fun p s => by
    classical
    simp only [ρ, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.1 h, map_zero]
  have hadd : ∀ p q, ρ (p + q) = ρ p + ρ q := fun p q => MvPolynomial.ext _ _ fun s => by
    simp only [hρ, MvPolynomial.coeff_add, map_add (f := _)]
  have hmul : ∀ p (g : MvPolynomial σ K), ρ (p * map (algebraMap K L) g) = ρ p * g := fun p g =>
    MvPolynomial.ext _ _ fun s => by
      classical
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hρ, coeff_mul, map_sum, coeff_map]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  refine le_antisymm (fun g hg => ?_) Ideal.le_comap_map
  have key : ∀ p ∈ I.map (MvPolynomial.map (algebraMap K L) : MvPolynomial σ K →+* MvPolynomial σ L),
      ∀ q, ρ (q * p) ∈ I := fun p hp => by
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      exact fun q => hmul q x ▸ I.mul_mem_left _ hx
    | zero =>
      intro q
      have : ρ (q * 0) = 0 := MvPolynomial.ext _ _ fun s => by simp [hρ]
      exact this ▸ I.zero_mem
    | add x y _ _ hx hy => exact fun q => by rw [mul_add, hadd]; exact I.add_mem (hx q) (hy q)
    | smul a x _ hx => exact fun q => by rw [smul_eq_mul, ← mul_assoc]; exact hx _
  have h1 := key _ hg 1
  have h2 : ρ (1 * map (algebraMap K L) g) = g := MvPolynomial.ext _ _ fun s => by
    rw [hρ, one_mul, coeff_map, hr']
  rwa [h2] at h1

theorem exists_isChowForm [CharZero K] {I : Ideal (MvPolynomial (Fin N) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin N) K))
    (hp : (I.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) :
      MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (AlgebraicClosure K))).IsPrime) {D : ℕ}
    (hD : ringKrullDim (MvPolynomial (Fin N) K ⧸ I) = (D + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin (D + 1) × Fin N) K, IsChowForm I D (hilbertDegree I) f := by
  have hpI : I.IsPrime := by
    rw [← comap_map_eq (L := AlgebraicClosure K) I]
    exact Ideal.comap_isPrime _ _
  obtain ⟨f, hf⟩ := exists_isChowFormInt hpI hI hD
  refine ⟨f, hf.isChowForm ?_⟩
  obtain ⟨hE, hEH⟩ := GlobalTheory.HilbBaseChange.idealHilbertPoly_map K (AlgebraicClosure K) N I
    (fun g hg n => homogeneousComponent_mem_of_mem hI hg n)
  have hE' := isHomogeneous_of_component hE
  obtain ⟨j, hj⟩ := exists_X_notMem hf
  obtain ⟨e, he⟩ := exists_ringKrullDim_quotient_eq_succ hE' (i := j) (fun h => hj (by
    rw [← comap_map_eq (L := AlgebraicClosure K) I, Ideal.mem_comap, map_X]
    exact h))
  have h1 := degree_idealHilbertPoly_eq_of_isPrime hE' he
  rw [hEH, degree_idealHilbertPoly_eq_of_isPrime hI hD] at h1
  obtain rfl : D = e := by exact_mod_cast h1
  obtain ⟨f', hf'⟩ := exists_isChowFormInt hp hE' he
  rw [hilbertDegree, hEH, ← hilbertDegree] at hf'
  have hdvd : f' ∣ map (algebraMap K (AlgebraicClosure K)) f := hf'.dvd_of_forall_aeval_eq_zero fun u hu => by
    obtain ⟨y, hy, h2, h3⟩ := (hf'.zero_iff u).1 hu
    rw [aeval_map_algebraMap]
    refine (hf.zero_iff_of_isAlgClosed hI u).2 ⟨y, hy, fun g hg => ?_, h3⟩
    have := h2 _ (Ideal.mem_map_of_mem _ hg)
    rwa [aeval_map_algebraMap] at this
  have hF0 : map (algebraMap K (AlgebraicClosure K)) f ≠ 0 := fun h =>
    hf.ne_zero (map_injective _ (algebraMap K (AlgebraicClosure K)).injective (h.trans (map_zero _).symm))
  have hFh := ((isMultiHomogeneous_iff_block.1 hf.homog).isHomogeneous).map (algebraMap K (AlgebraicClosure K))
  have hfh := (isMultiHomogeneous_iff_block.1 hf'.homog).isHomogeneous
  obtain ⟨c, hc, hcf⟩ := GlobalTheory.Chow.exists_eq_C_mul_of_dvd hF0 hdvd
    (by rw [hFh.totalDegree hF0, hfh.totalDegree hf'.ne_zero])
  rw [hcf]
  exact (hf'.C_mul hc).irred

end GlobalTheory.ChowExists

namespace GlobalTheory.Published

theorem chowFormIntExists_holds : ChowFormIntExists :=
  chowFormIntExists_iff.2 fun _ _ _ _ _ _ hP hp hD => GlobalTheory.ChowExists.exists_isChowFormInt hp hP hD

theorem chowFormExists_holds : ChowFormExists :=
  chowFormExists_iff.2 fun _ _ _ _ _ _ hP hp hD => GlobalTheory.ChowExists.exists_isChowForm hP hp hD

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdIndepOfLawsM
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
theorem rdIndep_of_lawsM : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ := by
  intro D T h j hj σ hσ
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdIndep_laws T.Q.c GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny GlobalTheory.abelianSchemeLaws_all.2.secTwist (T.U j) σ (h.evalWD j hj)
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ (T.Q.Xo j) T.Q.c)
    (h.unf j hj σ hσ)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneOfMemBase
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.OneMapExact.det_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (h : R.IsGrp F) :
    ∀ u : F.P0, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1 := by
  intro u PP
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simp
  rw [h1] at h2
  rw [← Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.TraceIncl.gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)),
    Units.val_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishTorsion
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem theta_nonvanish_coset (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) (a : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => (a * x).left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ (a * x) τ v ∧ v ≠ 0 :=
  abelianSchemeLaws_all.1.goodPt k P N hN hNk θ hθ a

theorem theta_nonvanish_torsion (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => x.left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ x τ v ∧ v ≠ 0 := by
  obtain ⟨x, hx, rest⟩ := theta_nonvanish_coset k P N hN hNk θ hθ 1
  exact ⟨1 * x, by rw [_root_.one_mul]; exact hx, rest⟩

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOnAdjoinSimple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ringHom_eq_on_adjoin_simple {E : Type} [Field E] [Algebra ℚ E] (f g : E →+* ℂ) (s : E) (h : f s = g s) (x : E)
    (hx : x ∈ IntermediateField.adjoin ℚ ({s} : Set E)) : f x = g x := by
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h
  | algebraMap q => simp
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | inv a _ ha => rw [map_inv₀, map_inv₀, ha]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]

theorem overK_iff_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ) :
    OverK σ ↔ σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD) :=
  ⟨fun h => h _ (IntermediateField.mem_adjoin_simple_self ℚ D.host.sqrtMinusD),
    fun h x hx => ringHom_eq_on_adjoin_simple (σ.comp D.embE) (D.what₂.embLL.comp D.embE) D.host.sqrtMinusD h x hx⟩

theorem overK_iff_good_of_pins {D : D7} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (ha : AlgTie T) (hp : T.Q.Pins)
    (σ : D.what₂.LL →+* ℂ) : OverK σ ↔ GoodEmb T.Q.c (res T σ) := by
  have e0 := res_embLL T ha hp.2.2.1
  have h1 : D.what₂.embLL (D.embE D.host.sqrtMinusD) = T.Q.H.rt0 :=
    (RingHom.congr_fun D.embE_φ₀ D.host.sqrtMinusD).trans hp.1.2.2.1.symm
  have h2 : GoodEmb T.Q.c (res T D.what₂.embLL) := e0 ▸ T.toCore.good_σ₀
  have hx : D.embE D.host.sqrtMinusD = algebraMap T.Q.c.F D.what₂.LL
      (IntermediateField.inclusion T.Q.c.le (ReciprocityTheory.ChartRestriction.G.Geo.Tor.baseKA T.Q.l).ρ) :=
    D.what₂.embLL.injective (h1.trans (Eq.symm h2))
  refine (overK_iff_sqrt σ).trans ⟨fun h => ?_, fun h => ?_⟩
  · exact (congrArg σ hx).symm.trans (h.trans h1)
  · exact (congrArg σ hx).trans (Eq.trans h h1.symm)

end GlobalTheory.GalLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsMultIPOfModel
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLower

theorem IsMultIP₂ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (x y : H.H) :
    ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := by
  have h1 : ∀ x y : H.H, inner ℂ x y ≠ 0 → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := fun x y hxy => by
    by_contra hc
    apply hxy
    rw [h, ipM, dite_eq_right hc, mul_zero]
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, fun v v' => by simp⟩
  by_cases hxy : inner ℂ x y = 0
  · obtain ⟨c, hc⟩ := h1 x (x + y) (by rw [inner_add_right, hxy, add_zero]; exact inner_self_ne_zero.2 hx)
    obtain ⟨c', hc'⟩ := h1 x x (inner_self_ne_zero.2 hx)
    refine ⟨c - c', fun v v' => ?_⟩
    have e : (fun g => star (H.e x v g) * H.e y v' g) =
        fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g := by
      funext g; simp [mul_add]
    rw [e]
    exact ⟨(hc v v').1.sub (hc' v v').1, by rw [integral_sub (hc v v').1 (hc' v v').1, (hc v v').2, (hc' v v').2, sub_mul]⟩
  · exact h1 x y hxy

theorem schurMult_of_models : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), SchurMult R.θ (R.MW i σ) (levSW R i) (chiW R i) (R.νW i) (R.fdW i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R h i σ _ _ _ T hT T' hT'
  obtain ⟨-, hr, hip⟩ := h i σ
  have hT1 : T ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT
  have hT2 : T' ∈ LinearMap.range (R.HW i σ).e := by rw [hr]; exact hT'
  obtain ⟨x, rfl⟩ := hT1
  obtain ⟨y, rfl⟩ := hT2
  exact IsMultIP₂ (R.HW i σ) hip x y

end GlobalTheory.LiftLower

end
end
