module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.UpMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.OffUnitsLeUnitIdl
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CoreAtQIffRowQ
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrPairsHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenEmbeddingVal
noncomputable section

open NumberField IsDedekindDomain Topology Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1

namespace GlobalTheory.CompanionTheory.HeckeFin

variable (L : Type) [Field L] [NumberField L]

def infIdele : (InfiniteAdeleRing L)ˣ →* Ideles L :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

theorem continuous_infIdele : Continuous (infIdele L) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : (InfiniteAdeleRing L)ˣ → InfiniteAdeleRing L) :=
  Units.isOpenEmbedding_val (R := ∀ v : InfinitePlace L, v.Completion)

theorem denseRange_units :
    DenseRange (Units.map (algebraMap L (InfiniteAdeleRing L)).toMonoidHom : Lˣ → (InfiniteAdeleRing L)ˣ) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨l, w, hw, hl⟩ := (InfiniteAdeleRing.denseRange_algebraMap L).exists_mem_open
    ((isOpenEmbedding_val L).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero] at hl
    exact w.ne_zero hl
  exact ⟨w, hw, Units.mk0 l hl0, Units.ext hl.symm⟩

variable {L}

end GlobalTheory.CompanionTheory.HeckeFin
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrPairsPf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem chrUnr_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    {χ : Chr (maximalRealSubfield E) E} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ w) (k : ℕ) :
    UnrAt (χ ^ k) w := by
  induction k with
  | zero =>
    intro x _
    simp [locChar]
  | succ n ih =>
    rw [pow_succ]
    exact UnrAt.mul ih h

private theorem chrVal_pow {E : Type} [Field E] [NumberField E] [IsCMField E]
    (χ : Chr (maximalRealSubfield E) E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) :
    ((val (χ ^ k) w : ℂˣ) : ℂ) = ((val χ w : ℂˣ) : ℂ) ^ k := by
  induction k with
  | zero => simp [val_one]
  | succ n ih => rw [pow_succ, val_mul, Units.val_mul, ih, pow_succ]

theorem UpperTheory.Gal.TP.Chr.chrPairs :
    UpperTheory.Gal.TP.Chr.ChrEx → UpperTheory.Gal.TP.Chr.TypVal → UpperTheory.Gal.TP.Sub.ChrPairs := by
  intro hEx hTyp E _ _ _ hunr n t hn ht emb b w₀ _
  obtain ⟨K, hKodd, hKb⟩ : ∃ K : ℕ, Odd K ∧ -(K : ℤ) ≤ b :=
    ⟨2 * b.natAbs + 1, ⟨b.natAbs, rfl⟩, by omega⟩
  obtain ⟨χ, ψ, hχ0, hH, hV, hA, hInj⟩ :=
    hEx E hunr emb w₀ (fun _ => -1) (fun _ => ⟨-1, by norm_num⟩)
  have hT := hTyp E emb
  have hnorm : ∀ w : HeightOneSpectrum (𝓞 E),
      ((normV w : ℕ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) := by
    intro w
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  obtain ⟨a, ha⟩ := hKodd
  obtain ⟨c, hc⟩ := ht
  obtain ⟨r, hr⟩ := hn
  have ht0 : 0 < t := by omega
  refine ⟨ψ K t,
    typ emb (fun _ => ((t : ℤ) + (K : ℤ) * -1) / 2) (fun _ => ((t : ℤ) - (K : ℤ) * -1) / 2),
    fun j => χ ^ (2 * (j : ℕ)), fun j => χ ^ (K + 2 * (j : ℕ)),
    fun j _ => ((2 * (j : ℕ) : ℕ) : ℤ) * -1, fun j _ => ((K + 2 * (j : ℕ) : ℕ) : ℤ) * -1,
    fun j i => ψ (2 * (j : ℕ)) (2 * ((i : ℕ) : ℤ) - ((n : ℤ) + 2 * t - 2)),
    fun j i => typ emb
      (fun _ => ((2 * ((i : ℕ) : ℤ) - ((n : ℤ) + 2 * t - 2)) + ((2 * (j : ℕ) : ℕ) : ℤ) * -1) / 2)
      (fun _ => ((2 * ((i : ℕ) : ℤ) - ((n : ℤ) + 2 * t - 2)) - ((2 * (j : ℕ) : ℕ) : ℤ) * -1) / 2),
    hA _ _ ⟨a + c + 1, by subst ha hc; push_cast; ring⟩, ?_, ?_,
    (hV K t w₀).1.mpr (chrUnr_pow hχ0 K), fun i => (hV _ _ w₀).1.mpr (chrUnr_pow hχ0 _)⟩
  · intro j
    obtain ⟨h1, h2, h3⟩ := hH (2 * (j : ℕ))
    obtain ⟨h1', h2', h3'⟩ := hH (K + 2 * (j : ℕ))
    refine ⟨h1, h1', h3 n (by omega), h3' (n + t) (by omega), h2, h2', ?_, ?_⟩
    · intro w
      push_cast
      omega
    · refine ⟨fun i => hA _ _ ⟨((j : ℕ) : ℤ) + ((i : ℕ) : ℤ) - r - 2 * c, by push_cast; omega⟩,
        fun w => ?_, fun w => ?_, fun i w => ?_, fun i w => ?_, fun w hκ hψ => ?_⟩
      · dsimp only
        rw [(hT _ _ w).1]
        push_cast
        omega
      · dsimp only
        rw [(hT _ _ w).2]
        push_cast
        omega
      · dsimp only
        rw [(hT _ _ w).1]
        push_cast
        omega
      · dsimp only
        rw [(hT _ _ w).2]
        push_cast
        omega
      · dsimp only at hψ ⊢
        have u0 := (hV K t w).1.mp hκ
        have ux := (hV (2 * (j : ℕ)) _ w).1.mp (hψ ⟨0, ht0⟩)
        have hv : ((val χ w : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        refine ⟨ux, by rw [pow_add]; exact UnrAt.mul u0 ux, ?_, fun i => ?_⟩
        · rw [(hV K t w).2, chrVal_pow, chrVal_pow, hnorm, pow_add,
            mul_inv_cancel_right₀ (pow_ne_zero _ hv)]
          push_cast
          rw [neg_div]
        · rw [(hV _ _ w).2, chrVal_pow, hnorm]
          congr 2
          push_cast
          ring
  · intro i i' h
    have := hInj _ _ _ _ h
    simp at this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ConjDivNorm
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep

namespace UpperTheory.Gal.TP.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem mk_emb_eq (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (v : InfinitePlace E) :
    InfinitePlace.mk (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1 = v := by
  apply (IsCMField.equivInfinitePlace E).injective
  rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply, InfinitePlace.comap_mk,
    (emb (v.comap (algebraMap (maximalRealSubfield E) E))).2, InfinitePlace.mk_embedding]

private theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    starRingEnd ℂ z / (‖starRingEnd ℂ z‖ : ℂ) = (z / (‖z‖ : ℂ))⁻¹ := by
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have hc : starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [RCLike.norm_conj, inv_div]
  field_simp
  rw [hc]

open Classical in
theorem muEmb : MuEmb := by
  intro E _ _ _ hU emb w₀ m hm
  let e : InfinitePlace E → ℤ := fun v =>
    if v.embedding = (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1
    then m (v.comap (algebraMap (maximalRealSubfield E) E))
    else - m (v.comap (algebraMap (maximalRealSubfield E) E))
  have he : ∀ v, Odd (e v) := fun v => by
    by_cases h : v.embedding = (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1
    · simpa [e, h] using hm _
    · simpa [e, h] using hm _
  obtain ⟨μ, hμ, hS⟩ := UpperTheory.ConvolutionTheory.D.muEx E hU {w₀} (Set.finite_singleton w₀) e he
  refine ⟨μ, hμ.1, hμ.2.1, fun k => ?_, hS w₀ rfl⟩
  have hk : ((μ.inf k : ℂˣ) : ℂ) = _ := GlobalTheory.BCT.inf_mu_unit E μ e hμ k
  rw [hk]
  refine Fintype.prod_equiv (IsCMField.equivInfinitePlace E) _ _ fun v => ?_
  rw [IsCMField.equivInfinitePlace_apply]
  have hmk := mk_emb_eq emb v
  have hor := InfinitePlace.mk_eq_iff.1 (hmk.trans (InfinitePlace.mk_embedding v).symm)
  by_cases h : v.embedding = (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1
  · simp only [e, if_pos h]
    rw [← h]
  · have hc : (emb (v.comap (algebraMap (maximalRealSubfield E) E))).1 =
        ComplexEmbedding.conjugate v.embedding := by
      rcases hor with h' | h'
      · exact absurd h'.symm h
      · rw [← h']
        exact (star_star _).symm
    have hz : v.embedding (k : E) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    simp only [e, if_neg h]
    rw [hc, ComplexEmbedding.conjugate_coe_eq, conj_div_norm hz, inv_zpow']

end UpperTheory.Gal.TP.Chr
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFacts
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem symm_eq_mk {E : Type} [Field E] [NumberField E] [IsCMField E]
    (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (w : InfinitePlace (maximalRealSubfield E)) :
    (IsCMField.equivInfinitePlace E).symm w = InfinitePlace.mk (emb w).1 := by
  rw [Equiv.symm_apply_eq, IsCMField.equivInfinitePlace_apply, InfinitePlace.comap_mk, (emb w).2,
    InfinitePlace.mk_embedding]

private theorem logNorm_diag {E : Type} [Field E] [NumberField E] [IsCMField E] (k : Eˣ) :
    GlobalTheory.Mem.Chr.CharModel.logNorm E (infDiag k) = ∑ v : InfinitePlace E, 2 * Real.log (v (k : E)) := by
  have hp : ∀ v : InfinitePlace E, v (k : E) ≠ 0 := fun v => by simp
  have h := InfinitePlace.prod_eq_abs_norm (k : E)
  change GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.infDiag k) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm, (GlobalTheory.Mem.Chr.CharModel.infDiag_parts k).1,
    (GlobalTheory.Mem.Chr.CharModel.infDiag_parts k).2, GlobalTheory.Mem.Chr.CharModel.logFin_one, sub_zero,
    GlobalTheory.Mem.Chr.CharModel.logInf_principal, ← h, Real.log_prod (fun v _ => pow_ne_zero _ (hp v))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))]
  norm_num

theorem UpperTheory.Gal.TP.Chr.absFacts :
    UpperTheory.Gal.TP.Chr.AbsFacts := by
  intro E _ _ _ emb z
  refine ⟨fun w => ⟨DiscreteGroups.T1.G.absC_unrAt z w, ?_⟩, fun k => ?_⟩
  · simpa [Formalism.UG.qV, Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply,
      Submodule.cardQuot_apply] using DiscreteGroups.T1.G.absC_val z w
  ·
    change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (infDiag k)) = _
    rw [logNorm_diag, ← (IsCMField.equivInfinitePlace E).symm.sum_comp, Complex.ofReal_sum, Finset.mul_sum,
      Complex.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    have h0 : 0 < ‖(emb w).1 (k : E)‖ := norm_pos_iff.2 ((map_ne_zero _).2 k.ne_zero)
    rw [symm_eq_mk emb w, InfinitePlace.apply, Complex.cpow_def_of_ne_zero (by exact_mod_cast h0.ne'),
      ← Complex.ofReal_log h0.le]
    congr 1
    push_cast
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadEx
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

set_option maxHeartbeats 400000 in
theorem UpperTheory.Gal.TP.Chr.readEx :
    UpperTheory.Gal.TP.Chr.ReadEx := by
  intro E _ _ _ μ hU
  let e := GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)
  let f : (AE (↥(maximalRealSubfield E)) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ := Units.map (e : _ →* _)
  refine ⟨{ toFun := fun z => ⟨((μ.1 (f z) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hU (f z))⟩,
            map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp only [map_mul, Units.val_mul]
    rfl
  · intro z
    rfl
  · have hf : Continuous f := by
      show Continuous (Units.map (e : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E))
      exact Continuous.units_map _ (GlobalTheory.UnitaryHeckeBaseChange.continuous_toAdele _ E)
    have hμc : Continuous (μ.1 : Ideles E → ℂˣ) := μ.2.1
    refine continuous_induced_rng.2 ?_
    exact Units.continuous_val.comp (hμc.comp hf)
  · intro x
    apply Subtype.ext
    show ((μ.1 (f _) : ℂˣ) : ℂ) = 1
    rw [show f _ = diagUnits E x from Units.ext ?_, μ.2.2 x]
    · rfl
    · exact GlobalTheory.UnitaryHeckeBaseChange.toAdele_incA (x : E)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadRes
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr
open scoped TensorProduct

theorem UpperTheory.Gal.TP.Chr.readRes :
    UpperTheory.Gal.TP.Chr.ReadRes := by
  intro E _ _ _ μ χ hR hμ a
  rw [hR]
  have h3 : ∀ {σ : E →ₐ[↥(maximalRealSubfield E)] E} (h : HeckeCharacterZeroLocus.ThmBIn.IsCMExt (↥(maximalRealSubfield E)) E σ),
      Units.map ((GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv h).toRingHom
        : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E)
      (Units.map (algebraMap (AF ↥(maximalRealSubfield E)) (AE (↥(maximalRealSubfield E)) E)
        : AF ↥(maximalRealSubfield E) →* AE (↥(maximalRealSubfield E)) E) a)
      = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E a := fun _ =>
    Units.ext (GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap (a : AF ↥(maximalRealSubfield E)))
  erw [h3 (GlobalTheory.GalOfCusp.isCMExt_real E), hμ a]
  simp only [GlobalTheory.GalOfCusp.quadChar, MonoidHom.comp_apply]
  split_ifs with hm
  · obtain ⟨y, ⟨t, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.1 hm
    have hn : GlobalTheory.IdeleNormChar.normSign E a = 1 := by
      refine (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).2 ⟨t, ?_⟩
      rw [← hyz]
      simpa [GlobalTheory.QuadSymbol.toUnits, GlobalTheory.QuadSymbol.normGroup] using hz
    simp [hn]
  · rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E a) with hn | hn
    · exfalso
      obtain ⟨t, ht⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 hn
      exact hm (Subgroup.mem_sup.2 ⟨_, ⟨t, rfl⟩, _, ht, mul_div_cancel _ _⟩)
    · simp [hn]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrExPf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

noncomputable section

namespace UpperTheory.Gal.TP.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private def psi (μ : HChar E) (k : ℕ) (s : ℤ) : HChar E := μ ^ k * Model.absC E ((s : ℂ) / 2)

private theorem hpow_apply (μ : HChar E) (k : ℕ) (x) : (μ ^ k).1 x = μ.1 x ^ k := by
  rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]

private theorem hpow_loc (μ : HChar E) (k : ℕ) (w) (x) : (μ ^ k).loc w x = μ.loc w x ^ k :=
  hpow_apply μ k _

private theorem hpow_inf (μ : HChar E) (k : ℕ) (x) : (μ ^ k).inf x = μ.inf x ^ k :=
  hpow_apply μ k _

private theorem hpow_val (μ : HChar E) (k : ℕ) (w) : (μ ^ k).val w = μ.val w ^ k :=
  hpow_apply μ k _

private theorem lc_pow (χ : Chr (maximalRealSubfield E) E) (k : ℕ) (w : HeightOneSpectrum (𝓞 E)) (x) :
    locChar (χ ^ k) w x = locChar χ w x ^ k := by
  show Circle.toUnits ((χ ^ k) (locIdele _ w x)) = Circle.toUnits (χ (locIdele _ w x)) ^ k
  rw [MonoidHom.pow_apply, map_pow]

private theorem typ_term (z : ℂ) (hz : z ≠ 0) (a b : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (a - b) * ((‖z‖ : ℝ) : ℂ) ^ (a + b) = z ^ a * (starRingEnd ℂ z) ^ b := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
  have hc : starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 / z := by
    rw [eq_div_iff hz, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h2 : (((‖z‖ : ℝ) : ℂ) ^ 2) ^ b = (((‖z‖ : ℝ) : ℂ) ^ b) ^ 2 := by
    rw [← zpow_natCast, ← zpow_natCast, zpow_comm]
  have hA : z ^ a ≠ 0 := zpow_ne_zero _ hz
  have hB : z ^ b ≠ 0 := zpow_ne_zero _ hz
  have hC : ((‖z‖ : ℝ) : ℂ) ^ a ≠ 0 := zpow_ne_zero _ hn
  have hD : ((‖z‖ : ℝ) : ℂ) ^ b ≠ 0 := zpow_ne_zero _ hn
  rw [hc, div_zpow, div_zpow, zpow_sub₀ hz, zpow_sub₀ hn, zpow_add₀ hn, h2]
  field_simp

private theorem inf_psi (hAb : AbsFacts) (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w)
    (μ : HChar E) (m : InfinitePlace (maximalRealSubfield E) → ℤ) (hμ : InfExp emb μ m) (k : ℕ) (s : ℤ) (x : Eˣ) :
    (((psi μ k s).inf x : ℂˣ) : ℂ) = ∏ w, ((emb w).1 (x : E) / ‖(emb w).1 (x : E)‖) ^ ((k : ℤ) * m w) *
      ((‖(emb w).1 (x : E)‖ : ℝ) : ℂ) ^ s := by
  rw [psi, HChar.inf_mul, Units.val_mul, hpow_inf, Units.val_pow_eq_pow_val, hμ x, (hAb E emb _).2 x,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h2 : (2 : ℂ) * ((s : ℂ) / 2) = s := by ring
  rw [h2, Complex.cpow_intCast, mul_comm (k : ℤ), zpow_mul, zpow_natCast]

private theorem exps {k : ℕ} {s m : ℤ} (hev : Even ((k : ℤ) + s)) (hm : Odd m) :
    ∃ a b : ℤ, (s + k * m) / 2 = a ∧ (s - k * m) / 2 = b ∧ a + b = s ∧ a - b = k * m := by
  obtain ⟨r, hr⟩ := hev
  obtain ⟨t, rfl⟩ := hm
  refine ⟨r + k * t, r - k * t - k, ?_, ?_, ?_, ?_⟩
  · rw [show s + k * (2 * t + 1) = 2 * (r + k * t) by linear_combination hr,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  · rw [show s - k * (2 * t + 1) = 2 * (r - k * t - k) by linear_combination hr,
      Int.mul_ediv_cancel_left _ two_ne_zero]
  · linear_combination -hr
  · ring

end UpperTheory.Gal.TP.Chr

theorem UpperTheory.Gal.TP.Chr.chrEx :
    UpperTheory.Gal.TP.Chr.MuEmb → UpperTheory.Gal.TP.Chr.ReadEx → UpperTheory.Gal.TP.Chr.ReadLoc → UpperTheory.Gal.TP.Chr.ReadRes → UpperTheory.Gal.TP.Chr.ReadExp → UpperTheory.Gal.TP.Chr.AbsFacts → UpperTheory.Gal.TP.Chr.TypProd → UpperTheory.Gal.TP.Chr.ExpInj → UpperTheory.Gal.TP.Chr.ChrEx := by
  intro hMu hRE hRL hRR hRX hAb hTP hEI E _ _ _ hun emb w₀ m hm
  have hloc (α β : HChar E) (w : HeightOneSpectrum (𝓞 E)) (x) :
      (α * β).loc w x = α.loc w x * β.loc w x := by
    rfl
  obtain ⟨μ, hμu, hμq, hμi, hμ0⟩ := hMu E hun emb w₀ m hm
  obtain ⟨χ, hr, hH⟩ := hRE E μ hμu
  have hl := hRL E μ χ hr
  have hres := hRR E μ χ hr hμq
  have hexp := hRX E emb μ χ m hr hμi
  have hval : ∀ w, val χ w = μ.val w := fun w => by
    show locChar χ w (atFin w (unif w)) = μ.loc w (atFin w (unif w))
    rw [hl]
  refine ⟨χ, psi μ, fun x hx => ?_, fun k => ⟨⟨hH.1.pow k, fun x => ?_⟩, fun z hz => ?_, fun j hj a => ?_⟩,
    fun k s w => ⟨⟨fun h x hx => ?_, fun h x hx => ?_⟩, ?_⟩, fun k s hev x _ => ?_, fun k k' s s' h => ?_⟩
  · rw [hl]
    exact hμ0 x hx
  · rw [MonoidHom.pow_apply, hH.2 x, one_pow]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hexp z hz, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    beta_reduce
    rw [mul_comm (k : ℤ), zpow_mul, zpow_natCast]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hres a]
    split_ifs with h
    · simp
    · rw [pow_one, neg_one_pow_eq_pow_mod_two, ← hj, ← neg_one_pow_eq_pow_mod_two]
  · have h1 : (psi μ k s).loc w x = 1 := h x hx
    rw [psi, hloc, hpow_loc, ((hAb E emb _).1 w).1 x hx, mul_one] at h1
    rw [lc_pow, hl]
    exact h1
  · have h1 : locChar (χ ^ k) w x = 1 := h x hx
    rw [lc_pow, hl] at h1
    rw [psi, hloc, hpow_loc, ((hAb E emb _).1 w).1 x hx, mul_one]
    exact h1
  · rw [psi, HChar.val_mul, Units.val_mul, hpow_val, Units.val_pow_eq_pow_val, ((hAb E emb _).1 w).2, hval, neg_div]
  · rw [hTP E emb _ _ (x : E), inf_psi hAb emb μ m hμi]
    refine Finset.prod_congr rfl fun w _ => ?_
    obtain ⟨a, b, ha, hb, h1, h2⟩ := exps hev (hm w)
    have hz : (emb w).1 (x : E) ≠ 0 := (map_ne_zero (emb w).1).2 x.ne_zero
    beta_reduce
    rw [ha, hb, ← typ_term _ hz a b, h1, h2]
  · have h1 := hEI E emb (fun w => k * m w) (fun w => k' * m w) s s' fun x => by
      rw [← inf_psi hAb emb μ m hμi k s x, ← inf_psi hAb emb μ m hμi k' s' x, h]
    obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
    have h3 : (k : ℤ) * m w = k' * m w := congrFun h1 w
    have hm0 : m w ≠ 0 := fun h0 => by simpa [h0] using hm w
    exact_mod_cast mul_right_cancel₀ hm0 h3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadExp
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.TP.Chr

private theorem exists_read {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) :
    ∃ ρ : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous ρ ∧
      ∀ x : E, ρ (algebraMap E (InfinitePlace.mk φ).Completion x) = φ x := by
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  have he : ∀ x : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)
      (algebraMap E (InfinitePlace.mk φ).Completion x) = (InfinitePlace.mk φ).embedding x := fun x =>
    by
      rw [InfinitePlace.Completion.algebraMap_apply]
      exact InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ x)
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨_, hc, fun x => (he x).trans (by rw [h])⟩
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)),
      Complex.continuous_conj.comp hc, fun x => ?_⟩
    rw [RingHom.comp_apply, he, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

private theorem inf_formula {E ι : Type} [Field E] [NumberField E] [Fintype ι] (μ : HChar E) (φ : ι → E →+* ℂ)
    (m : ι → ℤ) (ρ : ∀ i, (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hc : ∀ i, Continuous (ρ i))
    (hρ : ∀ i x, ρ i (algebraMap E _ x) = φ i x)
    (h : ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : E) / ‖φ i (k : E)‖) ^ m i)
    (y : (InfiniteAdeleRing E)ˣ) :
    ((μ.1 (GlobalTheory.CompanionTheory.HeckeFin.infIdele E y) : ℂˣ) : ℂ) =
      ∏ i, (ρ i ((y : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) /
        ‖ρ i ((y : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)))‖) ^ m i := by
  have hne : ∀ (i) (u : (InfiniteAdeleRing E)ˣ), ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) ≠ 0 := by
    intro i u e
    have h1 : (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)) *
        ((u⁻¹ : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)) = 1 :=
      congrFun u.mul_inv (InfinitePlace.mk (φ i))
    have h2 := congrArg (ρ i) h1
    rw [map_mul, map_one, e, zero_mul] at h2
    exact zero_ne_one h2
  have hci : ∀ i, Continuous fun u : (InfiniteAdeleRing E)ˣ => ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) :=
    fun i => (hc i).comp ((continuous_apply _).comp Units.continuous_val)
  have hL : Continuous fun u : (InfiniteAdeleRing E)ˣ => ((μ.1 (GlobalTheory.CompanionTheory.HeckeFin.infIdele E u) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (μ.2.1.comp (GlobalTheory.CompanionTheory.HeckeFin.continuous_infIdele E))
  have hR : Continuous fun u : (InfiniteAdeleRing E)ˣ => ∏ i, (ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) /
      ‖ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)))‖) ^ m i := by
    refine continuous_finsetProd _ fun i _ => ?_
    refine Continuous.zpow₀ ((hci i).div (Complex.continuous_ofReal.comp (hci i).norm) fun u => ?_) _ fun u => Or.inl ?_
    · exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne i u))
    · exact div_ne_zero (hne i u) (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne i u)))
  refine congrFun ((GlobalTheory.CompanionTheory.HeckeFin.denseRange_units E).equalizer hL hR (funext fun k => ?_)) y
  have e1 : GlobalTheory.CompanionTheory.HeckeFin.infIdele E (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = infDiag k := by
    classical
    refine Units.ext ?_
    rw [infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
    let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
    let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
    refine Prod.ext ?_ ?_
    · change _ = p1 _
      rw [map_prod]
      change _ = ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E))
      exact (Finset.univ_prod_mulSingle _).symm
    · change _ = p2 _
      rw [map_prod]
      exact (Finset.prod_eq_one fun _ _ => rfl).symm
  simp only [Function.comp_apply]
  rw [e1]
  refine (h k).trans (Finset.prod_congr rfl fun i _ => ?_)
  have e2 : ρ i (((Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E)
      (InfinitePlace.mk (φ i))) = φ i (k : E) := hρ i k
  rw [e2]

private theorem piInf_read {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : EmbOver E w) (ρ : (InfinitePlace.mk τ.1).Completion →+* ℂ) (hc : Continuous ρ)
    (hρ : ∀ x, ρ (algebraMap E _ x) = τ.1 x) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piInf τ z = ρ ((GlobalTheory.UnitaryHeckeBaseChange.toAdele F E z).1 (InfinitePlace.mk τ.1)) := by
  have key : (fun b : InfiniteAdeleRing F => InfinitePlace.Completion.extensionEmbedding w (b w)) =
      fun b => ρ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E b (InfinitePlace.mk τ.1)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply _))
      (hc.comp ((continuous_apply _).comp (GlobalTheory.UnitaryHeckeBaseChange.continuous_infiniteAdeleMap F E))) (funext fun x => ?_)
    have h1 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) = w.embedding x :=
      by
        rw [InfinitePlace.Completion.algebraMap_apply]
        exact InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E (algebraMap F _ x) (InfinitePlace.mk τ.1) =
        algebraMap E (InfinitePlace.mk τ.1).Completion (algebraMap F E x) :=
      congrFun (congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)) _
    simp only [Function.comp_apply]
    change InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) = ρ _
    rw [h1, h2, hρ]
    exact (RingHom.congr_fun τ.2 x).symm
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero ρ).symm
  | add x y hx hy =>
    rw [map_add (f := _), hx, hy, map_add (f := _), ← map_add (f := _)]
    rfl
  | tmul a e =>
    rw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul]
    have h3 : InfinitePlace.Completion.extensionEmbedding w (a.1 w) =
        ρ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a.1 (InfinitePlace.mk τ.1)) := congrFun key a.1
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E (AdeleRing (𝓞 E) E) e).1 (InfinitePlace.mk τ.1) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a.1 (InfinitePlace.mk τ.1) *
          algebraMap E (InfinitePlace.mk τ.1).Completion e := rfl
    rw [h4, map_mul, ← h3, hρ]
    rfl

theorem readExp : ReadExp := by
  intro E _ _ _ emb μ χ m hR hI z hz
  have hcm := GlobalTheory.GalOfCusp.isCMExt_real E
  set x : Ideles E := Units.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv hcm).toRingHom.toMonoidHom z with hx
  have hx1 : (x : AdeleRing (𝓞 E) E) = GlobalTheory.UnitaryHeckeBaseChange.toAdele _ E (z : AE (maximalRealSubfield E) E) := rfl
  have hfin : (x : AdeleRing (𝓞 E) E).2 = 1 := by
    let u : AF (maximalRealSubfield E) := (0, 1)
    have h0 : u • ((z : AE (maximalRealSubfield E) E) - 1) = 0 := hz u (map_zero _)
    have h1 := congrArg (GlobalTheory.UnitaryHeckeBaseChange.toAdele (maximalRealSubfield E) E) h0
    rw [Algebra.smul_def, map_mul, GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap, map_sub, map_one, map_zero, ← hx1] at h1
    have h2 := congrArg Prod.snd h1
    have h3 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E u).2 = 1 := map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)
    change (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E u).2 * ((x : AdeleRing (𝓞 E) E).2 - 1) = 0 at h2
    rw [h3, one_mul] at h2
    exact sub_eq_zero.1 h2
  let y : (InfiniteAdeleRing E)ˣ := Units.map (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom x
  have hxy : x = GlobalTheory.CompanionTheory.HeckeFin.infIdele E y := Units.ext (Prod.ext rfl hfin)
  choose ρ hc hρ using fun w => exists_read (emb w).1
  have hf := inf_formula μ (fun w => (emb w).1) m ρ hc hρ hI y
  rw [hR z]
  change ((μ.1 x : ℂˣ) : ℂ) = _
  rw [hxy, hf]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [piInf_read (emb w) (ρ w) (hc w) (hρ w) z]
  rfl

end UpperTheory.Gal.TP.Chr

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ReadLoc
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

open scoped TensorProduct

namespace UpperTheory.Gal.TP.Chr

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem fst_extZero (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    (GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (extZero F E y)).1 = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : extZero F E (a ⊗ₜ[F] x) =
        (((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) ⊗ₜ[F] x : HeckeCharacterZeroLocus.ThmBIn.AF F ⊗[F] E) :=
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ _ _
    rw [h]
    erw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul]
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E 0 * _ = 0
    rw [map_zero, zero_mul]
  | add y z hy hz =>
    simp only [map_add (f := _)]
    erw [Prod.fst_add, hy, hz]
    simp

private theorem snd_extZero (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    (GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (extZero F E y)).2 = finAdEquiv F E y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : extZero F E (a ⊗ₜ[F] x) =
        (((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) ⊗ₜ[F] x : HeckeCharacterZeroLocus.ThmBIn.AF F ⊗[F] E) :=
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ _ _
    rw [h]
    refine (congrArg (fun z : AdeleRing (𝓞 E) E => z.2)
      (GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul (F := F) (E := E) ((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) x)).trans ?_
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E a * algebraMap E (FiniteAdeleRing (𝓞 E) E) x = _
    apply RestrictedProduct.ext
    intro w
    refine Eq.trans ?_ (finAdEquiv_tmul a x w).symm
    simp only [complMap_rfl, GlobalTheory.CharTransport.locMap_eq]
    rfl
  | add y z hy hz =>
    simp only [map_add (f := _)]
    erw [Prod.snd_add, hy, hz]

private theorem toAdele_locIdele (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (locIdele F w x : AF F ⊗[F] E) =
      (GlobalTheory.Mem.Chr.localIdele E w x : AdeleRing (𝓞 E) E) := by
  rw [coe_locIdele]
  simp only [map_add (f := _), map_sub, map_one]
  refine Prod.ext ?_ ?_
  · erw [Prod.fst_add, Prod.fst_sub, fst_extZero, fst_extZero]
    simp
    rfl
  · erw [Prod.snd_add, Prod.snd_sub, snd_extZero, snd_extZero]
    simp
    rfl

end

end UpperTheory.Gal.TP.Chr

theorem UpperTheory.Gal.TP.Chr.readLoc :
    UpperTheory.Gal.TP.Chr.ReadLoc := by
  intro E _ _ _ μ χ hR w
  ext y
  simp only [locChar, Formalism.L2.Host.HChar.loc, MonoidHom.comp_apply]
  show ((χ ((locIdele (↥(maximalRealSubfield E)) w) y) : Circle) : ℂ) = _
  rw [hR]
  congr 2
  exact Units.ext (toAdele_locIdele w y)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.TypVal
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep

namespace UpperTheory.Gal.TP.Chr

private theorem pl_emb {E : Type} [Field E] [NumberField E] [IsCMField E]
    {w : InfinitePlace (maximalRealSubfield E)} (τ : EmbOver E w) : pl τ.1 = w := by
  unfold pl
  rw [InfinitePlace.comap_mk, τ.2, InfinitePlace.mk_embedding]

private theorem pl_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    pl (ComplexEmbedding.conjugate φ) = pl φ := by
  unfold pl
  rw [InfinitePlace.mk_conjugate_eq]

private theorem conj_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate φ ≠ φ := fun h =>
  IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.mpr h)

theorem typVal : TypVal := by
  intro E _ _ _ emb a b w
  have h1 : pl (emb w).1 = w := pl_emb (emb w)
  have h2 : pl (ComplexEmbedding.conjugate (emb w).1) = w := (pl_conj _).trans h1
  constructor
  · unfold typ
    rw [h1]
    exact if_pos rfl
  · unfold typ
    rw [h2]
    exact if_neg (conj_ne _)

end UpperTheory.Gal.TP.Chr

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.TypProd
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

private theorem pl_emb {E : Type} [Field E] [NumberField E] [IsCMField E]
    {w : InfinitePlace (maximalRealSubfield E)} (τ : EmbOver E w) : pl τ.1 = w := by
  unfold pl
  rw [InfinitePlace.comap_mk, τ.2, InfinitePlace.mk_embedding]

private theorem pl_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    pl (ComplexEmbedding.conjugate φ) = pl φ := by
  unfold pl
  rw [InfinitePlace.mk_conjugate_eq]

private theorem eq_or_conj_of_pl_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    {φ ψ : E →+* ℂ} (h : pl φ = pl ψ) : φ = ψ ∨ φ = ComplexEmbedding.conjugate ψ := by
  have hmk : InfinitePlace.mk φ = InfinitePlace.mk ψ :=
    (IsCMField.equivInfinitePlace E).injective (by
      simpa only [IsCMField.equivInfinitePlace_apply, pl] using h)
  rcases InfinitePlace.mk_eq_iff.1 hmk with h' | h'
  · exact Or.inl h'
  · right
    rw [← h']
    exact (star_star φ).symm

theorem UpperTheory.Gal.TP.Chr.typProd :
    UpperTheory.Gal.TP.Chr.TypVal → UpperTheory.Gal.TP.Chr.TypProd := by
  intro hv E _ _ _ emb a b x
  classical
  rw [← Finset.prod_fiberwise Finset.univ (pl (E := E))]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : (emb w).1 ≠ ComplexEmbedding.conjugate (emb w).1 := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal _ (ComplexEmbedding.isReal_iff.2 h.symm)
  have hfib : Finset.univ.filter (fun φ : E →+* ℂ => pl φ = w) =
      {(emb w).1, ComplexEmbedding.conjugate (emb w).1} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      exact eq_or_conj_of_pl_eq (h.trans (pl_emb (emb w)).symm)
    · rintro (rfl | rfl)
      · exact pl_emb _
      · rw [pl_conj, pl_emb]
  rw [hfib, Finset.prod_pair hne, (hv E emb a b w).1, (hv E emb a b w).2,
    ComplexEmbedding.conjugate_coe_eq]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ExpInj
open NumberField IsDedekindDomain GlobalTheory.AdelicU

namespace UpperTheory.Gal.TP.Chr

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private lemma exists_ext (τ : E →+* ℂ) :
    ∃ e : (InfinitePlace.mk τ).Completion → ℂ, Continuous e ∧ Function.Surjective e ∧
      ∀ x : E, e (algebraMap E _ x) = τ x := by
  have hs := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
    (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
  have hc : Continuous (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ)) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous
  have hv : ∀ x : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk τ)
      (algebraMap E _ x) = (InfinitePlace.mk τ).embedding x := fun x => by
    simpa [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply] using
      InfinitePlace.Completion.extensionEmbedding_coe _ (WithAbs.toAbs _ x)
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · exact ⟨_, hc, hs, fun x => by rw [hv, h]⟩
  · refine ⟨fun z => starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding _ z),
      Complex.continuous_conj.comp hc, fun y => ?_, fun x => ?_⟩
    · obtain ⟨z, hz⟩ := hs (starRingEnd ℂ y)
      exact ⟨z, by simp [hz]⟩
    · simp only [hv, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

private lemma dense_emb (emb : ∀ w : InfinitePlace (maximalRealSubfield E), EmbOver E w) :
    DenseRange (fun (x : E) (w : InfinitePlace (maximalRealSubfield E)) => (emb w).1 x) := by
  classical
  have key : ∀ w, (InfinitePlace.mk (emb w).1).comap (algebraMap (maximalRealSubfield E) E) = w := by
    intro w
    rw [InfinitePlace.comap_mk, (emb w).2, InfinitePlace.mk_embedding]
  have hinj : ∀ w w', InfinitePlace.mk (emb w).1 = InfinitePlace.mk (emb w').1 → w = w' := by
    intro w w' h
    rw [← key w, ← key w', h]
  choose e hc hs he using fun w => exists_ext (emb w).1
  let T : (∀ v : InfinitePlace E, v.Completion) → (∀ _ : InfinitePlace (maximalRealSubfield E), ℂ) :=
    fun f w => e w (f (InfinitePlace.mk (emb w).1))
  have hT : Continuous T := continuous_pi fun w => (hc w).comp (continuous_apply _)
  have hTs : Function.Surjective T := by
    intro y
    choose g hg using fun w => hs w (y w)
    have hcast : ∀ w w' (h : InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1),
        (h ▸ g w' : (InfinitePlace.mk (emb w).1).Completion) = g w := by
      intro w w' h
      obtain rfl := hinj _ _ h
      rfl
    refine ⟨fun v => if h : ∃ w, InfinitePlace.mk (emb w).1 = v then h.choose_spec ▸ g h.choose else 0, ?_⟩
    funext w
    have hex : ∃ w', InfinitePlace.mk (emb w').1 = InfinitePlace.mk (emb w).1 := ⟨w, rfl⟩
    simp only [T, dif_pos hex]
    rw [hcast w _ hex.choose_spec, hg]
  have hd := hTs.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hT
  convert hd using 1
  funext x w
  exact (he w x).symm

end

theorem expInj : ExpInj := by
  intro E _ _ _ emb m m' s s' h
  classical
  funext w₀
  let F : (InfinitePlace (maximalRealSubfield E) → ℤ) → ℤ →
      (InfinitePlace (maximalRealSubfield E) → ℂ) → ℂ :=
    fun n t y => ∏ w, (y w / ‖y w‖) ^ n w * ((‖y w‖ : ℝ) : ℂ) ^ t
  let U : Set (InfinitePlace (maximalRealSubfield E) → ℂ) := {y | ∀ w, y w ≠ 0}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const
  have hcont : ∀ n t, ContinuousOn (F n t) U := by
    intro n t
    refine continuousOn_finsetProd _ fun w _ => ?_
    have h1 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => y w := continuous_apply w
    have h2 : Continuous fun y : InfinitePlace (maximalRealSubfield E) → ℂ => ((‖y w‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp h1.norm
    have hne : ∀ y ∈ U, ((‖y w‖ : ℝ) : ℂ) ≠ 0 := fun y hy => by
      simpa using hy w
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (h1.continuousOn.div h2.continuousOn hne) _
      fun y hy => Or.inl (div_ne_zero (hy w) (hne y hy))) (ContinuousOn.zpow₀ h2.continuousOn _
      fun y hy => Or.inl (hne y hy))
  have hEq : ∀ y ∈ U, F m s y = F m' s' y := by
    intro y hy
    by_contra hne
    have hop := ((hcont m s).sub (hcont m' s')).isOpen_inter_preimage hU
      (isOpen_compl_singleton (x := (0 : ℂ)))
    obtain ⟨x, hxU, hx⟩ := (dense_emb emb).exists_mem_open hop
      ⟨y, hy, fun h0 => hne (sub_eq_zero.1 h0)⟩
    have hx0 : x ≠ 0 := fun h0 => hxU w₀ (by simp [h0])
    exact hx (sub_eq_zero.2 (h (Units.mk0 x hx0)))
  have hF : ∀ n t (θ : ℝ), F n t (Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I))) =
      Complex.exp (θ * Complex.I) ^ n w₀ := by
    intro n t θ
    simp only [F]
    rw [Finset.prod_eq_single w₀]
    · simp [Complex.norm_exp_ofReal_mul_I]
    · intro w _ hw
      simp [Function.update_of_ne hw]
    · simp
  have hUy : ∀ θ : ℝ, Function.update (1 : InfinitePlace (maximalRealSubfield E) → ℂ) w₀ (Complex.exp (θ * Complex.I)) ∈ U := by
    intro θ w
    by_cases hw : w = w₀
    · subst hw; simp [Complex.exp_ne_zero]
    · simp [Function.update_of_ne hw]
  by_contra hne
  have hd0 : ((m w₀ - m' w₀ : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hne
  set θ : ℝ := Real.pi / ((m w₀ - m' w₀ : ℤ) : ℝ) with hθ
  have h1 := hEq _ (hUy θ)
  rw [hF, hF] at h1
  have h2 : Complex.exp (θ * Complex.I) ^ (m w₀ - m' w₀) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  rw [← Complex.exp_int_mul] at h2
  have h3 : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ * Complex.I) = Real.pi * Complex.I := by
    have : ((m w₀ - m' w₀ : ℤ) : ℂ) * (θ : ℂ) = Real.pi := by
      have : ((m w₀ - m' w₀ : ℤ) : ℝ) * θ = Real.pi := by
        rw [hθ]; field_simp
      exact_mod_cast this
    rw [← mul_assoc, this]
  rw [h3, Complex.exp_pi_mul_I] at h2
  norm_num at h2

end UpperTheory.Gal.TP.Chr
end

namespace UpperTheory.Gal.TP.Chr

theorem chrEx_holds : ChrEx := chrEx muEmb readEx readLoc readRes readExp absFacts (typProd typVal) expInj

theorem chrPairs_holds : UpperTheory.Gal.TP.Sub.ChrPairs := chrPairs chrEx_holds typVal

end UpperTheory.Gal.TP.Chr
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP

open Sub

theorem twoUpOK_of_steps (hT : UpperTheory.TP.TLiftK) (hC : ChrPairs) (hU : UpOf) (hB : BaseNG) : TwoUpOK := by
  intro E _ _ _ hE hK _ hI n hn he U hA lam hl w₀ hw₀
  obtain ⟨Bs, δ, 𝔞, hG, hX, hW⟩ := hB E hE hI
  obtain ⟨d₀, hd⟩ := hT E Bs ⟨hG.cm, hK, hG.unram, hG.std, hG.inert, hG.psiP⟩ n hn _ rfl (hX n)
  set t := 2 * (d₀ + n) + 1 with ht
  obtain ⟨b, hb⟩ := (Set.finite_range fun x : InfinitePlace (maximalRealSubfield E) × Fin n => (lam (Bs.emb x.1).1).w x.2).bddBelow
  obtain ⟨κ, m, χX, χW, mX, mW, ψ, p, hκ, hj, hne, hu, hu'⟩ :=
    hC E hE n t he ⟨_, rfl⟩ Bs.emb (2 * b - ((n + t : ℕ) : ℤ)) w₀ hw₀
  have key : ∀ j, ∃ U' lam', IsUp U lam κ m U' lam' (ψ j) (p j) := fun j => by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hj j
    obtain ⟨U', hL⟩ := hd (n + t) (by omega) _ δ rfl (hW (n + t)) (χX j) (χW j) (mX j) (mW j) a1 a2 a3 a4 a5 a6 U
      (fun w => lam (Bs.emb w).1) hA (fun w => hl _) fun w k => by
        have h1 := a7 w
        have h2 : b ≤ (lam (Bs.emb w).1).w k := hb ⟨(w, k), rfl⟩
        omega
    exact ⟨U', hU E n t hn (by omega) Bs _ _ _ _ U hA lam hl U' hL κ m _ _ a8⟩
  obtain ⟨U₁, l₁, h₁⟩ := key 0
  obtain ⟨U₂, l₂, h₂⟩ := key 1
  exact ⟨t, κ, m, U₁, U₂, l₁, l₂, ψ 0, ψ 1, p 0, p 1, he.add_odd ⟨_, rfl⟩, hκ, h₁, h₂, hne, hu, hu'⟩

theorem twoUpOK_of_k (h : UpperTheory.TP.TLiftK) : TwoUpOK := twoUpOK_of_steps h Chr.chrPairs_holds upOf baseNG

end UpperTheory.Gal.TP
