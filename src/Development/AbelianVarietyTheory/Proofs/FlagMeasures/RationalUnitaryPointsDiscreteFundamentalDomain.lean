module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RepresentationIndependence.FrameOKMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNilpotentAlgebraIsotropicFlagUnipotentRadi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLevi

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open Matrix Topology Filter
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RatDiscrete

theorem finite_bounded {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) (B : ℝ) :
    {x : n → E | x ∈ Λ ∧ ∀ (τ : E →+* ℂ) i, ‖τ (x i)‖ ≤ B}.Finite := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  have hm' : (m : E) ≠ 0 := Int.cast_ne_zero.2 hm0
  have h1 := (NumberField.Embeddings.finite_of_norm_le E ℂ (‖(m : ℂ)‖ * B)).preimage
    (f := fun a : E => (m : E) * a) (mul_right_injective₀ hm').injOn
  refine (Set.Finite.pi' fun _ : n => h1).subset fun x hx i => ⟨hΛ x hx.1 i, fun τ => ?_⟩
  simp only [map_mul, map_intCast, norm_mul]
  exact mul_le_mul_of_nonneg_left (hx.2 τ i) (norm_nonneg _)

variable (I : AutInst)

theorem exists_place (τ : I.E →+* ℂ) : ∃ v, ∀ a, ‖τ a‖ = ‖I.φ v a‖ := by
  haveI := I.cm.totReal
  let ψ : I.F →+* ℂ := τ.comp (algebraMap I.F I.E)
  have hψ : ComplexEmbedding.IsReal ψ :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk ψ))
  refine ⟨InfinitePlace.mk ψ, fun a => ?_⟩
  obtain ⟨b, hb⟩ := (I.cm.fixed (a * star a)).1 (by rw [star_mul, star_star])
  have h1 : τ (a * star a) = I.φ (InfinitePlace.mk ψ) (a * star a) := by
    rw [← hb, I.φ_over, InfinitePlace.embedding_mk_eq_of_isReal hψ]
    rfl
  have h2 := congrArg norm h1
  simp only [map_mul, I.cm.cmUnram.2.1, norm_mul, Complex.norm_conj] at h2
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 h2

def IsImage (γ : Matrix (Fin I.n) (Fin I.n) I.E) (x : I.GA) : Prop :=
  (∀ v, uMat (x.1 v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v) ∧
    I.fmat x.2 = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))

theorem subsingleton_isImage (γ : Matrix (Fin I.n) (Fin I.n) I.E) :
    {x | IsImage I γ x}.Subsingleton := fun _ hx _ hy =>
  Prod.ext (funext fun v => Subtype.ext (Units.ext ((hx.1 v).trans (hy.1 v).symm)))
    (Subtype.ext (Units.ext (hx.2.trans hy.2.symm)))

theorem P_det (v) : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)

theorem isImage_one : IsImage I 1 1 := by
  refine ⟨fun v => ?_, ?_⟩
  · rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ (P_det I v)]
    rfl
  · rw [Matrix.map_one _ (map_zero _) (map_one _)]
    rfl

theorem isImage_mul {γ δ x y} (hx : IsImage I γ x) (hy : IsImage I δ y) :
    IsImage I (γ * δ) (x * y) := by
  refine ⟨fun v => ?_, ?_⟩
  · have : uMat ((x * y).1 v) = uMat (x.1 v) * uMat (y.1 v) := rfl
    rw [this, hx.1, hy.1, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v)]
  · have : I.fmat (x * y).2 = I.fmat x.2 * I.fmat y.2 := rfl
    rw [this, hx.2, hy.2, Matrix.map_mul]

theorem isImage_inv {γ : GL (Fin I.n) I.E} {x} (hx : IsImage I γ x) :
    IsImage I (γ⁻¹ : GL (Fin I.n) I.E) x⁻¹ := by
  refine ⟨fun v => ?_, ?_⟩
  · refine Units.inv_eq_of_mul_eq_one_right (u := (x.1 v : (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ)) ?_
    have := hx.1 v
    unfold uMat at this
    rw [this]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v)]
    rw [← Matrix.mul_assoc (Matrix.map _ _), ← Matrix.map_mul, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.nonsing_inv_mul _ (P_det I v)]
  · refine Units.inv_eq_of_mul_eq_one_right (u := (x.2 : GL (Fin I.n) (I.E ⊗[I.F] Af I.F))) ?_
    have := hx.2
    unfold AutInst.fmat at this
    rw [this, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

def ratSub : Subgroup I.GA where
  carrier := I.GFset
  one_mem' := ⟨1, one_mem _, isImage_one I⟩
  mul_mem' := fun ⟨γ, hγ, hx⟩ ⟨δ, hδ, hy⟩ => ⟨γ * δ, mul_mem hγ hδ, isImage_mul I hx hy⟩
  inv_mem' := fun ⟨γ, hγ, hx⟩ => ⟨γ⁻¹, inv_mem hγ, isImage_inv I hx⟩

theorem countable_GFset : I.GFset.Countable := by
  haveI : Countable I.E := Countable.of_equiv _ (Module.finBasis ℚ I.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin I.n) (Fin I.n) I.E) :=
    inferInstanceAs (Countable (Fin I.n → Fin I.n → I.E))
  refine (Set.countable_iUnion fun γ => (subsingleton_isImage I γ).countable).mono ?_
  rintro x ⟨γ, -, hx⟩
  exact Set.mem_iUnion.2 ⟨γ, hx⟩

theorem exists_bound {C : Set I.GA} (hC : IsCompact C) : ∃ B : ℝ, ∀ x ∈ C, ∀ v i j,
    ‖(I.P v * uMat (x.1 v) * (I.P v)⁻¹) i j‖ ≤ B := by
  have hc : Continuous fun x : I.GA => fun v i j => (I.P v * uMat (x.1 v) * (I.P v)⁻¹) i j := by
    refine continuous_pi fun v => ?_
    exact (continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp
      ((continuous_apply v).comp continuous_fst)))).matrix_mul continuous_const
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨B, fun x hx v i j => (norm_le_pi_norm _ j).trans ((norm_le_pi_norm _ i).trans
    ((norm_le_pi_norm _ v).trans (hB x hx)))⟩

theorem finite_coset (g : I.Gf) (B : ℝ) :
    {γ : Matrix (Fin I.n) (Fin I.n) I.E | (∀ v i j, ‖I.φ v (γ i j)‖ ≤ B) ∧
      ∃ y : I.Gf, g⁻¹ * y ∈ I.Kset ∧ I.fmat y = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))}.Finite := by
  classical
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  obtain ⟨c, hc0, hlow⟩ := Formalism.UG.P.adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨d, hd0, hup⟩ := Formalism.UG.P.adelstabL_upper (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
  rw [← hL] at hlow hup
  set G : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := g.1 with hGdef
  obtain ⟨e, he, s, hs, hsg, -⟩ := Formalism.UG.P.levelaf_exists_denom (E := I.E) G
  have hfin := Formalism.UG.P.adelstab_finite G I.Lf d e hd0 he hup (Formalism.UG.P.adelstab_entries G e s hs hsg)
  set u : I.E := algebraMap (𝓞 I.F) I.E c with hu
  have hu0 : u ≠ 0 := Formalism.UG.P.adelstab_algebraMap_ne_zero c hc0
  obtain ⟨Bu, hBu⟩ : ∃ Bu : ℝ, ∀ τ : I.E →+* ℂ, ‖τ u‖ ≤ Bu :=
    ⟨_, fun τ => Finite.le_ciSup (fun τ : I.E →+* ℂ => ‖τ u‖) τ⟩
  have h1 := (Set.Finite.pi' fun _ : Fin I.n => finite_bounded _ hfin (Bu * B)).preimage
    (f := fun (γ : Matrix (Fin I.n) (Fin I.n) I.E) j i => u * γ i j) (by
      intro a _ b _ h
      ext i j
      exact mul_left_cancel₀ hu0 (congrFun (congrFun h j) i))
  refine h1.subset ?_
  rintro γ ⟨hb, y, hy, hγ⟩ j
  refine ⟨?_, fun τ i => ?_⟩
  · have hs : (Pi.single j (Formalism.UG.P.levelafC I.E c) : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ I.Lf := by
      convert hlow (Pi.single j 1) fun i => ?_ using 1
      · funext i
        by_cases h : i = j <;> simp [h]
      · rw [Pi.single_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
    have h2 := (hy _).1 hs
    rw [Formalism.UG.P.adelstab_mem_iff]
    convert h2 using 1
    change _ = (((G⁻¹ : GL _ _) : Matrix _ _ _) * I.fmat y) *ᵥ _
    rw [← Matrix.mulVec_mulVec, hγ]
    congr 1
    funext i
    simp [hu, Formalism.UG.P.adelstab_incl_C, mul_comm]
  · obtain ⟨v, hv⟩ := exists_place I τ
    simp only [map_mul, norm_mul]
    rw [hv (γ i j)]
    exact mul_le_mul (hBu τ) (hb v i j) (norm_nonneg _) ((norm_nonneg _).trans (hBu τ))

theorem finite_inter {C : Set I.GA} (hC : IsCompact C) : (C ∩ I.GFset).Finite := by
  obtain ⟨-, -, -, -, hKo, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨B, hB⟩ := exists_bound I hC
  obtain ⟨t, -, ht⟩ := (hC.image continuous_snd).elim_nhds_subcover
    (fun g => {y | g⁻¹ * y ∈ I.Kset}) fun g _ =>
      (hKo.preimage (continuous_const.mul continuous_id)).mem_nhds (by
        show g⁻¹ * g ∈ I.Kset
        rw [inv_mul_cancel, ← hK]
        exact K.one_mem)
  refine ((t.finite_toSet.biUnion fun g _ => finite_coset I g B).biUnion
    fun γ _ => (subsingleton_isImage I γ).finite).subset ?_
  rintro x ⟨hx, γ, -, hγ⟩
  obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 (ht ⟨x, hx, rfl⟩)
  refine Set.mem_iUnion₂.2 ⟨γ, Set.mem_iUnion₂.2 ⟨g, hg, fun v i j => ?_, x.2, hgx, hγ.2⟩, hγ⟩
  have := hB x hx v i j
  rw [hγ.1 v] at this
  simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (P_det I v),
    Matrix.mul_nonsing_inv _ (P_det I v), Matrix.mul_one, Matrix.map_apply] using this

theorem isFundamentalDomain (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (h : I.IsFundDom (I.muA μf) fund) : IsFundamentalDomain (ratSub I) fund (I.muA μf) := by
  refine IsFundamentalDomain.mk'' h.1.nullMeasurableSet (ae_of_all _ fun y => ?_) (fun γ hγ => ?_)
    fun γ => ((measurePreserving_mul_left (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) (γ : I.GA).1).prod
      (measurePreserving_mul_left μf (γ : I.GA).2)).quasiMeasurePreserving
  · obtain ⟨γ, hγ, hy⟩ := h.2.1 y
    exact ⟨⟨γ, hγ⟩, hy⟩
  · exact h.2.2 γ γ.2 fun e => hγ (Subtype.ext e)

theorem rational_points : ∀ I : AutInst, ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ Countable Γ ∧ (∀ C : Set I.GA, IsCompact C → (C ∩ I.GFset).Finite) ∧ ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → IsFundamentalDomain Γ fund (I.muA μf) :=
  fun I => ⟨ratSub I, rfl, (countable_GFset I).to_subtype, fun _ hC => finite_inter I hC,
    fun μf _ _ fund h => isFundamentalDomain I μf fund h⟩

end GlobalTheory.RatDiscrete
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomainStatement
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain : ∀ I : AutInst, ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ Countable Γ ∧ (∀ C : Set I.GA, IsCompact C → (C ∩ I.GFset).Finite) ∧ ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → IsFundamentalDomain Γ fund (I.muA μf) := by
  first | exact @GlobalTheory.RatDiscrete.rational_points | exact GlobalTheory.RatDiscrete.rational_points | (intros; apply GlobalTheory.RatDiscrete.rational_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
open Formalism.UG.P

namespace GlobalTheory.St.G.IntAd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem levelafC_natCast (m : ℕ) : levelafC (F := F) E (m : 𝓞 F) = (m : E ⊗[F] Ad F) := by
  induction m with
  | zero => simp only [levelafC, Nat.cast_zero, map_zero, TensorProduct.tmul_zero]
  | succ k ih =>
    simp only [levelafC] at ih ⊢
    rw [Nat.cast_succ, Nat.cast_succ, map_add (f := _), map_one, TensorProduct.tmul_add, ih,
      Algebra.TensorProduct.one_def]

private theorem sum_afsplitI_one_apply_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∈ S) : (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w = 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w =
      ∑ v ∈ S, (afsplitI v (1 : v.adicCompletion F)) w from map_sum (evalV F w) _ S]
  rw [Finset.sum_eq_single_of_mem w hw (fun v _ hv => afsplitI_ne v w (Ne.symm hv) 1),
    afsplitI_self]

private theorem sum_afsplitI_one_apply_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F))
    (hw : w ∉ S) : (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (∑ v ∈ S, afsplitI v (1 : v.adicCompletion F)) w =
      ∑ v ∈ S, (afsplitI v (1 : v.adicCompletion F)) w from map_sum (evalV F w) _ S]
  exact Finset.sum_eq_zero (fun v hv => afsplitI_ne v w (fun h => hw (by rw [h]; exact hv)) 1)

theorem mem_of_local (a : E ⊗[F] Ad F)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) : a ∈ OAd F E := by
  classical
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) a
  have hfin := levelaf_finite_places (F := F) d hd0
  set S := hfin.toFinset with hS
  set dF : F := algebraMap (𝓞 F) F d with hdF
  have hdF0 : dF ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  set s : Ad F := ∑ v ∈ S, afsplitI v (1 : v.adicCompletion F) with hs
  set u : Ad F := (1 - s) * algebraMap F (Ad F) dF⁻¹ with hu
  have hu_int : u ∈ intAd F := by
    show ∀ w : HeightOneSpectrum (𝓞 F), u w ∈ w.adicCompletionIntegers F
    intro w
    have hcomp : u w = (1 - s w) * (dF⁻¹ • (1 : w.adicCompletion F)) := by
      rw [hu, afsplit_mul_apply, afsplit_sub_apply, afsplit_one_apply,
        Algebra.algebraMap_eq_smul_one, afsplit_smul_apply, afsplit_one_apply]
    by_cases hw : w ∈ S
    · rw [hcomp, hs, sum_afsplitI_one_apply_of_mem S w hw, sub_self, zero_mul]
      exact zero_mem _
    · rw [hcomp, hs, sum_afsplitI_one_apply_of_not_mem S w hw, sub_zero, one_mul, Algebra.smul_def, mul_one, map_inv₀,
        HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀]
      have h1 := levelaf_int_mem_v w d
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      have h2 : ¬ Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) d) < 1 :=
        fun hlt => hw (hfin.mem_toFinset.mpr hlt)
      have h3 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) d) = 1 :=
        le_antisymm h1 (not_lt.mp h2)
      rw [hdF, ← IsScalarTower.algebraMap_apply, h3, inv_one]
  have he : ∑ v ∈ S, afsplitEps E v = (1 : E) ⊗ₜ[F] s := by
    rw [hs, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  have h1 : (1 : E ⊗[F] Ad F) - ∑ v ∈ S, afsplitEps E v = ((1 : E) ⊗ₜ[F] u) * levelafC E d := by
    rw [he, levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hu, mul_assoc,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Ad F) d, ← hdF, ← map_mul, inv_mul_cancel₀ hdF0,
      map_one, mul_one, TensorProduct.tmul_sub, ← Algebra.TensorProduct.one_def]
  have hsplit : a = (∑ v ∈ S, afsplitEps E v) * a + ((1 : E) ⊗ₜ[F] u) * (levelafC E d * a) := by
    rw [← mul_assoc, ← h1]
    ring
  rw [hsplit]
  refine add_mem ?_ (mul_mem ?_ hd)
  · rw [Finset.sum_mul]
    refine sum_mem (fun v _ => ?_)
    rw [← afsplit_decomp]
    exact afsplit_IE_int v _ (h v)
  · have hmem := levelaf_tmul_mem (E := E) (1 : 𝓞 E) hu_int
    rwa [map_one] at hmem

theorem expand_trace {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E)
    (a : E ⊗[F] Ad F) :
    a = ∑ i, ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β i) ⊗ₜ[F]
      adelstabT F E (inclE (F := F) (Ad F) (β i) * a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero]
  | tmul e y =>
    have hT : ∀ i, adelstabT F E (inclE (F := F) (Ad F) (β i) * (e ⊗ₜ[F] y)) =
        Algebra.trace F E (e * β i) • y := by
      intro i
      rw [inclE, Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, adelstabT_tmul, Algebra.smul_def, mul_comm (β i) e]
    simp_rw [hT, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    conv_lhs => rw [← ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β).sum_repr e]
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_add, map_add (f := _), TensorProduct.tmul_add]

private theorem adelstabT_inclE_of_forall_divisible (a : E ⊗[F] Ad F)
    (h : ∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) (e : E) :
    adelstabT F E (inclE (F := F) (Ad F) e * a) = 0 := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) (inclE (F := F) (Ad F) e)
  have hxS : inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) ∈ OAd F E := by
    rw [map_mul, adelstab_incl_C]
    exact hd
  have hzero : adelstabT F E (inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * a) = 0 := by
    refine GlobalTheory.IntegralFinAdele.eq_zero_of_forall_mul F _ (fun M hM => ?_)
    obtain ⟨t, ht, hat⟩ := h M hM
    refine ⟨adelstabT F E (inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * t),
      adelstabT_mem (mul_mem hxS ht), ?_⟩
    rw [hat, mul_left_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have hdF0 : algebraMap (𝓞 F) F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hxe : inclE (F := F) (Ad F) (algebraMap (𝓞 F) E d * e) * a =
      algebraMap (𝓞 F) F d • (inclE (F := F) (Ad F) e * a) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E d, ← Algebra.smul_def, inclE,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
      ← TensorProduct.smul_tmul', smul_mul_assoc]
  rw [hxe, map_smul] at hzero
  calc adelstabT F E (inclE (F := F) (Ad F) e * a)
      = (algebraMap (𝓞 F) F d)⁻¹ • algebraMap (𝓞 F) F d • adelstabT F E (inclE (F := F) (Ad F) e * a) :=
        (inv_smul_smul₀ hdF0 _).symm
    _ = 0 := by rw [hzero, smul_zero]

theorem eq_zero_of_multiples (a : E ⊗[F] Ad F)
    (h : ∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) : a = 0 := by
  classical
  rw [expand_trace (Module.Free.chooseBasis F E) a]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [adelstabT_inclE_of_forall_divisible a h, TensorProduct.tmul_zero]

theorem exists_nat_denom (a : E ⊗[F] Ad F) :
    ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E := by
  obtain ⟨d, hd0, hd⟩ := levelaf_denom (E := E) a
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), Nat.pos_of_ne_zero ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  · rw [← levelafC_natCast, hq, levelafC_mul, mul_comm (levelafC E d), mul_assoc]
    exact mul_mem (levelafC_mem q) hd

theorem integral_adeles_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ a : E ⊗[F] Ad F, a ∈ OAd F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) ∧ (∀ a ∈ OAd F E, ∀ m : ℕ, 0 < m → ∃ x : 𝓞 E, ∃ t ∈ OAd F E, a = inclE (F := F) (Ad F) (x : E) + (m : E ⊗[F] Ad F) * t) ∧ (∀ a : E ⊗[F] Ad F, (∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) → a = 0) ∧ (∀ a : E ⊗[F] Ad F, ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E) ∧ (∀ x : E, inclE (F := F) (Ad F) x ∈ OAd F E ↔ x ∈ intOE E) := by
  intro F E _ _ _ _ _
  refine ⟨fun a => ⟨fun ha v => afsplit_prV_int v a ha, mem_of_local a⟩, ?_,
    fun a => eq_zero_of_multiples a, exists_nat_denom, fun x => ⟨?_, ?_⟩⟩
  · intro a ha m hm
    have hm' : (m : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    obtain ⟨b, t, ht, hab⟩ := csGlob_approx (E := E) csGlob_intAdApprox (m : 𝓞 F) hm' a ha
    refine ⟨b, t, ht, ?_⟩
    rw [hab, levelafC_natCast]
    try rfl
  · intro hx
    exact ⟨⟨x, csGlob_int x hx⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact adelstab_incl_int b

end GlobalTheory.St.G.IntAd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicPropertiesStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ a : E ⊗[F] Ad F, a ∈ OAd F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) ∧ (∀ a ∈ OAd F E, ∀ m : ℕ, 0 < m → ∃ x : 𝓞 E, ∃ t ∈ OAd F E, a = inclE (F := F) (Ad F) (x : E) + (m : E ⊗[F] Ad F) * t) ∧ (∀ a : E ⊗[F] Ad F, (∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) → a = 0) ∧ (∀ a : E ⊗[F] Ad F, ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E) ∧ (∀ x : E, inclE (F := F) (Ad F) x ∈ OAd F E ↔ x ∈ intOE E) := by
  first | exact @GlobalTheory.St.G.IntAd.integral_adeles_properties | exact GlobalTheory.St.G.IntAd.integral_adeles_properties | (intros; apply GlobalTheory.St.G.IntAd.integral_adeles_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem adelicStab_isCompact_isOpen :
    ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  intro I
  obtain ⟨h1, h2, -, h4, h5, -⟩ := GlobalTheory.CongTop.adelic_topology I
  exact ⟨h4, h5, h2, h1⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpenStatement
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen : ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  first | exact @GlobalTheory.adelicStab_isCompact_isOpen | exact GlobalTheory.adelicStab_isCompact_isOpen | (intros; apply GlobalTheory.adelicStab_isCompact_isOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPoints
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem secondCountable_finiteAdelicPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf :=
  fun I => (adelic_topology I).2.2.1

end GlobalTheory.CongTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPointsStatement
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf := by
  first | exact @GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | exact GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | (intros; apply GlobalTheory.CongTop.secondCountable_finiteAdelicPoints <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  have := rank_base_space D.R
  simp only [Ranks.N, zero_mul, add_zero] at this
  omega

variable {D : D7} (X : HidaSetting D)

def ci : Fin (2 * D.R.rS + D.R.k + 1) ≃ Fin X.B.I.n := finCongr (X.n_eq.trans (rank_eq D)).symm

def crdH (y : (VS D).V) : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E := fun i => X.bas.repr y (ci X i)

def vecOf : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).toLinearMap

def Jc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E :=
  fun i j => (VS D).hT (X.bas (ci X i)) (X.bas (ci X j))

def Lc : Submodule (𝓞 D.host.E) (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :=
  (VS D).L0.comap ((vecOf X).restrictScalars (𝓞 D.host.E))

def Pc (u : D.what₂.Word) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (D.R.rS + 1)) D.host.E :=
  Matrix.of fun i b => Fin.lastCases (crdH X (X.zu u) i) (fun a => crdH X (X.eX a) i) b

def fc : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin D.R.rS) D.host.E :=
  Matrix.of fun i a => crdH X (X.fY a) i

def Tc (u : D.what₂.Word) : D.host.F := (((D.mem u).A.T : ℕ) : D.host.F)

def tauOf (D : D7) (w : InfinitePlace D.host.E) : D.what₂.Tau :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose

def Direct (D : D7) (w : InfinitePlace D.host.E) : Prop := w.embedding = embS D (tauOf D w)

def A0 {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  (C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹).submatrix id (ci X)

def Ac {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  if Direct D w then A0 X C w else (A0 X C w).map star

def sc (D : D7) (a : Fin D.R.rS) : ℝ := (2 * D.host.v) ^ (D.R.rS - (a : ℕ))

def trX {θ : ℝ} (C : Choice X θ) (x : X.B.I.Ginf) : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun τ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ)))

def cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then M else fun i j => star (M i j)

def Gm (D : D7) (y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  fun w => cjw D w (y (tauOf D w))

end GlobalTheory.CovDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitary
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.CongTop

theorem exists_haar_sigmaFinite :
    ∀ (I : AutInst), ∃ μf : Measure I.Gf, μf.IsHaarMeasure ∧ SigmaFinite μf := by
  intro I
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  exact ⟨Measure.haar, inferInstance, inferInstance⟩

end GlobalTheory.CongTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteHaarFiniteAdelicUnitaryStatement
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sigmaFinite_haar_finiteAdelicUnitary : ∀ (I : AutInst), ∃ μf : Measure I.Gf, μf.IsHaarMeasure ∧ SigmaFinite μf := by
  first | exact @GlobalTheory.CongTop.exists_haar_sigmaFinite | exact GlobalTheory.CongTop.exists_haar_sigmaFinite | (intros; apply GlobalTheory.CongTop.exists_haar_sigmaFinite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometry
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameIsom

theorem frameOK_mapLF : ∀ (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
    ∀ (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂ →
    ∀ (T : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T), FrameOK D Λ₁ F → FrameOK D Λ₂ (mapLF γ F) := by
  intro D γ hγ Λ₁ Λ₂ hΛ T F hF
  subst hΛ
  have e : mapLF γ F = PI.RepsIndep.Tr.mapL γ hγ F := by
    unfold mapLF
    rw [dite_eq_left hγ]
    rfl
  rw [e]
  exact PI.RepsIndep.Tr.FrameOK_map hγ hF

end GlobalTheory.FrameIsom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometryStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralRowFrame_map_isometry : ∀ (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ∀ (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂ → ∀ (T : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T), FrameOK D Λ₁ F → FrameOK D Λ₂ (mapLF γ F) := by
  first | exact @GlobalTheory.FrameIsom.frameOK_mapLF | exact GlobalTheory.FrameIsom.frameOK_mapLF | (intros; apply GlobalTheory.FrameIsom.frameOK_mapLF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolic
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolic
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem gaugeSubEx_mem_maxK_iff {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    g ∈ maxK ε ↔ g ∈ Formalism.REAL.KG ε := by
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  constructor
  · intro h
    have h1 : (uMat g)ᴴ * uMat g = 1 := h
    have h2 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp h1
    refine ⟨Matrix.mem_unitaryGroup_iff'.mpr h1, ?_⟩
    show uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g
    calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hg]
      _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.one_mul]
  · intro h
    exact Matrix.mem_unitaryGroup_iff'.mp h.1

theorem gaugeSubEx_haarK (n : ℕ) (ε : Fin n → Bool) :
    ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧
      ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  have hK : maxK ε = (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) :=
    Set.ext fun g => gaugeSubEx_mem_maxK_iff ε g
  have hc : IsCompact (Formalism.REAL.KG ε : Set (Formalism.REAL.UJ ε)) :=
    isCompact_iff_compactSpace.mpr (Formalism.REAL.instCompactKG n ε)
  have hm : MeasurableSet (maxK ε) := hK ▸ hc.isClosed.measurableSet
  have hv : Measurable (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) := measurable_subtype_coe
  have := Formalism.REAL.compact_haar_probability n ε
  refine ⟨(Formalism.REAL.muK ε).map Subtype.val, ?_, ?_, ?_⟩
  · rw [Measure.map_apply hv hm.compl]
    have : (Subtype.val : Formalism.REAL.KG ε → Formalism.REAL.UJ ε) ⁻¹' (maxK ε)ᶜ = ∅ := by
      ext k
      simp [hK]
    rw [this, measure_empty]
  · rw [Measure.map_apply hv MeasurableSet.univ, Set.preimage_univ, measure_univ]
  · intro k hk
    have hk' : k ∈ Formalism.REAL.KG ε := (gaugeSubEx_mem_maxK_iff ε k).mp hk
    have h := map_mul_left_eq_self (Formalism.REAL.muK ε) ⟨k, hk'⟩
    rw [Measure.map_map (measurable_const_mul k) hv]
    conv_rhs => rw [← h]
    rw [Measure.map_map hv (measurable_const_mul _)]
    rfl

theorem gaugeSubEx : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagN ε W) (dimN n j) μ) ∧ (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μ) ∧ ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧ ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  intro n ε a j W _ hW
  refine ⟨?_, ?_, gaugeSubEx_haarK n ε⟩
  · obtain ⟨A, E, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_nilpotentAlgebra_isotropicFlagUnipotentRadical n ε a j W hW
    rw [h4]
    exact GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε A _ E h1 h2 h3
  · obtain ⟨A, E, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_algebra_isotropicFlagSelfAdjointLevi n ε a j W hW
    rw [h4]
    exact GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra n ε A _ E h1 h2 h3

end GlobalTheory.FlagMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGaugeMeasuresIsotropicFlagParabolicStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gauge_measures_isotropicFlag_parabolic : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∀ i, 1 ≤ j i) → IsIsoFlag ε j W → (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagN ε W) (dimN n j) μ) ∧ (∃ μ, SigmaFinite μ ∧ IsGaugeSub (flagM ε W) ((n - 2 * ∑ i, j i) ^ 2 + 2 * ∑ i, j i ^ 2) μ) ∧ ∃ μ : Measure (Formalism.REAL.UJ ε), μ (maxK ε)ᶜ = 0 ∧ μ Set.univ = 1 ∧ ∀ k ∈ maxK ε, μ.map (fun g => k * g) = μ := by
  first | exact @GlobalTheory.FlagMeas.gaugeSubEx | exact GlobalTheory.FlagMeas.gaugeSubEx | (intros; apply GlobalTheory.FlagMeas.gaugeSubEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureLeCardMul
open MeasureTheory Formalism.MainNotions.S NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongIndex

theorem measure_le_card_mul {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [Finite Q] (K H : Set G) (q : K → Q)
    (hq : ∀ x y : K, q x = q y → (y : G)⁻¹ * x ∈ H) : μ K ≤ (Nat.card Q : ENNReal) * μ H := by
  classical
  haveI := Fintype.ofFinite Q
  have h1 : K ⊆ ⋃ c : Q, Subtype.val '' (q ⁻¹' {c}) := fun x hx =>
    Set.mem_iUnion.2 ⟨q ⟨x, hx⟩, ⟨x, hx⟩, rfl, rfl⟩
  have h2 : ∀ c : Q, μ (Subtype.val '' (q ⁻¹' {c})) ≤ μ H := by
    intro c
    by_cases h : ∃ y, q y = c
    · obtain ⟨y, rfl⟩ := h
      rw [← measure_preimage_mul μ (y : G)⁻¹ H]
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hq x y hx
    · have : q ⁻¹' {c} = ∅ := Set.eq_empty_of_forall_notMem fun y hy => h ⟨y, hy⟩
      simp [this]
  calc μ K ≤ ∑ c : Q, μ (Subtype.val '' (q ⁻¹' {c})) :=
        (measure_mono h1).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _c : Q, μ H := Finset.sum_le_sum fun c _ => h2 c
    _ = _ := by simp [Nat.card_eq_fintype_card]

section Lift

variable {O A L n : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype n] [DecidableEq n]
  [AddCommGroup L] [Module O L] (S : Subring A) (ι : L →ₗ[O] (n → A)) (a : A)

theorem exists_approx (hO : ∀ o : O, algebraMap O A o ∈ S)
    (hS : ∀ s ∈ S, ∃ o : O, ∃ w ∈ S, s = algebraMap O A o + a * w) (ha : a ∈ S)
    {y : n → A} (hy : y ∈ Submodule.span S (Set.range ι)) :
    ∃ l : L, ∃ z ∈ Submodule.span S (Set.range ι), y = ι l + a • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    exact ⟨l, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, z, hz, rfl⟩ := hx
    obtain ⟨l', z', hz', rfl⟩ := hy
    exact ⟨l + l', z + z', add_mem hz hz', by rw [map_add (f := _), smul_add]; abel⟩
  | smul s x _ hx =>
    obtain ⟨l, z, hz, rfl⟩ := hx
    obtain ⟨o, w, hw, e⟩ := hS s s.2
    refine ⟨o • l, (⟨w, hw⟩ : S) • ι l + s • z,
      add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)) (Submodule.smul_mem _ _ hz), ?_⟩
    rw [map_smul, ← algebraMap_smul A o]
    simp only [Subring.smul_def, smul_add, smul_smul]
    rw [e, add_smul, mul_comm a (_ + _), add_assoc]

theorem exists_end [Module.Projective O L] (hO : ∀ o : O, algebraMap O A o ∈ S)
    (hS : ∀ s ∈ S, ∃ o : O, ∃ w ∈ S, s = algebraMap O A o + a * w) (ha : a ∈ S)
    (x : Matrix n n A) (hx : ∀ y ∈ Submodule.span S (Set.range ι), x *ᵥ y ∈ Submodule.span S (Set.range ι)) :
    ∃ φ : L →ₗ[O] L, ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), x *ᵥ ι l = ι (φ l) + a • z := by
  let N : Submodule O (n → A) :=
    { carrier := {w | ∃ z ∈ Submodule.span S (Set.range ι), w = a • z}
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
        exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro o _ ⟨z, hz, rfl⟩
        refine ⟨(⟨_, hO o⟩ : S) • z, Submodule.smul_mem _ _ hz, ?_⟩
        rw [Subring.smul_def, smul_comm a, algebraMap_smul] }
  let f : L →ₗ[O] ((n → A) ⧸ N) := N.mkQ ∘ₗ ι
  let h : L →ₗ[O] ((n → A) ⧸ N) := N.mkQ ∘ₗ (Matrix.mulVecLin x).restrictScalars O ∘ₗ ι
  have hh : ∀ l, h l ∈ LinearMap.range f := by
    intro l
    obtain ⟨l', z, hz, e⟩ := exists_approx S ι a hO hS ha (hx _ (Submodule.subset_span ⟨l, rfl⟩))
    refine ⟨l', ((Submodule.Quotient.eq N).2 ⟨z, hz, ?_⟩).symm⟩
    exact sub_eq_of_eq_add' e
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property f.rangeRestrict (h.codRestrict _ hh)
    f.surjective_rangeRestrict
  refine ⟨φ, fun l => ?_⟩
  have e : f (φ l) = h l := congrArg Subtype.val (LinearMap.congr_fun hφ l)
  obtain ⟨z, hz, e'⟩ := (Submodule.Quotient.eq N).1 e.symm
  exact ⟨z, hz, eq_add_of_sub_eq' e'⟩

theorem congr_of_end (g : ℕ) (x y : GL n A)
    (hx : x ∈ Formalism.UG.stabGL (Submodule.span S (Set.range ι)))
    (hy : y ∈ Formalism.UG.stabGL (Submodule.span S (Set.range ι))) (φ ψ θ : L →ₗ[O] L)
    (hφ : ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), (x : Matrix n n A) *ᵥ ι l = ι (φ l) + (g : A) • z)
    (hψ : ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), (y : Matrix n n A) *ᵥ ι l = ι (ψ l) + (g : A) • z)
    (hθ : φ = ψ + g • θ) :
    y⁻¹ * x ∈ GlobalTheory.CongTop.cong (Submodule.span S (Set.range ι)) (g : A) := by
  refine ⟨mul_mem (inv_mem hy) hx, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, rfl⟩ := hv
    obtain ⟨z, hz, e⟩ := hφ l
    obtain ⟨z', hz', e'⟩ := hψ l
    refine ⟨((y⁻¹ : GL n A) : Matrix n n A) *ᵥ (ι (θ l) + z - z'),
      (inv_mem hy _).1 (sub_mem (add_mem (Submodule.subset_span ⟨_, rfl⟩) hz) hz'), ?_⟩
    have e2 : (x : Matrix n n A) *ᵥ ι l - (y : Matrix n n A) *ᵥ ι l = (g : A) • (ι (θ l) + z - z') := by
      rw [e, e', hθ, LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_nsmul,
        ← Nat.cast_smul_eq_nsmul A, smul_sub, smul_add]
      abel
    rw [← Matrix.mulVec_smul, ← e2, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Units.inv_mul, Units.val_mul, Matrix.sub_mulVec]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨z, hz, e⟩ := hv
    obtain ⟨z', hz', e'⟩ := hw
    exact ⟨z + z', add_mem hz hz', by rw [Matrix.mulVec_add, e, e', smul_add]⟩
  | smul s v _ hv =>
    obtain ⟨z, hz, e⟩ := hv
    refine ⟨s • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, Matrix.mulVec_smul, e, smul_comm]

end Lift

section Rank

variable {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

theorem exists_inj (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ m ≤ n, ∃ e : (L →ₗ[𝓞 E] L) →ₗ[ℤ] (Fin m → Fin n → E), Function.Injective e := by
  obtain ⟨b, hbL, hb, hli⟩ := exists_linearIndependent E (L : Set (Fin n → E))
  haveI : Finite b := hli.finite
  haveI := Fintype.ofFinite b
  have hc : Fintype.card b ≤ n := by simpa using hli.fintype_card_le_finrank
  let u := (Fintype.equivFin b).symm
  let e : (L →ₗ[𝓞 E] L) →+ (Fin (Fintype.card b) → Fin n → E) :=
    { toFun := fun φ i => (φ ⟨u i, hbL (u i).2⟩ : L)
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  refine ⟨_, hc, e.toIntLinearMap, (injective_iff_map_eq_zero e).2 fun φ hφ => ?_⟩
  ext1 l
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E b (l : Fin n → E)
    (by rw [hb, hL]; trivial)
  have hle : Submodule.span (𝓞 E) b ≤ (LinearMap.ker φ).map L.subtype := by
    refine Submodule.span_le.2 fun w hw => ⟨⟨w, hbL hw⟩, ?_, rfl⟩
    have := congrFun hφ (u.symm ⟨w, hw⟩)
    simpa [e] using this
  obtain ⟨l', hl', e'⟩ := hle ht
  have e2 : l' = (t : 𝓞 E) • l := Subtype.ext e'
  rw [e2, SetLike.mem_coe, LinearMap.mem_ker, map_smul, smul_eq_zero] at hl'
  exact hl'.resolve_left (nonZeroDivisors.ne_zero t.2)

theorem card_end_quot (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (g : ℕ) :
    ∃ r ≤ n ^ 2 * Module.finrank ℚ E,
      (nsmulAddMonoidHom (α := L →ₗ[𝓞 E] L) g).range.index = g ^ r := by
  obtain ⟨m, hm, e, he⟩ := exists_inj L hL
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  haveI : IsNoetherian (𝓞 E) L := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian (𝓞 E) (L →ₗ[𝓞 E] L) := isNoetherian_linearMap _ _ _
  haveI : Module.Finite (𝓞 E) (L →ₗ[𝓞 E] L) := Module.IsNoetherian.finite _ _
  haveI : Module.Finite ℤ (L →ₗ[𝓞 E] L) := Module.Finite.trans (𝓞 E) _
  haveI : Module.IsTorsionFree ℤ (L →ₗ[𝓞 E] L) := he.moduleIsTorsionFree e e.map_smul
  refine ⟨_, ?_, AddSubgroup.index_range_nsmul _ g⟩
  have h1 := e.rank_le_of_injective he
  rw [← IsFractionRing.rank_right_eq ℤ ℚ (Fin m → Fin n → E), ← Module.finrank_eq_rank,
    ← Module.finrank_eq_rank, Nat.cast_le] at h1
  refine h1.trans ?_
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, sq]
  gcongr

end Rank

theorem measure_Kset_le : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] (g : ℕ), 1 ≤ g → μf I.Kset ≤ (g : ENNReal) ^ (2 * (I.n ^ 2 * I.f)) * μf (I.Kg g) ∧ 0 < μf (I.Kg g) ∧ μf I.Kset < ⊤ := by
  intro I μf _ g hg
  obtain ⟨-, -, hsc, hc, -, -, h⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨ho, ⟨H, hH⟩, -⟩ := h g hg
  refine ⟨?_, ho.measure_pos μf ⟨1, hH ▸ H.one_mem⟩, hc.measure_lt_top⟩
  haveI : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.2 I.L_fg
  haveI : Module.FinitePresentation (𝓞 I.E) I.L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 I.E) I.L := Module.Flat.projective_of_finitePresentation
  let ι : I.L →ₗ[𝓞 I.E] (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    { toFun := fun x i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => rfl }
  have hL : I.Lf = Submodule.span (IntAf I.F I.E) (Set.range ι) := rfl
  have hO : ∀ o : 𝓞 I.E, algebraMap _ (I.E ⊗[I.F] Af I.F) o ∈ IntAf I.F I.E := fun o =>
    Formalism.UG.P.levelaf_tmul_mem o (one_mem _)
  have hS : ∀ s ∈ IntAf I.F I.E, ∃ o : 𝓞 I.E, ∃ w ∈ IntAf I.F I.E,
      s = algebraMap _ (I.E ⊗[I.F] Af I.F) o + (g : I.E ⊗[I.F] Af I.F) * w := by
    intro s hs
    obtain ⟨x, hx, w, hw, e⟩ := Formalism.UG.P.csSpan_approx (F := I.F) (E := I.E) Formalism.UG.P.csGlob_intAdApprox (g : 𝓞 I.F)
      (Nat.cast_ne_zero.2 (by omega)) hs
    refine ⟨⟨x, hx⟩, w, hw, ?_⟩
    rw [e, ← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]
    rfl
  have key := fun x : I.Kset => exists_end (IntAf I.F I.E) ι (g : I.E ⊗[I.F] Af I.F) hO hS
    (natCast_mem _ g) (I.fmat x) fun y hy => (x.2 y).1 hy
  choose φ hφ using key
  obtain ⟨r, hr, hi⟩ := card_end_quot I.L I.L_span I.L_fg g
  set N := (nsmulAddMonoidHom (α := I.L →ₗ[𝓞 I.E] I.L) g).range
  have hi' : Nat.card ((I.L →ₗ[𝓞 I.E] I.L) ⧸ N) = g ^ r := hi
  haveI : Finite ((I.L →ₗ[𝓞 I.E] I.L) ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hi']; positivity)
  have h1 := measure_le_card_mul μf I.Kset (I.Kg g) (fun x => (QuotientAddGroup.mk (φ x) : _ ⧸ N))
    fun x y hxy => by
      obtain ⟨θ, hθ⟩ := QuotientAddGroup.eq.1 hxy.symm
      exact congr_of_end (IntAf I.F I.E) ι g _ _ x.2 y.2 (φ x) (φ y) θ (hφ x) (hφ y)
        (by rw [show g • θ = -φ y + φ x from hθ]; abel)
  refine h1.trans ?_
  rw [hi', Nat.cast_pow]
  have h2 : Module.finrank ℚ I.E = I.f * 2 := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]; rfl
  gcongr
  · exact_mod_cast hg
  · rw [h2] at hr; linarith

end GlobalTheory.CongIndex
end
end
