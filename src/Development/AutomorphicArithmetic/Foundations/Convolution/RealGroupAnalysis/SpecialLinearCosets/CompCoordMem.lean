module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section Gen

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def ptMat (c c' : Fin 2 → K) : Matrix (Fin 2) (Fin 2) K := !![c 0, c' 0; c 1, c' 1]

private theorem ptMat_cont (c : Fin 2 → K) : Continuous (ptMat c) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [ptMat] <;> first | exact continuous_const | exact continuous_apply _

private theorem slice_mem {a : Matrix (Fin 2) (Fin 2) K → ℂ}
    (ha : a ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K)) (c : Fin 2 → K) :
    (fun c' => a (ptMat c c')) ∈ localSchwartzBruhatPi K := by
  have hl : Function.LeftInverse (fun X : Matrix (Fin 2) (Fin 2) K => (![X 0 1, X 1 1] : Fin 2 → K))
      (ptMat c) := by
    intro c'
    ext i
    fin_cases i <;> simp [ptMat]
  have hg : Continuous (fun X : Matrix (Fin 2) (Fin 2) K => (![X 0 1, X 1 1] : Fin 2 → K)) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_id.matrix_elem 0 1
    · exact continuous_id.matrix_elem 1 1
  exact ⟨ha.1.comp_continuous (ptMat_cont c),
    ha.2.comp_isClosedEmbedding (hl.isClosedEmbedding hg (ptMat_cont c))⟩

private theorem comp_coord_mem {f : (Fin 2 × Fin 2 → K) → ℂ} (hf : f ∈ localSchwartzBruhatPi K) :
    f ∘ matrixCoordHomeomorph (Fin 2) K ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K) :=
  ⟨hf.1.comp_continuous (matrixCoordHomeomorph (Fin 2) K).continuous,
    hf.2.comp_homeomorph (matrixCoordHomeomorph (Fin 2) K)⟩

variable [MeasurableSpace K] [BorelSpace K]

private noncomputable def PG (ψ : AddChar K Circle) (a : Matrix (Fin 2) (Fin 2) K → ℂ)
    (X : Matrix (Fin 2) (Fin 2) K) : ℂ :=
  localFourierPi ψ (fun c' => a (ptMat (fun i => X i 1) c')) ![-X 1 0, X 0 0]

private theorem PG_add {ψ : AddChar K Circle} (hψ : Continuous ψ)
    {a b : Matrix (Fin 2) (Fin 2) K → ℂ}
    (ha : a ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K))
    (hb : b ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K)) :
    PG ψ (a + b) = PG ψ a + PG ψ b := by
  funext X
  exact congrFun (localFourierPi_add hψ
    (integrable_of_mem_localSchwartzBruhatPi (slice_mem ha _))
    (integrable_of_mem_localSchwartzBruhatPi (slice_mem hb _))) _

private theorem PG_smul (ψ : AddChar K Circle) (s : ℂ) (a : Matrix (Fin 2) (Fin 2) K → ℂ) :
    PG ψ (s • a) = s • PG ψ a := by
  funext X
  exact congrFun (localFourierPi_smul (ψ := ψ) s (fun c' => a (ptMat (fun i => X i 1) c'))) _

private noncomputable def outF (ψ : AddChar K Circle) (g : Fin 2 × Fin 2 → K → ℂ) : Fin 2 × Fin 2 → K → ℂ :=
  fun p => ![![GroundTheory.LocalField.localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ (g (1, 1)), g (0, 0)],
    ![fun x => GroundTheory.LocalField.localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ (g (0, 1)) (-x), g (1, 0)]] p.1 p.2

private theorem PG_tensor (ψ : AddChar K Circle) (g : Fin 2 × Fin 2 → K → ℂ) :
    PG ψ (localTensor g ∘ matrixCoordHomeomorph (Fin 2) K) =
      localTensor (outF ψ g) ∘ matrixCoordHomeomorph (Fin 2) K := by
  funext X
  have hs : (fun c' : Fin 2 → K => (localTensor g ∘ matrixCoordHomeomorph (Fin 2) K) (ptMat (fun i => X i 1) c')) =
      (g (0, 0) (X 0 1) * g (1, 0) (X 1 1)) • localTensor ![g (0, 1), g (1, 1)] := by
    funext c'
    simp [localTensor, Fintype.prod_prod_type, Fin.prod_univ_two, ptMat, coe_matrixCoordHomeomorph, matrixCoord]
    ring
  rw [PG, hs, localFourierPi_smul, localFourierPi_localTensor]
  simp [localTensor, Fintype.prod_prod_type, Fin.prod_univ_two, outF, coe_matrixCoordHomeomorph, matrixCoord]
  ring

private theorem PG_mem {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {f : (Fin 2 × Fin 2 → K) → ℂ} (hf : f ∈ localSchwartzBruhatPi K) :
    PG ψ (f ∘ matrixCoordHomeomorph (Fin 2) K) ∈
      GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K) := by
  rw [localSchwartzBruhatPi_eq_span] at hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨⟨N, a⟩, rfl⟩ := hg
    rw [PG_tensor]
    refine comp_coord_mem (localTensor_mem fun p => ?_)
    have h1 : ∀ {u : K → ℂ}, u ∈ GroundTheory.LocalField.schwartzBruhat K →
        GroundTheory.LocalField.localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ u ∈ GroundTheory.LocalField.schwartzBruhat K :=
      fun hu => GroundTheory.LocalField.localFourier_mem_schwartzBruhat _ hψ hψ1 hu
    have h0 : ∀ q : Fin 2 × Fin 2, cosetInd (GroundTheory.LocalField.valBall K N) (a q) ∈ GroundTheory.LocalField.schwartzBruhat K :=
      fun q => cosetInd_valBall_mem N (a q)
    obtain ⟨i, j⟩ := p
    fin_cases i <;> fin_cases j
    · exact h1 (h0 _)
    · exact h0 _
    · have := h1 (h0 (0, 1))
      exact ⟨this.1.comp_continuous continuous_neg, this.2.comp_homeomorph (Homeomorph.neg K)⟩
    · exact h0 _
  | zero =>
    have : (0 : (Fin 2 × Fin 2 → K) → ℂ) ∘ matrixCoordHomeomorph (Fin 2) K = (0 : ℂ) • (0 : Matrix (Fin 2) (Fin 2) K → ℂ) := by
      funext X; simp
    rw [this, PG_smul, zero_smul]
    exact zero_mem _
  | add g h hg hh ihg ihh =>
    rw [← localSchwartzBruhatPi_eq_span] at hg hh
    have : (g + h) ∘ matrixCoordHomeomorph (Fin 2) K =
        g ∘ matrixCoordHomeomorph (Fin 2) K + h ∘ matrixCoordHomeomorph (Fin 2) K := rfl
    rw [this, PG_add hψ (comp_coord_mem hg) (comp_coord_mem hh)]
    exact add_mem ihg ihh
  | smul c g _ ih =>
    have : (c • g) ∘ matrixCoordHomeomorph (Fin 2) K = c • (g ∘ matrixCoordHomeomorph (Fin 2) K) := rfl
    rw [this, PG_smul]
    exact Submodule.smul_mem _ c ih

private theorem PG_mem' {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {a : Matrix (Fin 2) (Fin 2) K → ℂ}
    (ha : a ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K)) :
    PG ψ a ∈ GroundTheory.LocalField.schwartzBruhat (Matrix (Fin 2) (Fin 2) K) := by
  have hf : a ∘ (matrixCoordHomeomorph (Fin 2) K).symm ∈ localSchwartzBruhatPi K :=
    ⟨ha.1.comp_continuous (matrixCoordHomeomorph (Fin 2) K).symm.continuous,
      ha.2.comp_homeomorph (matrixCoordHomeomorph (Fin 2) K).symm⟩
  have h := PG_mem hψ hψ1 hf
  have he : (a ∘ (matrixCoordHomeomorph (Fin 2) K).symm) ∘ matrixCoordHomeomorph (Fin 2) K = a := by
    funext X
    simp
  rwa [he] at h

end Gen

private theorem Pt_eq_PG {F : Type} [Field F] [NumberField F] (v : P F) (a : M2 v → ℂ) :
    Pt a = PG (localAdelicChar F v) a := by
  funext X
  unfold Pt PG localFourierPi
  refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
  have h : X 0 0 * c' 1 - X 1 0 * c' 0 = ∑ i, c' i * (![-X 1 0, X 0 0] : Fin 2 → Kv v) i := by
    simp [Fin.sum_univ_two]
    ring
  simp only [ψl, h]
  rfl

theorem UpperTheory.ConvolutionTheory.R2.I.ptMem :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∃ T : SB (M2 v) →ₗ[ℂ] SB (M2 v), ∀ a, (T a).1 = Pt a.1 := by
  intro F _ _ v
  have hc := continuous_localAdelicChar (K := F) v
  have h1 := localAdelicChar_ne_one (K := F) (v := v)
  refine ⟨{ toFun := fun a => ⟨Pt a.1, ?_⟩, map_add' := ?_, map_smul' := ?_ }, fun a => rfl⟩
  · rw [Pt_eq_PG]
    exact PG_mem' hc h1 a.2
  · intro a b
    apply Subtype.ext
    change Pt (a.1 + b.1) = Pt a.1 + Pt b.1
    rw [Pt_eq_PG, Pt_eq_PG, Pt_eq_PG]
    exact PG_add hc a.2 b.2
  · intro s a
    apply Subtype.ext
    change Pt (s • a.1) = s • Pt a.1
    rw [Pt_eq_PG, Pt_eq_PG]
    exact PG_smul _ s a.1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem sg_eq_incl {F : Type} [Field F] [NumberField F] (v : P F) (x : Kv v) :
    sg v x = finitePlaceIncl v x := by
  obtain ⟨-, -, h3, -, -, -, -, h8, -, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws F v
  refine Prod.ext ?_ ?_
  · rw [(h8 x).1, finitePlaceIncl_apply, finiteAdeleInr_fst]
  · rw [finitePlaceIncl_apply, finiteAdeleInr_snd]
    refine Subtype.ext (funext fun u => ?_)
    by_cases hu : u = v
    · subst hu
      exact (h3 x).trans (finiteAdeleSingleAdd_apply_self u x).symm
    · exact ((h8 x).2 u hu).trans (finiteAdeleSingleAdd_apply_of_ne hu x).symm

private theorem exists_char_ne {F : Type} [Field F] [NumberField F] (v : P F) :
    ∃ y, localAdelicChar F v y ≠ 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (FractionalIdeal.count F v ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) :
      FractionalIdeal (nonZeroDivisors (𝓞 F)) F) + 1))
  have h := (forall_localAdelicChar_mul_eq_one_iff v z).1 fun a _ => hc _
  rw [mem_localInvDifferent_iff_valued, hz, WithZero.exp_le_exp] at h
  omega

private theorem locConst_of_char {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (χ : AddChar G Circle) (H : AddSubgroup G)
    (hH : IsOpen (H : Set G)) (h1 : ∀ y ∈ H, χ y = 1) :
    IsLocallyConstant fun x => ((χ x : Circle) : ℂ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h0 := hH.mem_nhds (zero_mem H)
  have hcc : Continuous fun y : G => y - x := continuous_id.sub continuous_const
  have hc : Filter.Tendsto (fun y : G => y - x) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self] using hcc.tendsto x
  filter_upwards [hc h0] with y hy
  have e := AddChar.map_add_eq_mul χ (y - x) x
  rw [h1 _ hy, one_mul, sub_add_cancel] at e
  rw [e]

private theorem psi_locConst {F : Type} [Field F] [NumberField F] (v : P F) :
    IsLocallyConstant (ψl v) :=
  locConst_of_char (localAdelicChar F v) (localInvDifferent v) (isOpen_localInvDifferent v)
    fun _ hy => localAdelicChar_eq_one_of_mem hy

private theorem ab_idl_eq {F : Type} [Field F] [NumberField F] (v : P F) (t : (Kv v)ˣ) :
    ab (idl v t) = (GroundTheory.LocalField.modulus (t : Kv v) : ℝ) := by
  obtain ⟨-, -, -, -, -, h6, h7, -, -, -⟩ := UpperTheory.ConvolutionTheory.R2.H.sgLaws F v
  let f0 : (Kv v)ˣ →* ℝ :=
    { toFun := fun t => ab (idl v t)
      map_one' := by simp [ab, idl]
      map_mul' := fun a b => by simp [ab, idl] }
  have hz : ∀ (x : (Kv v)ˣ) (n : ℤ), f0 (x ^ n) = f0 x ^ n := fun x n => by
    have := congrArg Units.val (map_zpow f0.toHomUnits x n)
    simpa using this
  set ϖ := GroundTheory.LocalField.unifUnit (Kv v) with hϖ
  have hϖ1 : GroundTheory.LocalField.ord (ϖ : Kv v) = 1 := by
    simpa using GroundTheory.LocalField.ord_unifUnit_zpow (K := Kv v) 1
  have hU : IsU ϖ := by
    show Valued.v (ϖ : Kv v) = _
    rw [valued_eq_exp_neg_ord ϖ.ne_zero, hϖ1]
    rfl
  have hu : f0 (ϖ ^ (-GroundTheory.LocalField.ord (t : Kv v)) * t) = 1 := h7 _ (by
    rw [valued_eq_one_iff_ord (Units.ne_zero _), GroundTheory.LocalField.ord_units_mul,
      GroundTheory.LocalField.ord_unifUnit_zpow]
    omega)
  have e : f0 t = f0 ϖ ^ GroundTheory.LocalField.ord (t : Kv v) := by
    conv_lhs => rw [GroundTheory.LocalField.eq_unifUnit_zpow_mul t]
    rw [map_mul, hz, hu, mul_one]
  show f0 t = _
  rw [e, show f0 ϖ = _ from h6 ϖ hU, GroundTheory.LocalField.modulus_of_ne_zero t.ne_zero,
    residueCard_adicCompletion]
  push_cast
  rw [_root_.inv_zpow, _root_.zpow_neg]

theorem UpperTheory.ConvolutionTheory.R2.I.psiLaws :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), localAdelicChar F v ≠ 1 ∧ (∀ x, ψ (sg v x) = ψl v x) ∧ (∀ x y, ψl v (x + y) = ψl v x * ψl v y) ∧
      IsLocallyConstant (ψl v) ∧ (∀ x : Kv v, x ≠ 0 → ∃ s, ψl v (s * x) ≠ 1) ∧
      ∀ t : (Kv v)ˣ, ab (idl v t) = (GroundTheory.LocalField.modulus (t : Kv v) : ℝ) := by
  intro F _ _ v
  refine ⟨fun h => ?_, fun x => ?_, fun x y => ?_, psi_locConst v, fun x hx => ?_, ab_idl_eq v⟩
  · obtain ⟨y, hy⟩ := exists_char_ne v
    exact hy (by rw [h]; rfl)
  · simp only [ψ, ψl, sg_eq_incl, localAdelicChar_apply]
  · simp only [ψl, AddChar.map_add_eq_mul, Circle.coe_mul]
  · obtain ⟨y, hy⟩ := exists_char_ne v
    refine ⟨y / x, fun h => hy ?_⟩
    rw [div_mul_cancel₀ y hx] at h
    exact Circle.coe_eq_one.1 h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.FstDetFin
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem fst_detFin {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    (((Matrix.GeneralLinearGroup.det (finGL E 2 k) : (A E)ˣ) : A E)).1 = 1 := by
  have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)
  have h1 : Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k) = 1 :=
    map_cornerGL_of_zero _ _ (fun _ => rfl) k
  rw [h1] at h
  refine h.symm.trans ?_
  simp

private theorem fst_norm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (z : (A E)ˣ) (hz : (z : A E).1 = 1) :
    ((GroundTheory.Global.ideleNorm F E z : (A F)ˣ) : A F).1 = 1 := by
  let e : A F := ((1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have h1 : am E e * (z : A E) = am E e := by
    have hi1 : (am E e).1 = 1 := map_one (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
    have hi2 : (am E e).2 = 0 := map_zero (AdeleBaseChange.finiteAdeleMap F E)
    refine Prod.ext ?_ ?_
    · change (am E e).1 * (z : A E).1 = (am E e).1
      rw [hz, mul_one]
    · change (am E e).2 * (z : A E).2 = (am E e).2
      rw [hi2, zero_mul]
  have h2 := congrArg D.co h1
  rw [D.co_am_mul, ← D.mkE_base, D.co_mkE] at h2
  have hu : e * D.co z 0 = e := congrFun h2 0
  have ht : e * D.co z 1 = 0 := congrFun h2 1
  have hu1 : (D.co z 0).1 = 1 := by
    have h := congrArg Prod.fst hu
    change (1 : InfiniteAdeleRing F) * (D.co z 0).1 = 1 at h
    rwa [one_mul] at h
  have ht1 : (D.co z 1).1 = 0 := by
    have h := congrArg Prod.fst ht
    change (1 : InfiniteAdeleRing F) * (D.co z 1).1 = 0 at h
    rwa [one_mul] at h
  rw [D.coe_ideleNorm]
  change (D.co z 0).1 ^ 2 - (rt D.δ : A F).1 * (D.co z 1).1 ^ 2 = 1
  rw [hu1, ht1]
  simp

theorem UpperTheory.ConvolutionTheory.R2.I.locSm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (v : P F),
      (∀ f, IsOpen {g | π.locRep v g f = f}) ∧ (∀ x (f : π.V) g, (π.locRep v x f).1.1 g = f.1.1 (g * lc v x)) ∧
      ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (_ : Dat F E) (k : GL (Fin 2) (Af E)), ∀ f ∈ π.V,
        ∃ f' ∈ π.V, f'.1 = fun g => f.1 (g * dM (nu F (finGL E 2 k))) := by
  intro F _ _ _ π v
  refine ⟨fun f => ?_, fun x f g => rfl, ?_⟩
  · have e : {g | π.locRep v g f = f} = locGL F 2 v ⁻¹' {k | TR.finRep F 2 k f.1 = f.1} := by
      ext g
      exact Subtype.ext_iff
    rw [e]
    exact (π.cusp f.1 f.2).1.level.preimage (CuspSub.continuous_locGL v)
  · intro E _ _ _ D k f hf
    have h1 : ((nu F (finGL E 2 k) : (A F)ˣ) : A F).1 = 1 := fst_norm D _ (fst_detFin k)
    generalize nu F (finGL E 2 k) = t at h1
    have hp : TR.pInf F (t : A F) = 1 := by
      change (TR.infEq F).symm (t : A F).1 = 1
      rw [h1]
      exact map_one _
    have hinf : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [dM, hp]
    have hd : finGL F 2 (Matrix.GeneralLinearGroup.map (pFin F) (dM t)) = dM t := by
      have h := TR.infGL_mul_finGL (dM t)
      rwa [hinf, map_one, one_mul] at h
    refine ⟨_, π.stable (.fin (Matrix.GeneralLinearGroup.map (pFin F) (dM t))) f hf, ?_⟩
    funext g
    change f.1 (g * finGL F 2 _) = f.1 (g * dM t)
    rw [hd]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.MkLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.mkLaws :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E), (∀ u t u' t', D.mkE u t * D.mkE u' t' = D.mkE (u * u' + rt D.δ * (t * t')) (u * t' + t * u')) ∧
      (∀ u t u' t', D.mkE u t + D.mkE u' t' = D.mkE (u + u') (t + t')) ∧ D.mkE 1 0 = 1 ∧ (∀ u t, D.co (D.mkE u t) = ![u, t]) ∧
      (∀ z, D.mkE (D.co z 0) (D.co z 1) = z) ∧ (∀ u t, D.bar (D.mkE u t) = D.mkE u (-t)) ∧
      ∀ (z : (A E)ˣ) u t, (z : A E) = D.mkE u t → ((ideleNorm F E z : (A F)ˣ) : A F) = u ^ 2 - rt D.δ * t ^ 2 := by
  intro F E _ _ _ _ _ D
  refine ⟨D.mkE_mul, fun u t u' t' => (D.mkE_add u t u' t').symm, D.mkE_one, D.co_mkE, D.mkE_co, D.bar_mkE, ?_⟩
  intro z u t h
  have hc := D.co_mkE u t
  rw [D.coe_ideleNorm, h, hc]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GenSL
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.genSL :
    ∀ (K : Type) [Field K] (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (b : K), g.1 = !![1, b; 0, 1] → g ∈ H) →
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (c : K), g.1 = !![1, 0; c, 1] → g ∈ H) → H = ⊤ := by
  intro K _ H hu hl
  have hdet : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := fun g => by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  have nU : ∀ b : K, ∃ g ∈ H, g.1 = !![1, b; 0, 1] := fun b =>
    ⟨⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩, hu _ b rfl, rfl⟩
  have nL : ∀ c : K, ∃ g ∈ H, g.1 = !![1, 0; c, 1] := fun c =>
    ⟨⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩, hl _ c rfl, rfl⟩
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, g.1 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    obtain ⟨x, hx, hx'⟩ := nU ((g.1 0 0 - 1) / g.1 1 0)
    obtain ⟨l, hl1, hl'⟩ := nL (g.1 1 0)
    obtain ⟨y, hy, hy'⟩ := nU ((g.1 1 1 - 1) / g.1 1 0)
    have hd := hdet g
    have e : g = x * l * y := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx', hl', hy']
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
          first | ring1 | linear_combination (-1 : K) * hd
    rw [e]
    exact H.mul_mem (H.mul_mem hx hl1) hy
  refine eq_top_iff.2 fun g _ => ?_
  by_cases hc : g.1 1 0 = 0
  · obtain ⟨l, hl1, hl'⟩ := nL 1
    have hd := hdet g
    have ha : g.1 0 0 ≠ 0 := by
      intro h0
      rw [h0, hc] at hd
      simp at hd
    have h2 : l * g ∈ H := by
      apply key
      rw [Matrix.SpecialLinearGroup.coe_mul, hl']
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hc] using ha
    have e : g = l⁻¹ * (l * g) := by group
    rw [e]
    exact H.mul_mem (H.inv_mem hl1) h2
  · exact key g hc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.WeilLiftEquivariance
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

private theorem nu_mul' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h h' : GL (Fin 2) (A E)) : nu F (h * h') = nu F h * nu F h' := by
  simp only [nu, map_mul]

private theorem nu_gl' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (b : A E) : nu F (gl (nU b)) = 1 := by
  have h : Matrix.GeneralLinearGroup.det (gl (nU b)) = 1 := by
    exact Units.ext (nU b).2
  simp only [nu, h, map_one]

private theorem dM_mul' {F : Type} [Field F] [NumberField F] (s t : (A F)ˣ) :
    dM (s * t) = dM s * dM t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cD_one' {F : Type} [Field F] [NumberField F] (g : G1 F) : cD 1 g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem Wf_tr {F : Type} [Field F] [NumberField F] (f : GL (Fin 2) (A F) → ℂ)
    (x y : GL (Fin 2) (A F)) : Wf (fun g => f (g * x)) y = Wf f (y * x) := by
  simp only [Wf, mul_assoc]

theorem UpperTheory.ConvolutionTheory.R2.I.weilLift_equivariance :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (f : GL (Fin 2) (A F) → ℂ) (φ : S4 F) (h : GL (Fin 2) (A E)),
      (∀ h₀, W1 W M f φ (h * h₀) = W1 W M (fun g => f (g * dM (nu F h₀))) (W.L h₀ φ) h) ∧
      ∀ u t, W1 W M f φ (gl (nU (D.mkE u t)) * h) = ψ (-(2 * u)) * W1 W M f φ h := by
  intro F E _ _ _ _ _ _ _ D W M f φ h
  constructor
  · intro h₀
    have key : w1 W f φ (h * h₀) = w1 W (fun g => f (g * dM (nu F h₀))) (W.L h₀ φ) h := by
      funext g
      simp only [w1]
      rw [Wf_tr, nu_mul', dM_mul', map_mul, Module.End.mul_apply, mul_assoc]
    simp only [W1, key]
  · intro u t
    have hn := nu_gl' (F := F) (D.mkE u t)
    have key : ∀ g, w1 W f φ (gl (nU (D.mkE u t)) * h) g = ψ (-(2 * u)) * w1 W f φ h g := by
      intro g
      have hc : W.Om g (W.L (gl (nU (D.mkE u t))) (W.L h φ)) =
          W.L (gl (nU (D.mkE u t))) (W.Om g (W.L h φ)) := by
        have := congrArg (fun T : Module.End ℂ (S4 F) => T (W.L h φ)) (W.comm (gl (nU (D.mkE u t))) g)
        simp only [Module.End.mul_apply, hn, cD_one'] at this
        exact this.symm
      have hne := (hatSt F E D W).nE u t (W.Om g (W.L h φ)) 1 1 0
      have hs : -(1 * (2 * (u * 1 - rt D.δ * (t * 0)))) = -(2 * u) := by
        simp
      rw [hs] at hne
      simp only [w1]
      rw [nu_mul', hn, one_mul, map_mul, Module.End.mul_apply, hc, hne]
      ring
    simp only [W1, Meas.I0, iw, key]
    rw [← integral_const_mul]
    congr 1
    funext p
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CosetSum
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.cosetSum :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (U U' : Subgroup G), U' ≤ U → IsCompact (U : Set G) → IsOpen (U' : Set G) →
      ∃ s : Finset G, s.Nonempty ∧ (∀ g ∈ s, g ∈ U) ∧ ∀ x, ind U x = ∑ g ∈ s, ind U' (x * g⁻¹) := by
  intro G _ _ _ _ U U' hle hU hU'
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hopen : IsOpen ((U'.subgroupOf U : Subgroup U) : Set U) := hU'.preimage continuous_subtype_val
  haveI : Finite (U ⧸ U'.subgroupOf U) := Subgroup.quotient_finite_of_isOpen _ hopen
  haveI : Finite (Quotient (QuotientGroup.rightRel (U'.subgroupOf U))) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel (U'.subgroupOf U)).symm
  letI : Fintype (Quotient (QuotientGroup.rightRel (U'.subgroupOf U))) := Fintype.ofFinite _
  let mk : U → Quotient (QuotientGroup.rightRel (U'.subgroupOf U)) := fun u => Quotient.mk _ u
  let r : Quotient (QuotientGroup.rightRel (U'.subgroupOf U)) → G := fun q => ((Quotient.out q : U) : G)
  have hrU : ∀ q, r q ∈ U := fun q => (Quotient.out q : U).2
  have hinj : Function.Injective r := by
    intro a b h
    have : (Quotient.out a : U) = Quotient.out b := Subtype.ext h
    rw [← Quotient.out_eq a, ← Quotient.out_eq b, this]
  have key : ∀ (u : U) q, (u : G) * (r q)⁻¹ ∈ U' ↔ q = mk u := by
    intro u q
    have h1 : mk (Quotient.out q) = q := Quotient.out_eq q
    constructor
    · intro h
      rw [← h1]
      refine Quotient.sound ?_
      change QuotientGroup.rightRel _ _ _
      rw [QuotientGroup.rightRel_apply]
      change ((u * (Quotient.out q)⁻¹ : U) : G) ∈ U'
      simpa [r] using h
    · intro h
      have h2 : mk (Quotient.out q) = mk u := h1.trans h
      have h3 := Quotient.exact h2
      change QuotientGroup.rightRel _ _ _ at h3
      rw [QuotientGroup.rightRel_apply] at h3
      have h4 : ((u * (Quotient.out q)⁻¹ : U) : G) ∈ U' := h3
      simpa [r] using h4
  refine ⟨Finset.univ.image r, ⟨r (mk 1), Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_⟩
  · intro g hg
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hg
    exact hrU q
  · intro x
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    by_cases hx : x ∈ U
    · have h1 : ind U x = 1 := by simp [ind, Set.indicator, hx]
      rw [h1, Finset.sum_eq_single (mk ⟨x, hx⟩)]
      · have : x * (r (mk ⟨x, hx⟩))⁻¹ ∈ U' := (key ⟨x, hx⟩ _).mpr rfl
        simp [ind, Set.indicator, this]
      · intro q _ hq
        have : x * (r q)⁻¹ ∉ U' := fun h => hq ((key ⟨x, hx⟩ q).mp h)
        simp [ind, Set.indicator, this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h1 : ind U x = 0 := by simp [ind, Set.indicator, hx]
      rw [h1]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      have : x * (r q)⁻¹ ∉ U' := fun h => hx (by
        have := U.mul_mem (hle h) (hrU q)
        simpa using this)
      simp [ind, Set.indicator, this]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CosetSpan
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.cosetSpan :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G], Lgrp G → ∀ a ∈ SB G, ∀ N ∈ 𝓝 (1 : G),
      ∃ (U : Subgroup G) (s : Finset G) (c : G → ℂ), IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ (U : Set G) ⊆ N ∧
        ∀ x, a x = ∑ g ∈ s, c g * ind U (g⁻¹ * x) := by
  intro G _ _ _ _ hL a ha N hN
  have hlc : IsLocallyConstant a := (GroundTheory.LocalField.mem_schwartzBruhat.1 ha).1
  have hcs : HasCompactSupport a := (GroundTheory.LocalField.mem_schwartzBruhat.1 ha).2
  have hK : IsCompact (tsupport a) := hcs
  have hS : IsOpen {p : G × G | a (p.1 * p.2) = a p.1} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hev := (IsLocallyConstant.iff_eventually_eq a).1 hlc
    have e1 : ∀ᶠ q : G × G in 𝓝 p, a (q.1 * q.2) = a (p.1 * p.2) :=
      ((continuous_fst.mul continuous_snd).tendsto p).eventually (hev (p.1 * p.2))
    have e2 : ∀ᶠ q : G × G in 𝓝 p, a q.1 = a p.1 :=
      (continuous_fst.tendsto p).eventually (hev p.1)
    filter_upwards [e1, e2] with q h1 h2
    show a (q.1 * q.2) = a q.1
    rw [h1, h2]
    exact hp
  obtain ⟨W1, W0, -, hW0, hKW, h1W, hWS⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (1 : G))) hS (by
      rintro ⟨x, u⟩ ⟨-, hu⟩
      have hu' : u = 1 := hu
      subst hu'
      show a (x * 1) = a x
      rw [mul_one])
  have hN' : N ∩ W0 ∈ 𝓝 (1 : G) := Filter.inter_mem hN (hW0.mem_nhds (h1W rfl))
  obtain ⟨U, hUo, hUc, hUN⟩ := hL _ hN'
  have hinv0 : ∀ x ∈ tsupport a, ∀ u ∈ U, a (x * u) = a x := fun x hx u hu =>
    hWS (Set.mk_mem_prod (hKW hx) (hUN hu).2)
  have hinv : ∀ x, ∀ u ∈ U, a (x * u) = a x := by
    intro x u hu
    by_cases hx : x ∈ tsupport a
    · exact hinv0 x hx u hu
    by_cases hxu : x * u ∈ tsupport a
    · have h := hinv0 _ hxu u⁻¹ (U.inv_mem hu)
      rw [mul_inv_cancel_right] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hxu, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {y : G | x⁻¹ * y ∈ U}) (by
    intro x _
    have ho : IsOpen {y : G | x⁻¹ * y ∈ U} :=
      hUo.preimage (continuous_const.mul continuous_id)
    refine ho.mem_nhds ?_
    show x⁻¹ * x ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem)
  let r : G → G := fun x => Quotient.out (QuotientGroup.mk x : G ⧸ U)
  have hr : ∀ x, (r x)⁻¹ * x ∈ U := fun x => QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have h1 : ∀ y ∈ U, ind U y = 1 := fun y hy => by simp [ind, hy]
  have h0 : ∀ y, y ∉ U → ind U y = 0 := fun y hy => by simp [ind, hy]
  refine ⟨U, t.image r, a, hUo, hUc, fun x hx => (hUN hx).1, ?_⟩
  intro x
  have huniq : ∀ g ∈ t.image r, ∀ g' ∈ t.image r, g⁻¹ * x ∈ U → g'⁻¹ * x ∈ U → g' = g := by
    intro g hg g' hg' hgx hgx'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨y', -, rfl⟩ := Finset.mem_image.1 hg'
    have e : (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk y' := by
      have a1 : (QuotientGroup.mk (r y) : G ⧸ U) = QuotientGroup.mk x := QuotientGroup.eq.2 hgx
      have a2 : (QuotientGroup.mk (r y') : G ⧸ U) = QuotientGroup.mk x := QuotientGroup.eq.2 hgx'
      have b1 : (QuotientGroup.mk (r y) : G ⧸ U) = QuotientGroup.mk y := QuotientGroup.out_eq' _
      have b2 : (QuotientGroup.mk (r y') : G ⧸ U) = QuotientGroup.mk y' := QuotientGroup.out_eq' _
      rw [← b1, ← b2, a1, a2]
    show Quotient.out (QuotientGroup.mk y' : G ⧸ U) = Quotient.out (QuotientGroup.mk y : G ⧸ U)
    rw [e]
  by_cases h : ∃ g ∈ t.image r, g⁻¹ * x ∈ U
  · obtain ⟨g, hg, hgx⟩ := h
    rw [Finset.sum_eq_single g, h1 _ hgx, mul_one]
    · have e := hinv g _ hgx
      rw [mul_inv_cancel_left] at e
      exact e
    · intro b hb hne
      rw [h0, mul_zero]
      intro hbx
      exact hne (huniq g hg b hb hgx hbx)
    · intro hn
      exact absurd hg hn
  · have hx0 : a x = 0 := by
      by_contra hne
      have hxs : x ∈ tsupport a := subset_tsupport _ hne
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxs)
      refine h ⟨r y, Finset.mem_image_of_mem r hy, ?_⟩
      have e : (r y)⁻¹ * x = ((r y)⁻¹ * y) * (y⁻¹ * x) := by group
      rw [e]
      exact U.mul_mem (hr y) hxy
    rw [hx0]
    symm
    apply Finset.sum_eq_zero
    intro g hg
    rw [h0 _ (fun hgx => h ⟨g, hg, hgx⟩), mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.IsCompactBoxSet
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

section SlopeTestRemainingChoices

open GroundTheory.LocalField

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def boxSet (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℤ) : Set (Matrix (Fin 2) (Fin 2) K) :=
  {m | ∀ i j, m i j ∈ valBall K n}

private theorem isOpen_boxSet (n : ℤ) : IsOpen (boxSet K n) := by
  have : boxSet K n = ⋂ i, ⋂ j, (fun X : Matrix (Fin 2) (Fin 2) K => X i j) ⁻¹'
      (valBall K n : Set K) := by
    ext X; simp [boxSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))

private theorem isCompact_boxSet (n : ℤ) : IsCompact (boxSet K n) := by
  have : boxSet K n = Set.univ.pi fun _ : Fin 2 => Set.univ.pi fun _ : Fin 2 =>
      (valBall K n : Set K) := by
    ext X
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_valBall n

private def boxGrp (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℤ) : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K)) where
  carrier := Multiplicative.toAdd ⁻¹' boxSet K n
  one_mem' := fun _ _ => zero_mem _
  mul_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
  inv_mem' := fun ha i j => neg_mem (ha i j)

private theorem lgrp_matrix : Lgrp (Multiplicative (Matrix (Fin 2) (Fin 2) K)) := by
  intro N hN
  have hS : Multiplicative.ofAdd ⁻¹' N ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K) :=
    (continuous_ofAdd.tendsto (0 : Matrix (Fin 2) (Fin 2) K)) hN
  obtain ⟨r, hr⟩ := GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS
  refine ⟨boxGrp K r, (isOpen_boxSet (r : ℤ)).preimage continuous_toAdd, ?_, ?_⟩
  · have := (isCompact_boxSet (K := K) (r : ℤ)).image continuous_ofAdd
    convert this using 1
    ext x
    constructor
    · intro hx
      exact ⟨Multiplicative.toAdd x, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · intro x hx
    exact hr hx

private def cgrp (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) where
  carrier := {g | g.1 - 1 ∈ boxSet K ((n : ℤ) + 1)}
  one_mem' := by
    intro i j
    simp
  mul_mem' := by
    intro a b ha hb i j
    have e : (a * b).1 - 1 = (a.1 - 1) * (b.1 - 1) + (a.1 - 1) + (b.1 - 1) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
    rw [e]
    refine add_mem (add_mem ?_ (ha i j)) (hb i j)
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    exact valBall_antitone (by omega) (mul_mem_valBall (ha i l) (hb l j))
  inv_mem' := by
    intro g hg i j
    have e : (g⁻¹).1 = !![g.1 1 1, -g.1 0 1; -g.1 1 0, g.1 0 0] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    have h00 := hg 0 0
    have h01 := hg 0 1
    have h10 := hg 1 0
    have h11 := hg 1 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq] at h00 h11
    simp only [Matrix.sub_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at h01 h10
    rw [e]
    fin_cases i <;> fin_cases j <;> simp
    · exact h11
    · exact h01
    · exact h10
    · exact h00

private theorem isOpen_cgrp (n : ℕ) :
    IsOpen (cgrp K n : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  have hc : Continuous fun g : Matrix.SpecialLinearGroup (Fin 2) K => g.1 - 1 :=
    continuous_subtype_val.sub continuous_const
  exact (isOpen_boxSet _).preimage hc

private theorem isCompact_cgrp [T2Space K] (n : ℕ) :
    IsCompact (cgrp K n : Set (Matrix.SpecialLinearGroup (Fin 2) K)) := by
  refine (Subtype.isCompact_iff (p := fun A : Matrix (Fin 2) (Fin 2) K => A.det = 1)).2 ?_
  have hC : IsCompact ((fun m : Matrix (Fin 2) (Fin 2) K => m + 1) '' boxSet K ((n : ℤ) + 1)) :=
    (isCompact_boxSet _).image (continuous_id.add continuous_const)
  have hD : IsClosed {m : Matrix (Fin 2) (Fin 2) K | m.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  convert hC.inter_right hD using 1
  ext m
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g.1 - 1, hg, by simp⟩, g.2⟩
  · rintro ⟨⟨y, hy, rfl⟩, hd⟩
    refine ⟨⟨y + 1, hd⟩, ?_, rfl⟩
    change (y + 1) - 1 ∈ boxSet K ((n : ℤ) + 1)
    simpa using hy

private theorem lgrp_sl [T2Space K] : Lgrp (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro N hN
  obtain ⟨W, hW', hWN⟩ := (mem_nhds_subtype {A : Matrix (Fin 2) (Fin 2) K | A.det = 1} (1 : Matrix.SpecialLinearGroup (Fin 2) K) N).1 hN
  have hW : W ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) K) := hW'
  have hS : (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W ∈ 𝓝 (0 : Matrix (Fin 2) (Fin 2) K) := by
    have hc : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m + 1 :=
      continuous_id.add continuous_const
    have := hc.tendsto (0 : Matrix (Fin 2) (Fin 2) K)
    rw [zero_add] at this
    exact this hW
  obtain ⟨r, hr⟩ := GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset hS
  refine ⟨cgrp K r, isOpen_cgrp r, isCompact_cgrp r, fun g hg => hWN ?_⟩
  have h1 : g.1 - 1 ∈ (fun m : Matrix (Fin 2) (Fin 2) K => m + 1) ⁻¹' W :=
    hr fun i j => valBall_antitone (m := (r : ℤ)) (n := (r : ℤ) + 1) (by omega) (hg i j)
  have h2 : (g.1 - 1) + 1 ∈ W := h1
  rw [sub_add_cancel] at h2
  exact h2

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.I.lgrp :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), Lgrp (SL v) ∧ Lgrp (Multiplicative (M2 v)) := by
  intro F _ _ v
  exact ⟨lgrp_sl, lgrp_matrix⟩
end
