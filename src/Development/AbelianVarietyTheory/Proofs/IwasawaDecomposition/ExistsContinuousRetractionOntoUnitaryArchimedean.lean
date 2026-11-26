module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DualWeylZeroConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def evGL (w : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℂ) w)

theorem gl_ext_evGL {a b : GL (Fin n) (Cinf E)} (h : ∀ w, evGL w a = evGL w b) : a = b := by
  ext i j w
  exact congrArg (fun x : GL (Fin n) ℂ => x i j) (h w)


open Classical in
def atPlace (v : InfinitePlace E) : Cinf E →ₙ+* Cinf E where
  toFun x := Pi.single v (x v)
  map_mul' x y := Pi.single_mul (α := fun _ : InfinitePlace E => ℂ) v (x v) (y v)
  map_zero' := Pi.single_zero (M := fun _ : InfinitePlace E => ℂ) v
  map_add' x y := Pi.single_add (f := fun _ : InfinitePlace E => ℂ) v (x v) (y v)

theorem atPlace_self (v : InfinitePlace E) (x : Cinf E) : atPlace v x v = x v := by
  classical
  exact Pi.single_eq_same (M := fun _ : InfinitePlace E => ℂ) v (x v)

theorem atPlace_of_ne {v w : InfinitePlace E} (h : w ≠ v) (x : Cinf E) : atPlace v x w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun _ : InfinitePlace E => ℂ) h (x v)

def cutGL (v : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) (Cinf E) := cornerGL n (atPlace v)

theorem evGL_cutGL_self (v : InfinitePlace E) (y : GL (Fin n) (Cinf E)) : evGL v (cutGL v y) = evGL v y :=
  map_cornerGL_of_hom _ _ _ (fun x => atPlace_self v x) y

theorem evGL_cutGL_of_ne {v w : InfinitePlace E} (h : w ≠ v) (y : GL (Fin n) (Cinf E)) :
    evGL w (cutGL v y) = 1 :=
  map_cornerGL_of_zero _ _ (fun x => atPlace_of_ne h x) y

theorem unitary_iff_evGL (y : GL (Fin n) (Cinf E)) :
    y.valᴴ * y.val = 1 ↔ ∀ w, (evGL w y).valᴴ * (evGL w y).val = 1 := by
  have key : ∀ (w : InfinitePlace E) i j, ((evGL w y).valᴴ * (evGL w y).val) i j = (y.valᴴ * y.val) i j w := by
    intro w i j
    simp [evGL, Matrix.mul_apply, Finset.sum_apply]
  constructor
  · intro h w
    ext i j
    rw [key, h]
    rcases eq_or_ne i j with rfl | e <;> simp [*]
  · intro h
    ext i j w
    rw [← key, h w]
    rcases eq_or_ne i j with rfl | e <;> simp [*]

theorem cInf_unitary (g : UA E n) : (cInf g).valᴴ * (cInf g).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [mul_one] at hg
  have h1 : (cInf g).val = g.1.val.map (pInf E) := rfl
  have h3 : (cT (conjAd E) g.1.val).map (pInf E) = (cInf g).valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, h1]
    exact (infEq E).symm_apply_apply _
  have h5 := congrArg (fun m => m.map (pInf E)) hg
  simp only [Matrix.map_mul, h3, ← h1] at h5
  rw [h5]
  ext1 i j
  rcases eq_or_ne i j with rfl | e <;> simp [*]

theorem continuous_pInfComp : Continuous (pInf E) := by
  have h : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_cInf : Continuous (cInf : UA E n → GL (Fin n) (Cinf E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map continuous_pInfComp)).comp continuous_subtype_val

theorem continuous_cutGL (v : InfinitePlace E) : Continuous (cutGL v : GL (Fin n) (Cinf E) → _) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (atPlace v : Cinf E → Cinf E) :=
    continuous_pi fun w => by
      by_cases h : w = v
      · subst h
        exact (show Continuous fun x : Cinf E => x w from continuous_apply w).congr
          fun x => (atPlace_self w x).symm
      · exact continuous_const.congr fun x => (atPlace_of_ne h x).symm
  exact continuous_const.sub (continuous_const) |>.add (continuous_id.matrix_map hs)

theorem continuous_infGL : Continuous (infGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) :=
    (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub (continuous_const) |>.add (continuous_id.matrix_map hs)

theorem coord_embedding (w : InfinitePlace E) : coord w.embedding = Pi.evalRingHom (fun _ => ℂ) w := by
  have h := InfinitePlace.mk_embedding w
  unfold coord
  rw [if_pos (by rw [h]), h]

theorem map_coord_of_evGL (τ : E →+* ℂ) {y : GL (Fin n) (Cinf E)} (h : evGL (InfinitePlace.mk τ) y = 1) :
    GeneralLinearGroup.map (coord τ) y = 1 := by
  unfold coord
  split_ifs
  · exact h
  · have : GeneralLinearGroup.map ((starRingEnd ℂ).comp (Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ))) y =
        GeneralLinearGroup.map (starRingEnd ℂ) (evGL (InfinitePlace.mk τ) y) := by
      ext i j
      rfl
    rw [this, h, map_one]

theorem evGL_cInf_of_mem {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) {w : InfinitePlace E}
    (h : w ≠ InfinitePlace.mk τ) : evGL w (cInf x) = 1 := by
  have h1 : x ∈ (cEmb (n := n) w.embedding).ker :=
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 w.embedding) (by rwa [InfinitePlace.mk_embedding])
  have h2 : GeneralLinearGroup.map (coord w.embedding) (cInf x) = 1 := MonoidHom.mem_ker.1 h1
  rwa [coord_embedding] at h2

def cutGA (τ : E →+* ℂ) : UA E n →* GA E n := (infGL E n).comp ((cutGL (InfinitePlace.mk τ)).comp cInf)

theorem cutGA_mem_UA (τ : E →+* ℂ) (g : UA E n) : cutGA τ g ∈ UA E n := by
  refine infGL_mem_UA (cutGL (InfinitePlace.mk τ) (cInf g)) ((unitary_iff_evGL _).2 fun w => ?_)
  by_cases h : w = InfinitePlace.mk τ
  · subst h
    rw [evGL_cutGL_self]
    exact (unitary_iff_evGL _).1 (cInf_unitary g) _
  · rw [evGL_cutGL_of_ne h]
    simp

theorem cInf_cutGA (τ : E →+* ℂ) (g : UA E n) :
    cInf (⟨cutGA τ g, cutGA_mem_UA τ g⟩ : UA E n) = cutGL (InfinitePlace.mk τ) (cInf g) :=
  pInf_infGL _

theorem cutGA_mem_embU (τ : E →+* ℂ) (g : UA E n) : (⟨cutGA τ g, cutGA_mem_UA τ g⟩ : UA E n) ∈ embU n τ := by
  refine ⟨pFin_infGL _, Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_⟩
  change GeneralLinearGroup.map (coord τ') (cInf _) = 1
  rw [cInf_cutGA]
  exact map_coord_of_evGL τ' (evGL_cutGL_of_ne h _)

def embRet (τ : E →+* ℂ) : UA E n →* embU n τ where
  toFun g := ⟨⟨cutGA τ g, cutGA_mem_UA τ g⟩, cutGA_mem_embU τ g⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (cutGA τ)))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul (cutGA τ) a b))

theorem cInf_embRet (τ : E →+* ℂ) (g : UA E n) :
    cInf (embRet τ g : UA E n) = cutGL (InfinitePlace.mk τ) (cInf g) := cInf_cutGA τ g

theorem continuous_embRet (τ : E →+* ℂ) : Continuous (embRet (n := n) τ) :=
  Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_infGL.comp ((continuous_cutGL _).comp continuous_cInf)) _) _

theorem embRet_apply (τ : E →+* ℂ) (x : embU n τ) : embRet τ (x : UA E n) = x := by
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · refine (cInf_embRet τ x.1).trans (gl_ext_evGL fun w => ?_)
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      exact evGL_cutGL_self _ _
    · rw [evGL_cutGL_of_ne h]
      exact (evGL_cInf_of_mem x.2 h).symm
  · exact (pFin_infGL _).trans (MonoidHom.mem_ker.1 x.2.1).symm

theorem commute_embRet (τ : E →+* ℂ) (g : UA E n) (y : embU n τ) :
    Commute ((embRet τ g : UA E n)⁻¹ * g) (y : UA E n) := by
  have h2 : GeneralLinearGroup.map (pFin E) y.1.1 = 1 := y.2.1
  have h1 : evGL (InfinitePlace.mk τ) (cInf ((embRet τ g : UA E n)⁻¹ * g)) = 1 := by
    rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, evGL_cutGL_self, inv_mul_cancel]
  generalize (embRet τ g : UA E n)⁻¹ * g = a at h1 ⊢
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * y.1) = cInf (y.1 * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      rw [h1, one_mul, mul_one]
    · rw [evGL_cInf_of_mem y.2 h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]

theorem exists_embRet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ),
    ∃ r : UA E n →* embU n τ, Continuous r ∧ (∀ x : embU n τ, r x = x) ∧
      ∀ (g : UA E n) (y : embU n τ), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) :=
  fun _ _ _ _ _ τ => ⟨embRet τ, continuous_embRet τ, embRet_apply τ, commute_embRet τ⟩

end GlobalTheory.DefU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedeanStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_retraction_onto_unitaryArchimedeanPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ), ∃ r : UA E n →* embU n τ, Continuous r ∧ (∀ x : embU n τ, r x = x) ∧ ∀ (g : UA E n) (y : embU n τ), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) := by
  first | exact @GlobalTheory.DefU.exists_embRet | exact GlobalTheory.DefU.exists_embRet | (intros; apply GlobalTheory.DefU.exists_embRet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CoefInv

open GlobalTheory.SplitScalar GlobalTheory.HeisOrtho

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f : WO S T → ℂ)
    (w : WO S T) : ℂ := ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ

theorem coef_right (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {f : WO S T → ℂ} {u : WO S T}
    (hu : heisO ψ S T u f = f) (w : WO S T) :
    coef ψ S T μ 𝓕 f w = ψ (symplOH S T w u) * coef ψ S T μ 𝓕 f (w + u) := by
  have h := heisO_heisO ψ S T w u f
  rw [hu] at h
  unfold coef
  rw [h, ← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem coef_left (hψ : IsCharAF D.host.F ψ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {u : WO S T}
    (hu : heisO ψ S T u f = f) (w : WO S T) :
    coef ψ S T μ 𝓕 f w = ψ (symplOH S T u w) * coef ψ S T μ 𝓕 f (w + u) := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
    (fun x => heisO ψ S T w f x * star (f x)) (by
      intro γ hγ x
      have h0 := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T γ x)))
      have h1 := heisO_quasi hf w γ hγ x
      have h2 := heisO_quasi hf 0 γ hγ x
      rw [heisO_zero] at h2
      show heisO ψ S T w f (γ + x) * (starRingEnd ℂ) (f (γ + x)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]
      rfl) u
  unfold coef
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h0 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T x u))
  have h1 : ψ (symplOH S T x u) * heisO ψ S T w f (x + u) = ψ (symplOH S T u w) * heisO ψ S T (u + w) f x :=
    congrFun (heisO_heisO ψ S T u w f) x
  have h2 : ψ (symplOH S T x u) * f (x + u) = f x := congrFun hu x
  show heisO ψ S T w f (x + u) * (starRingEnd ℂ) (f (x + u)) =
    ψ (symplOH S T u w) * (heisO ψ S T (w + u) f x * (starRingEnd ℂ) (f x))
  rw [← h2, add_comm w u, ← mul_assoc, ← h1, map_mul, mul_mul_mul_comm, h0, one_mul]

theorem char_eq_one (hψ : IsCharAF D.host.F ψ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {u : WO S T}
    (hu : heisO ψ S T u f = f) {w : WO S T} (hw : coef ψ S T μ 𝓕 f w ≠ 0) : ψ (symplO S T w u) = 1 := by
  have h1 := coef_right μ 𝓕 hu w
  have h2 := coef_left hψ hμ h𝓕 hf hu w
  have h3 : coef ψ S T μ 𝓕 f (w + u) ≠ 0 := fun h => hw (by rw [h1, h, mul_zero])
  have h4 := mul_right_cancel₀ h3 (h1.symm.trans h2)
  rw [← symplOH_add_self, AddChar.map_add_eq_mul]
  nth_rewrite 2 [h4]
  rw [← AddChar.map_add_eq_mul, symplOH_skew S T w u, add_neg_cancel, AddChar.map_zero_eq_one]

theorem nsmul_cancel {m n : ℕ} {N : ℕ} (hN : 0 < N) {x y : Mx D m n} (h : N • x = N • y) : x = y := by
  have hu : IsUnit (N : AE D) := by
    have h1 : IsUnit (N : D.host.F) := (Nat.cast_ne_zero.2 hN.ne').isUnit
    have h2 := (h1.map (algebraMap D.host.F (AF D.host.F))).map (algebraMap (AF D.host.F) (AE D))
    rwa [map_natCast, map_natCast] at h2
  refine Matrix.ext fun i j => hu.mul_left_cancel ?_
  have h3 : N • x i j = N • y i j := congrFun (congrFun h i) j
  rwa [nsmul_eq_mul, nsmul_eq_mul] at h3

theorem symplO_nsmul (N : ℕ) (x y : WO S T) : symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := symplO_smul S T (N : AE D) x y
  rwa [map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h

theorem real_part (w : WO S T) : (realIdem D • w).map (finPart D) = 0 := by
  funext i j
  show finPart D (realIdem D * w i j) = 0
  rw [RingHom.map_mul, finPart_realIdem, zero_mul]

theorem fin_part (w : WO S T) : (w - realIdem D • w).map (infPart D) = 0 := by
  funext i j
  show infPart D (w i j - realIdem D * w i j) = 0
  rw [RingHom.map_sub, RingHom.map_mul, infPart_realIdem, one_mul, sub_self]

theorem actO_real {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T) {u : WO S T}
    (hu : u.map (finPart D) = 0) : actO S T g h u = u := by
  have h1 : (Formalism.L2.Theta.mt T h).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  have h2 : (Formalism.L2.Theta.mt S g⁻¹).map (infPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h3 : (actO S T g h u).map (infPart D) = u.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : (actO S T g h u).map (finPart D) = u.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]
  exact Matrix.ext fun i j => adele_ext (congrFun (congrFun h3 i) j) (congrFun (congrFun h4 i) j)

theorem eventually_mod (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p : GA D S × GA D T in 𝓝 1, ∀ x ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
      (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), actO S T p.1 p.2 x = x + N • l := by
  obtain ⟨G, hG, hGl, hgen⟩ := GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT
  have h := (Filter.eventually_all_finite hG).2 fun u hu =>
    GlobalTheory.LatNhds.eventually_move S T ΛS ΛT hS hT u (latO_fin (hGl u hu)) N hN
  filter_upwards [h] with p hp
  intro w hw
  have key := hgen (((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True).map (nsmulAddMonoidHom N)).comap (GlobalTheory.LatLevel.actHom S T p.1 p.2 - AddMonoidHom.id _))
    (fun α hα u hu => ?_) w hw
  · obtain ⟨l, hl, e⟩ := key
    refine ⟨l, hl, ?_⟩
    have e' : N • l = actO S T p.1 p.2 w - w := e
    rw [e', add_sub_cancel]
  · obtain ⟨l, hl, e⟩ := hp u hu
    refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l,
      GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩) _ hl, ?_⟩
    show N • (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • l) =
      actO S T p.1 p.2 (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u) -
        algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) • u
    rw [GlobalTheory.LatNhds.actO_smul, e, smul_add, add_sub_cancel_left, smul_comm]

theorem eventually_coef_of_ne (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w,
      coef ψ S T μ 𝓕 f w ≠ 0 → coef ψ S T μ 𝓕 f (actO S T p.1 p.2 w) = coef ψ S T μ 𝓕 f w := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨N, hN, hNU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  have hfix := fun u hu => hUf _ (hNU u hu) (latO_fin (AddSubgroup.nsmul_mem _ hu N))
  filter_upwards [eventually_mod _ _ hS hT (N * (2 * N)) (by positivity)] with p hp hg hh w hw
  have hfin : (N • (w - realIdem D • w)).map (infPart D) = 0 := by
    rw [GlobalTheory.LatNhds.fin_iff, smul_comm, GlobalTheory.LatNhds.fin_iff.1 (fin_part w), nsmul_zero]
  have hmem := GlobalTheory.LatVac.mem_of_char hψ hS hT hfin fun u hu => by
    rw [symplO_nsmul, symplO_sub_left, symplO_real_fin S T (real_part w) (latO_fin (AddSubgroup.nsmul_mem _ hu N)),
      sub_zero]
    exact char_eq_one hψ.1 hμ h𝓕 hf (hfix u hu) hw
  obtain ⟨l, hl, e⟩ := hp _ hmem
  have e1 : actO S T p.1 p.2 (w - realIdem D • w) = (w - realIdem D • w) + (2 * N) • l := by
    refine nsmul_cancel hN ?_
    rw [nsmul_add, ← mul_nsmul', ← e]
    exact (map_nsmul (GlobalTheory.LatLevel.actHom S T p.1 p.2) N _).symm
  have e2 : actO S T p.1 p.2 w = w + N • (l + l) := by
    have h := GlobalTheory.LatNhds.actO_add p.1 p.2 (realIdem D • w) (w - realIdem D • w)
    rw [e1, actO_real hg hh (real_part w), ← add_assoc, add_sub_cancel] at h
    rw [h, ← two_nsmul, ← mul_nsmul]
  have h1 := coef_right μ 𝓕 (hfix _ (AddSubgroup.add_mem _ hl hl)) w
  rw [nsmul_add, symplOH_add_right, symplOH_add_self, char_eq_one hψ.1 hμ h𝓕 hf (hfix l hl) hw, one_mul,
    ← nsmul_add] at h1
  rw [e2, ← h1]

theorem eventually_coef_actO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w, ∫ x in 𝓕, heisO ψ S T (actO S T p.1 p.2 w) f x * star (f x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 f hf
  have h1 := eventually_coef_of_ne hψ hμ h𝓕 hf
  haveI : ∀ V : HSp D, IsTopologicalGroup (GA D V) := fun V => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have ht : Filter.Tendsto (fun p : GA D S × GA D T => p⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := GA D S × GA D T)).tendsto 1
    rwa [inv_one] at this
  filter_upwards [h1, ht.eventually h1] with p hp hp' hg hh w
  show coef ψ S T μ 𝓕 f (actO S T p.1 p.2 w) = coef ψ S T μ 𝓕 f w
  by_cases hw : coef ψ S T μ 𝓕 f w = 0
  · by_contra hne
    have h2 := hp' (inv_mem hg) (inv_mem hh) _ (hw ▸ hne)
    have h3 := GlobalTheory.AdelicLatMove.actO_actO_inv S T p.1⁻¹ p.2⁻¹ w
    rw [inv_inv, inv_inv] at h3
    exact hne (h2.symm.trans (congrArg _ h3))
  · exact hp hg hh w hw

end GlobalTheory.Mem.CoefInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyWeilMatrixCoeffFinitePointInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_weilMatrixCoeff_finitePoint_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ᶠ p : GA D S × GA D T in 𝓝 1, p.1 ∈ GfC S → p.2 ∈ GfC T → ∀ w, ∫ x in 𝓕, heisO ψ S T (actO S T p.1 p.2 w) f x * star (f x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ := by
  first | exact @GlobalTheory.Mem.CoefInv.eventually_coef_actO | exact GlobalTheory.Mem.CoefInv.eventually_coef_actO | (intros; apply GlobalTheory.Mem.CoefInv.eventually_coef_actO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZero
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

namespace GlobalTheory.BijPointsIso

universe u

variable {X Y : Scheme.{u}}

theorem universallyInjective_of_injective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    UniversallyInjective f := by
  rw [UniversallyInjective.iff_diagonal, surjective_iff]
  intro z
  let K := AlgebraicClosure ((pullback f f).residueField z)
  let φ : Spec (.of K) ⟶ pullback f f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField z) K)) ≫
      (pullback f f).fromSpecResidueField z
  have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
    h K (by simp only [Category.assoc, pullback.condition])
  have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f := by
    apply pullback.hom_ext <;> simp [hφ₁]
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨(φ ≫ pullback.fst f f) pt, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem surjective_of_surjective_algClosed (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K],
      Function.Surjective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f)) :
    Function.Surjective f := by
  intro y
  let K := AlgebraicClosure (Y.residueField y)
  obtain ⟨g, hg⟩ := h K (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫
    Y.fromSpecResidueField y)
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  refine ⟨g pt, ?_⟩
  rw [← Scheme.Hom.comp_apply]
  simp only at hg
  rw [hg, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem bijective_residue_of_isField {R : Type*} [CommRing R] [IsLocalRing R] (hR : IsField R) :
    Function.Bijective (IsLocalRing.residue R) := by
  refine ⟨fun a b e ↦ ?_, Ideal.Quotient.mk_surjective⟩
  change Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b at e
  rw [Ideal.Quotient.eq, IsLocalRing.isField_iff_maximalIdeal_eq.mp hR, Ideal.mem_bot,
    sub_eq_zero] at e
  exact e

theorem isIso_stalkMap_genericPoint (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [UniversallyInjective f] [IsDominant f]
    (hc : CharZero (Y.residueField (f (genericPoint X)))) :
    IsIso (f.stalkMap (genericPoint X)) := by
  set x := genericPoint X
  have h3 : Function.Injective f ∧ ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective.{u} f).out 1 3).mp ‹_›
  have hpi := h3.2 x
  have hr : Function.Bijective (f.residueFieldMap x) := by
    algebraize [(f.residueFieldMap x).hom]
    have : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) := hpi
    exact IsPurelyInseparable.bijective_algebraMap_of_isSeparable _ _
  have hX : IsField (X.presheaf.stalk x) := Field.toIsField X.functionField
  have hY : IsField (Y.presheaf.stalk (f x)) := by
    rw [GlobalTheory.apply_genericPoint_of_isDominant f]
    exact Field.toIsField Y.functionField
  have hsq := Scheme.residue_residueFieldMap f x
  have hsq' : ∀ a, X.residue x (f.stalkMap x a) = f.residueFieldMap x (Y.residue (f x) a) :=
    fun a ↦ (congrArg (fun g ↦ g.hom a) hsq).symm
  have bX := bijective_residue_of_isField hX
  have bY := bijective_residue_of_isField hY
  rw [ConcreteCategory.isIso_iff_bijective]
  have : Function.Bijective (X.residue x ∘ f.stalkMap x) := by
    have e : (X.residue x ∘ f.stalkMap x) = (f.residueFieldMap x ∘ Y.residue (f x)) := funext hsq'
    rw [e]; exact hr.comp bY
  exact (Function.Bijective.of_comp_iff' bX _).mp this

end GlobalTheory.BijPointsIso

namespace GlobalTheory.BijPointsIso

theorem charZero_residueField {F : Type} [Field F] [CharZero F] (Y : Var F) (y : Y.X) :
    CharZero (Y.X.residueField y) := by
  let ψ : F →+* Y.X.residueField y :=
    (Y.X.residue y).hom.comp ((Y.X.presheaf.germ ⊤ y trivial).hom.comp (algebraMap F Γ(Y.X, ⊤)))
  exact charZero_of_injective_ringHom ψ.injective

theorem isIso_of_bijective_points : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F)
    (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str →
      (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) →
        IsIso h := by
  intro F _ _ Y₁ Y₂ h hc hb
  have : UniversallyInjective h :=
    universallyInjective_of_injective_algClosed h fun K _ _ ↦ (hb K).1
  have : IsProper (h ≫ Y₂.str) := hc ▸ inferInstance
  have : IsProper h := IsProper.of_comp h Y₂.str
  have hs : Function.Surjective h := surjective_of_surjective_algClosed h fun K _ _ ↦ (hb K).2
  have : IsDominant h := ⟨hs.denseRange⟩
  have := isIso_stalkMap_genericPoint h (charZero_residueField Y₂ _)
  have hN := Y₂.isNormalScheme
  exact GlobalTheory.isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap h hN.isIntegrallyClosed_stalk

end GlobalTheory.BijPointsIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZeroStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F) (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str → (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) → IsIso h := by
  first | exact @GlobalTheory.BijPointsIso.isIso_of_bijective_points | exact GlobalTheory.BijPointsIso.isIso_of_bijective_points | (intros; apply GlobalTheory.BijPointsIso.isIso_of_bijective_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCCRXOpDOp
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculusStatement
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergSmoothVector_derivative_calculus : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  first | exact @GlobalTheory.Mem.Lift.DCalc.dH_calculus | exact GlobalTheory.Mem.Lift.DCalc.dH_calculus | (intros; apply GlobalTheory.Mem.Lift.DCalc.dH_calculus <;> assumption)
end

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.Ccr

theorem comm_comb {A : Type} [Ring A] [Algebra ℂ A] (p p' q q' : A) (s t c₁ c₂ c₃ c₄ : ℂ)
    (h₁ : p * q = q * p + c₁ • (1 : A)) (h₂ : p * q' = q' * p + c₂ • (1 : A))
    (h₃ : p' * q = q * p' + c₃ • (1 : A)) (h₄ : p' * q' = q' * p' + c₄ • (1 : A)) :
    (p + s • p') * (q + t • q') = (q + t • q') * (p + s • p') + (c₁ + t * c₂ + s * c₃ + s * t * c₄) • (1 : A) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h₁, h₂, h₃, h₄]
  module

theorem exists_om {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) :
    ∃ om : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ, ∀ x y, om x y = (star y ⬝ᵥ H *ᵥ x).im := by
  let b : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
    (fun x x' y => by simp [mulVec_add, dotProduct_add])
    (fun r x y => by simp [mulVec_smul, dotProduct_smul])
    (fun x y y' => by simp [add_dotProduct])
    (fun r x y => by simp [smul_dotProduct])
  exact ⟨LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ b), fun x y => rfl⟩

theorem im_self {ι : Type} [Fintype ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (x : ι → ℂ) :
    (star x ⬝ᵥ H *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ H *ᵥ x) = star x ⬝ᵥ H *ᵥ x := by
    rw [← star_dotProduct_star, star_star, star_mulVec, hH, dotProduct_mulVec]
  exact Complex.conj_eq_iff_im.mp h

theorem pair_inv {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (k l : ι) :
    star (H⁻¹ *ᵥ Pi.single l 1) ⬝ᵥ H *ᵥ Pi.single k 1 = if k = l then (1 : ℂ) else 0 := by
  rw [star_mulVec, conjTranspose_nonsing_inv, hH, ← dotProduct_mulVec, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), one_mulVec, dotProduct_single]
  by_cases h : k = l <;> simp [h]

end GlobalTheory.Mem.Lift.Ccr


open GlobalTheory.Mem.Lift.Ccr in
theorem GlobalTheory.Mem.Lift.exists_isCCR_xOp_dOp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∃ x d : ι → Module.End ℂ (smS ρ), (∀ k f, (x k f).1 = xOp ρ k f.1) ∧ (∀ k f, (d k f).1 = dOp ρ H k f.1) ∧ IsCCR x d := by
  intro ι _ _ H hH hd B _ _ ρ hρ
  obtain ⟨om, hom⟩ := exists_om H
  have hρ' : IsHeis (fun x y => om x y) ρ := by simpa only [hom] using hρ
  have key := GlobalTheory.T.heisenbergSmoothVector_derivative_calculus (ι → ℂ) B om ρ (fun x => by rw [hom, im_self hH]) hρ'
  let D : (ι → ℂ) → Module.End ℂ (smS ρ) := fun v =>
    { toFun := fun f => ⟨dH ρ v f.1, (key f.1 f.2).1 v⟩
      map_add' := fun f g => Subtype.ext (dH_add v f.2 g.2)
      map_smul' := fun a f => Subtype.ext (dH_smul v a f.2) }
  have hD : ∀ u v, D u * D v = D v * D u + (2 * π * I * ((star v ⬝ᵥ H *ᵥ u).im : ℂ)) • (1 : Module.End ℂ (smS ρ)) := by
    intro u v
    refine LinearMap.ext fun f => Subtype.ext ?_
    have := (key f.1 f.2).2.2.2.2 u v
    rw [hom, sub_eq_iff_eq_add'] at this
    exact this
  have hc : ∀ (u v : ι → ℂ) (s t : ℂ), (D u + s • D (I • u)) * (D v + t • D (I • v)) =
      (D v + t • D (I • v)) * (D u + s • D (I • u)) +
        (2 * π * I * ((1 + s * t) * (star v ⬝ᵥ H *ᵥ u).im + (s - t) * (star v ⬝ᵥ H *ᵥ u).re)) •
          (1 : Module.End ℂ (smS ρ)) := by
    intro u v s t
    rw [comm_comb _ _ _ _ s t _ _ _ _ (hD u v) (hD u (I • v)) (hD (I • u) v) (hD (I • u) (I • v))]
    congr 2
    simp only [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    simp
    ring
  have hII : (1 : ℂ) + I * I = 0 := by simp
  refine ⟨fun k => D (Pi.single k 1) + (-I) • D (I • Pi.single k 1),
    fun l => (-(1 / (4 * π)) : ℂ) • (D (H⁻¹ *ᵥ Pi.single l 1) + I • D (I • H⁻¹ *ᵥ Pi.single l 1)),
    fun k f => ?_, fun k f => rfl, fun k l => ?_, fun k l => ?_, fun k l => ?_⟩
  · rw [xOp, sub_eq_add_neg, ← neg_smul]
    rfl
  · beta_reduce
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc]
    simp
  · simp only [smul_mul_assoc, mul_smul_comm]
    rw [hc (Pi.single k 1), pair_inv hH hd, ← smul_sub, sub_add_cancel_left, ← neg_smul, smul_smul]
    by_cases h : k = l
    · simp only [h, if_true, one_im, one_re, ofReal_zero, ofReal_one]
      have hp : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      have : (-(1 / (4 * π)) : ℂ) * -(2 * π * I * ((1 + -I * I) * 0 + (-I - I) * 1)) = 1 := by
        field_simp
        linear_combination (-4) * hII
      rw [this, one_smul]
    · simp [h]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctions
noncomputable section

namespace GlobalTheory.Mem.Lift.ThOps

theorem exists_restrict {Θ M : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M] (j : Θ →ₗ[ℂ] M)
    (hj : Function.Injective j) (A : Module.End ℂ M) (hA : ∀ f, ∃ g, j g = A (j f)) :
    ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = A (j f) := by
  choose a ha using hA
  exact ⟨{ toFun := a
           map_add' := fun f g => hj (by simp only [map_add (f := _), ha])
           map_smul' := fun c f => hj (by simp only [map_smul, ha, RingHom.id_apply]) }, ha⟩

theorem isCCR_restrict {Θ M κ : Type} [DecidableEq κ] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M]
    (j : Θ →ₗ[ℂ] M) (hj : Function.Injective j) {x d : κ → Module.End ℂ Θ} {x₀ d₀ : κ → Module.End ℂ M}
    (hx : ∀ k f, j (x k f) = x₀ k (j f)) (hd : ∀ k f, j (d k f) = d₀ k (j f)) (h : GlobalTheory.Mem.Lift.IsCCR x₀ d₀) :
    GlobalTheory.Mem.Lift.IsCCR x d := by
  refine ⟨fun k l => LinearMap.ext fun f => hj ?_, fun k l => LinearMap.ext fun f => hj ?_,
    fun k l => LinearMap.ext fun f => hj ?_⟩
  · simpa only [Module.End.mul_apply, hx] using LinearMap.congr_fun (h.1 k l) (j f)
  · simpa only [Module.End.mul_apply, hd] using LinearMap.congr_fun (h.2.1 k l) (j f)
  · have := LinearMap.congr_fun (h.2.2 k l) (j f)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hx, hd] at this ⊢
    rw [this]
    split_ifs <;> simp


open Matrix GlobalTheory.RealWeil in
theorem exists_ops {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B)
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) {Θ : Type} [AddCommGroup Θ] [Module ℂ Θ] (J : Θ →ₗ[ℂ] B)
    (hJ : Function.Injective J) (hs : ∀ f, Sm ρ (J f)) (hk : ∀ v f, ∃ g, J g = dH ρ v (J f)) :
    ∃ x d : ι → Module.End ℂ Θ, IsCCR x d ∧
      ∀ (X : Matrix ι ι ℂ) (f : Θ), J ((∑ k, ∑ l, X k l • (x k * d l)) f) = nOp ρ H X (J f) := by
  obtain ⟨x₀, d₀, hx₀, hd₀, hc⟩ := exists_isCCR_xOp_dOp ι H hH hd B ρ hρ
  let j : Θ →ₗ[ℂ] smS ρ := J.codRestrict _ hs
  have hj : Function.Injective j := fun f g e => hJ (congrArg Subtype.val e)
  have h1 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = x₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • Pi.single k 1) f
    refine ⟨g₁ - Complex.I • g₂, Subtype.ext ?_⟩
    rw [hx₀]
    change J _ = xOp ρ k (J f)
    rw [xOp, map_sub, map_smul, e₁, e₂]
  have h2 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = d₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (H⁻¹ *ᵥ Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • H⁻¹ *ᵥ Pi.single k 1) f
    refine ⟨(-(1 / (4 * Real.pi)) : ℂ) • (g₁ + Complex.I • g₂), Subtype.ext ?_⟩
    rw [hd₀]
    change J _ = dOp ρ H k (J f)
    rw [dOp, map_smul, map_add (f := _), map_smul, e₁, e₂]
  choose x hx using h1
  choose d hd' using h2
  refine ⟨x, d, isCCR_restrict j hj hx hd' hc, fun X f => ?_⟩
  have ex : ∀ k f, J (x k f) = xOp ρ k (J f) := fun k f => (congrArg Subtype.val (hx k f)).trans (hx₀ k _)
  have ed : ∀ k f, J (d k f) = dOp ρ H k (J f) := fun k f => (congrArg Subtype.val (hd' k f)).trans (hd₀ k _)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [nOp, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul, ex, ed]

end GlobalTheory.Mem.Lift.ThOps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


open GlobalTheory.RealWeil in
theorem GlobalTheory.Mem.Lift.exists_isCCR_theta : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  intro D θ σ h ψ hψ S T
  let J : thetaSub ψ S T →ₗ[ℂ] BB ψ S T :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO S T → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ S T (J f).1 := fun f => (hc f).symm ▸ f.2
  have hs : ∀ f, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) (J f) := fun f => sm_of_theta h hψ _ (ht f)
  have hk : ∀ v f, ∃ g, J g = dH (rhoV hψ σ S T) v (J f) := by
    intro v f
    obtain ⟨F', hF', hd⟩ := exists_deriv h hψ (J f) (ht f) v
    refine ⟨⟨F'.1, hF'⟩, QB_ext fun w => ?_⟩
    rw [hc]
    exact (hd w).unique (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (hs f)))
  obtain ⟨x, d, hxd, hn⟩ := ThOps.exists_ops (HM S T) HM_herm HM_det (rhoV hψ σ S T) (isHeis_rhoB h hψ) J hJ hs hk
  refine ⟨x, d, hxd, fun X f F hF => ?_⟩
  have e : F = J f := QB_ext fun w => by rw [hF, hc]
  rw [e, ← hn, hc]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ccr_operators_thetaFunctions : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  first | exact @GlobalTheory.Mem.Lift.exists_isCCR_theta | exact GlobalTheory.Mem.Lift.exists_isCCR_theta | (intros; apply GlobalTheory.Mem.Lift.exists_isCCR_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetCharEqOneOfHasWt
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.NonTriv

section Char

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unit (k : Eˣ) (hk : GlobalTheory.Mem.Chr.diagUnits E k ∈ unitIdl E) : ∃ u : (𝓞 E)ˣ, ((u : 𝓞 E) : E) = k := by
  have hv : ∀ x : Eˣ, GlobalTheory.Mem.Chr.diagUnits E x ∈ unitIdl E → ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (x : E) ≤ 1 :=
    fun x hx v => by rw [← GlobalTheory.Mem.Chr.AntiExist.val_diag v x, hx v]
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) (k : E) (hv k hk)
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) ((k⁻¹ : Eˣ) : E)
    (hv k⁻¹ (inv_mem hk))
  have hab : a * b = 1 := RingOfIntegers.ext (by
    change algebraMap (𝓞 E) E (a * b) = algebraMap (𝓞 E) E 1
    rw [map_mul, ha, hb, map_one, Units.mul_inv])
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

end Char

section Char

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


end Char

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.DefU.NonTriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFundamentalDomainIsometryTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFundamentalDomainIsometryTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Isom

theorem haar_fd_phi : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  intro D V V' I S μ 𝓕 hμ h𝓕
  haveI hB : BorelSpace (WO S V) := ⟨rfl⟩
  haveI hB' : BorelSpace (WO S V') := ⟨rfl⟩
  have hc := I.continuous_phi S
  have hcs := I.continuous_phi_symm S
  have hrat : ∀ x, I.phi S x ∈ ratL V' S ↔ x ∈ ratL V S := by
    intro x
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨I.Q * z, ?_⟩
      have h1 := I.symm.phi_ratW S z
      have h2 : ratW V' S z = I.phi S x := hz
      rw [h2, ← I.phi_symm_apply, AddEquiv.symm_apply_apply] at h1
      exact h1.symm
    · rintro ⟨z, hz⟩
      refine ⟨I.P * z, ?_⟩
      have h1 := I.phi_ratW S z
      have h2 : ratW V S z = x := hz
      rw [h2] at h1
      exact h1.symm
  let m : WO S V ≃ᵐ WO S V' :=
    { toEquiv := (I.phi S).toEquiv
      measurable_toFun := hc.measurable
      measurable_invFun := hcs.measurable }
  have hmp : MeasurePreserving m (μ.map m.symm) μ :=
    (MeasurePreserving.symm m.symm ⟨m.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving (I.phi S) (μ.map (I.phi S).symm) μ := hmp
  refine ⟨μ.map (I.phi S).symm, I.phi S ⁻¹' 𝓕, AddEquiv.isAddHaarMeasure_map μ (I.phi S).symm hcs (by simpa using hc), ?_, ?_⟩
  · let f : ratL V' S → ratL V S := fun y => ⟨(I.phi S).symm y, (hrat _).1 (by simpa using y.2)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext ((I.phi S).symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨I.phi S x, (hrat _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  · intro u
    have := hmp'.setLIntegral_comp_preimage_emb m.measurableEmbedding (fun b => u ((I.phi S).symm b)) 𝓕
    simpa using this.symm

end GlobalTheory.Mem.Isom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFundamentalDomainIsometryTransportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_isometryTransport : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  first | exact @GlobalTheory.Mem.Isom.haar_fd_phi | exact GlobalTheory.Mem.Isom.haar_fd_phi | (intros; apply GlobalTheory.Mem.Isom.haar_fd_phi <;> assumption)
end
end
