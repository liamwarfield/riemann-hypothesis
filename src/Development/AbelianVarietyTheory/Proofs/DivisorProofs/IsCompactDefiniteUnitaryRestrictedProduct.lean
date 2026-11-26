module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ParabolicAtStandardWeylElement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairMovesPhasedHeisenbergTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem continuous_mapLoc (w : Pl E) : Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) :=
  Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))

omit [IsCMField E] in
theorem entry_mem_of_mem_KGL {w : Pl E} {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    g.val i j ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
  obtain ⟨k, rfl⟩ := hg
  exact (k.val i j).2


omit [IsCMField E] in
theorem isCompact_box (D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E))) (hD : ∀ w, IsCompact (D w))
    (hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w (n := n)) :
    IsCompact {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
  let Q : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) '' D w
  let Q' : Fin n → Fin n → ∀ w : Pl E, Set (w.adicCompletion E) := fun i j w =>
    (fun g : GL (Fin n) (w.adicCompletion E) => (g⁻¹).val i j) '' D w
  have hQ : ∀ i j w, IsCompact (Q i j w) := fun i j w =>
    (hD w).image (Units.continuous_val.matrix_elem i j)
  have hQ' : ∀ i j w, IsCompact (Q' i j w) := fun i j w =>
    (hD w).image (Units.continuous_coe_inv.matrix_elem i j)
  have hQK : ∀ i j, ∀ᶠ w in cofinite, Q i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL (hw hg) i j
  have hQK' : ∀ i j, ∀ᶠ w in cofinite, Q' i j w ⊆ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    fun i j => hDK.mono fun w hw => by
      rintro _ ⟨g, hg, rfl⟩
      exact entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL w (n := n)).inv_mem (hw hg)) i j
  let P : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q i j w}
  let P' : Set (Matrix (Fin n) (Fin n) (Af E)) :=
    Set.univ.pi fun i => Set.univ.pi fun j => {a : Af E | ∀ w, a w ∈ Q' i j w}
  have hP : IsCompact P := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q i j) (hQ i j) (hQK i j)
  have hP' : IsCompact P' := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    GlobalTheory.IdeleCyl.isCompact_restrictedProduct_forall_mem (fun w : Pl E => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Q' i j) (hQ' i j) (hQK' i j)
  have hC : IsClosed {g : GL (Fin n) (Af E) | ∀ w, GeneralLinearGroup.map (pLoc E w) g ∈ D w} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun w => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact (hD w).isClosed.preimage (continuous_mapLoc w)
  refine IsCompact.of_isClosed_subset (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hP.prod (hP'.image MulOpposite.continuous_op))) hC ?_
  intro g hg
  refine ⟨fun i _ j _ w => ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, rfl⟩, ⟨(g⁻¹ : GL (Fin n) (Af E)).val, fun i _ j _ w => ?_, rfl⟩⟩
  refine ⟨GeneralLinearGroup.map (pLoc E w) g, hg w, ?_⟩
  show ((GeneralLinearGroup.map (pLoc E w) g)⁻¹ : GL (Fin n) (w.adicCompletion E)).val i j = _
  rw [← map_inv]
  rfl

end GlobalTheory.BCT.LocCpt

namespace GlobalTheory.BCT.LocCpt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_GLint_of_entries' {K : Type} [Field K] (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_or_conj_mem {S : Set (Pl E)} (hS : IsSection S) (w : Pl E) :
    w ∈ S ∨ conjSrc (GlobalTheory.SplitPts.conjE E) w ∈ S := by
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
  by_cases hw : IsSplitAt w
  · rcases (GlobalTheory.SplitPts.over_split hw).2.2 u hu with rfl | rfl
    · exact Or.inl huS
    · exact Or.inr huS
  · left
    by_contra hwS
    exact hw ⟨u, fun h => hwS (h ▸ huS), hu⟩

theorem cLoc_eq_invT (x : UA E n) (w : Pl E) :
    cLoc w x = invT n _ (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
      (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)) := by
  set Y := GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x)
  have h : (Y.val)ᵀ * (cLoc w x).val = 1 := GlobalTheory.SplitPts.comp_eq x w
  apply Units.ext
  show (cLoc w x).val = ((Y⁻¹).val)ᵀ
  calc (cLoc w x).val = ((Y⁻¹).val)ᵀ * ((Y.val)ᵀ * (cLoc w x).val) := by
        rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mul]
    _ = ((Y⁻¹).val)ᵀ := by rw [h, Matrix.mul_one]

end GlobalTheory.BCT.LocCpt


open GlobalTheory.BCT.LocCpt in
theorem GlobalTheory.BCT.LocCpt.loc_cpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E),
    IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) →
    IsCompact {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  intro E _ _ _ hU n S hS C hC hCK
  set c := GlobalTheory.SplitPts.conjE E
  let φ : ∀ w : Pl E, GL (Fin n) ((conjSrc c w).adicCompletion E) → GL (Fin n) (w.adicCompletion E) :=
    fun w g => invT n _ (GeneralLinearGroup.map (conjLoc c w) g)
  have hφ : ∀ w, Continuous (φ w) := fun w => (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec c w).1))
  let D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E)) := fun w =>
    if w ∈ S then Subtype.val '' C w else φ w '' (Subtype.val '' C (conjSrc c w))
  have hD : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ S
    · simp only [D, if_pos hw]; exact (hC w).image continuous_subtype_val
    · simp only [D, if_neg hw]; exact ((hC _).image continuous_subtype_val).image (hφ w)
  have hDK : ∀ᶠ w in cofinite, D w ⊆ GlobalTheory.LFun.KGL w (n := n) := by
    have h1 : ∀ᶠ w in cofinite, C (conjSrc c w) = KL n (conjSrc c w) :=
      (conjSrc_injective c).tendsto_cofinite.eventually hCK
    filter_upwards [hCK, h1] with w hw hw'
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS, hw]
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hk
    · simp only [D, if_neg hwS, hw']
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have hk' : (k : GL (Fin n) _) ∈ GlobalTheory.LFun.KGL (conjSrc c w) (n := n) := Subgroup.mem_subgroupOf.1 hk
      have hO : ∀ y, y ∈ ((conjSrc c w).adicCompletionIntegers E : Set _) →
          conjLoc c w y ∈ (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := fun y hy => by
        rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec c w).2.2 y]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hy
      apply mem_GLint_of_entries'
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL ((GlobalTheory.LFun.KGL _ (n := n)).inv_mem hk') b a)
      · intro a b
        exact hO _ (entry_mem_of_mem_KGL hk' b a)
  have hB := isCompact_box D hD hDK

  have hmem : ∀ (x : finU (E := E) (n := n)) (w : Pl E), toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w ↔
      cLoc w (x : UA E n) ∈ Subtype.val '' C w := by
    intro x w
    have hx := GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w (x : UA E n)
    rw [toSub, dite_eq_left hx]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨k, hk, e⟩
      have : k = ⟨_, hx⟩ := Subtype.ext e
      rwa [← this]
  have hclosed : IsClosed {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
    simp only [hmem, Set.setOf_forall]
    refine isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    haveI : T2Space (GL (Fin n) (w.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact ((hC w).image continuous_subtype_val).isClosed.preimage
      ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val)

  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  have hfc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    haveI : T2Space (GL (Fin n) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
    have hc := GlobalTheory.CuspRep.ContAut.continuous_map_pInf E n
    exact isClosed_eq (hc.comp continuous_subtype_val) continuous_const
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hfc.isClosedEmbedding_subtypeVal
  refine IsCompact.of_isClosed_subset (hι.isCompact_preimage (hB.image GlobalTheory.DefU.LocAdm.continuous_finGL)) hclosed ?_
  intro x hx
  refine ⟨GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n), fun w => ?_, ?_⟩
  · have e : ∀ u : Pl E, GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) ((x : UA E n) : GA E n)) =
        cLoc u (x : UA E n) := fun u => Units.ext rfl
    rw [e]
    by_cases hwS : w ∈ S
    · simp only [D, if_pos hwS]
      exact (hmem x w).1 (hx w hwS)
    · simp only [D, if_neg hwS]
      have hw' := (mem_or_conj_mem hS w).resolve_left hwS
      refine ⟨cLoc (conjSrc c w) (x : UA E n), (hmem x _).1 (hx _ hw'), ?_⟩
      exact (cLoc_eq_invT (x : UA E n) w).symm
  · have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E n) : GA E n) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProductStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_definiteUnitary_restricted_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) → IsCompact {x : finU (E := E) (n := n) | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  first | exact @GlobalTheory.BCT.LocCpt.loc_cpt | exact GlobalTheory.BCT.LocCpt.loc_cpt | (intros; apply GlobalTheory.BCT.LocCpt.loc_cpt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExists
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem conj_embK {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  show conjEmb τ ((H.bar z : 𝓞 E) : E) = τ (z : E)
  rw [H.bar_eq]
  simp [conjEmb, IsCMField.complexEmbedding_complexConj]

private theorem exists_sum_wedge_local {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (a b : Fin n → M), ∑ k, exteriorPower.ιMulti R 2 ![a k, b k] = w := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, a, b, rfl⟩ := hx
    obtain ⟨m, c, d, rfl⟩ := hy
    refine ⟨n + m, Fin.append a c, Fin.append b d, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r x _ hx =>
    obtain ⟨n, a, b, rfl⟩ := hx
    refine ⟨n, fun k ↦ r • a k, b, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • a k, b k] : Fin 2 → M) = Function.update ![a k, b k] 0 (r • ![a k, b k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

private theorem mem_of_annihilates_local {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ψ : LinearMap.BilinForm K V) [hψ : ψ.IsPerfPair] (F : Submodule K V)
    (hiso : ∀ f ∈ F, ∀ g ∈ F, ψ f g = 0) (hdim : 2 * Module.finrank K F = Module.finrank K V) (f : V)
    (hf : ∀ g ∈ F, ψ f g = 0) : f ∈ F := by
  let Φ : V →ₗ[K] Module.Dual K F := F.subtype.dualMap ∘ₗ ψ
  have hΦ : Function.Surjective Φ :=
    (LinearMap.dualMap_surjective_of_injective F.injective_subtype).comp hψ.bijective_left.2
  have hker : F ≤ LinearMap.ker Φ := fun f hf' ↦ LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ hiso f hf' g g.2)
  have hr := LinearMap.finrank_range_add_finrank_ker Φ
  rw [LinearMap.range_eq_top.2 hΦ, finrank_top, Subspace.dual_finrank_eq] at hr
  have heq : F = LinearMap.ker Φ := Submodule.eq_of_le_of_finrank_eq hker (by omega)
  rw [heq]
  exact LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ hf g g.2)

private theorem isGen_self_local {X : Scheme.{0}} {L : Semi.LB X} (hL : L.IsLB) :
    Semi.LB.Gen.IsGen (⟨fun p => L.g p.1 p.2⟩ : Semi.LB.Iso L L) := by
  refine fun p q => unit_ext fun y hy => ?_
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

private theorem polForm_exists_local : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X}
    {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm K (HdR A), IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  open GlobalTheory.Published GlobalTheory.CatCoh in
  intro P E _ _ _ H Dw l Xo K _ x A _ π hπ
  have hA : Semi.IsAbelianScheme A := by
    have hG := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hc : IsCommMonObj A := by
      open MonoidalCategory CartesianMonoidalCategory MonObj in
      open scoped CategoryTheory.Obj in
        exact (by
          rw [isCommMonObj_iff_isMulCommutative]
          intro T
          refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
          rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
            ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm])
    exact ⟨hc, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 K A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso K ⊥ (dp0 K) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := exists_sum_wedge_local (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 K) (𝟙 _) A
    rw [show prim (dp0 K) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 K) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 K) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (isGen_self_local hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 K A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩
  obtain ⟨hfin, -, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, -, hFfin, -, hFrk⟩ := P.2.1 K A _ hA gA
  let p : PrimeSpectrum K := IsLocalRing.closedPoint K
  have d1 : Module.finrank K (primDR A) = 2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
    have := hrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have d2 : Module.finrank K (PrimitiveSubmodule A) = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have := hFrk p
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have d3 := Subspace.finrank_add_finrank_dualAnnihilator_eq (PrimitiveSubmodule A)
  have d4 : Module.finrank K (HdR A) = Module.finrank K (primDR A) := Subspace.dual_finrank_eq
  exact mem_of_annihilates_local _ (Fil A) hiso (by
    change 2 * Module.finrank K (PrimitiveSubmodule A).dualAnnihilator = _
    omega) f hf

theorem ksExist : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type)
    [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q →
    GlobalTheory.FlagTan.IsTanX y x' → ∃ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
      GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ hx
  have P := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G x'
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G y.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := polForm_exists_local P Xo hπ
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P Xo hπ a ha hpol
  have hK := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field P hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  have hL := (P.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P y hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → K,
      ∃ w, IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ =>
    GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, conj_embK]) a₀
  choose cf w hw using hrow
  refine ⟨fun k => cf k.1 k.2.1 k.2.2, A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub,
    hb, hπ, hπ', rfl, hpol, hu, fun σ k => hbl ⟨σ, k⟩, fun τ a₀ => ⟨w τ a₀, (hw τ a₀).1, (hw τ a₀).2⟩⟩

end GlobalTheory.KSExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixExistsStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_matrix_exists : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∃ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M := by
  first | exact @GlobalTheory.KSExist.ksExist | exact GlobalTheory.KSExist.ksExist | (intros; apply GlobalTheory.KSExist.ksExist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactRatioOfFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdLowestKTypeDimsIndepComplexEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdLowestKTypeDimsIndepComplexEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DimProdLab

theorem lab_spec {D : D7} (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
  unfold lab; rw [dite_eq_left (GlobalTheory.ConjReading.lab_exists σ ρ)]; exact (GlobalTheory.ConjReading.lab_exists σ ρ).choose_spec

theorem lab_injective {D : D7} (σ : D.what₂.LL →+* ℂ) : Function.Injective (lab σ : D.what₂.Tau → D.what₂.Tau) := by
  intro ρ ρ' h
  have cc : ∀ f : D.host.E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp f) = f := GlobalTheory.ConjReading.conj_conj
  rcases lab_spec σ ρ with h1 | h1 <;> rcases lab_spec σ ρ' with h2 | h2 <;> rw [h] at h1
  · exact Formalism.IndefR.Fock.KV.tauE_injective (h1.symm.trans h2)
  · exact absurd (h1.symm.trans h2) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · exact absurd (h2.symm.trans h1) (Formalism.IndefR.Fock.KV.tauE_ne_conj _ _)
  · have e := congrArg (fun f => (starRingEnd ℂ).comp f) (h1.symm.trans h2)
    simp only [cc] at e
    exact Formalism.IndefR.Fock.KV.tauE_injective e

theorem dimK_congr {R : Ranks} (hc : HCParam R) {a b : ℕ × ℕ} (e : a = b) :
    dimK a.1 a.2 (Formalism.L2.NTheta.kapW hc a.1 a.2) = dimK b.1 b.2 (Formalism.L2.NTheta.kapW hc b.1 b.2) := by
  subst e; rfl

theorem prod_dims (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := by
  set s := D.R.sigW ((i : ℕ) + 1)
  let hd : D.what₂.Tau → ℚ := fun τ => dimK s.1 s.2 (Formalism.L2.NTheta.kapW (D.hc τ) s.1 s.2)
  have h1 : ∀ ρ, dimK _ _ (kapAt (Wc D i) σ ρ) = hd (lab σ ρ) := fun ρ =>
    dimK_congr (D.hc (lab σ ρ)) (Formalism.IndefR.Fock.KV.sig_Wc i ρ)
  have h2 : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ = ((hd τ : ℚ) : ℝ) := fun τ =>
    congrArg (fun q : ℚ => (q : ℝ)) (dimK_congr (D.hc τ) (Formalism.IndefR.Fock.KV.sig_Wc i τ))
  have hb : Function.Bijective (lab σ : D.what₂.Tau → D.what₂.Tau) := (lab_injective σ).bijective_of_finite
  simp only [h1, h2]
  refine (Equiv.prod_comp (Equiv.ofBijective _ hb) (fun τ => ((hd τ : ℚ) : ℂ))).trans ?_
  push_cast
  rfl

end GlobalTheory.DimProdLab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdLowestKTypeDimsIndepComplexEmbeddingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_lowestKTypeDims_indep_complexEmbedding : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := by
  first | exact @GlobalTheory.DimProdLab.prod_dims | exact GlobalTheory.DimProdLab.prod_dims | (intros; apply GlobalTheory.DimProdLab.prod_dims <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExactRatioProof

open scoped InnerProductSpace ComplexConjugate

theorem L1 : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := GlobalTheory.T.prod_lowestKTypeDims_indep_complexEmbedding

theorem K2aux (D : D7) (T : CoreJ D) (h : LawsJ T) (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ) (hs : GoodEmb T.Q.c s)
    (f : FDSec (T.U ((i : ℕ) + 1) s).X) (W : HSp D) (hV : T.V ((i : ℕ) + 1) s = W) :
    eLpNorm' (fun q : AutQ W => ‖(hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) : ℂ) •
      adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f) :
          GA D W → ℂ) q.out‖) 2 (muQ1 W) =
      ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) *
        petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
          (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
  subst hV
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hmu := h.muUnit _ hj s hs
  have hcu := h.cUnit _ hj s hs
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  unfold petE
  rw [← Real.enorm_eq_ofReal hc0.le, ← eLpNorm'_const_smul c (by norm_num)]
  refine eLpNorm'_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc0, adel_muPin]
  rw [hcu, hmu.2.1]
  simp only [abs_one, one_mul, abs_norm, abs_of_nonneg (ptN_nonneg _ _ _)]
  unfold ptN
  rw [pnorm_eq_of_unit _ _ _ _ (hmu.2.2.2 _)]

theorem K2 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X), eLpNorm' (fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) = ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) * petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f :=
  fun D T h i s hs hV f => K2aux D T h i s hs f (Wc D i) hV

theorem K3 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ f ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.scalarForms T i s, petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f ≠ ⊤ := by
  intro D T h i s hs f hf
  obtain ⟨th, hr, -, hdu⟩ := h.dictU _ ⟨Nat.le_add_left _ _, i.2⟩ s hs
  exact petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hf

end GlobalTheory.ExactRatioProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedForm
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.Cover

open Matrix

theorem isPosDef_toReal_of_pos {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {β : LinearMap.BilinForm ℤ X} (hs : ∀ y z, β y z = β z y) (hp : ∀ x, x ≠ 0 → 0 < β x x) :
    IsPosDef (toReal β) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let GZ : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℤ := fun i j => β (b i) (b j)
  let G : Matrix (Module.Free.ChooseBasisIndex ℤ X) (Module.Free.ChooseBasisIndex ℤ X) ℝ := GZ.map (Int.cast : ℤ → ℝ)
  have hval : ∀ v : Module.Free.ChooseBasisIndex ℤ X → ℤ,
      β (∑ i, v i • b i) (∑ i, v i • b i) = v ⬝ᵥ (GZ *ᵥ v) := fun v => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, GZ,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hx : ∀ v : Module.Free.ChooseBasisIndex ℤ X → ℤ, v ≠ 0 → ∑ i, v i • b i ≠ 0 := fun v hv h0 =>
    hv (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent v h0 i)
  have hcast : ∀ c : Module.Free.ChooseBasisIndex ℤ X → ℤ,
      (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) = ((c ⬝ᵥ (GZ *ᵥ c) : ℤ) : ℝ) := fun c => by
    simp [dotProduct, mulVec, G]
  have hG : G.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star ((β (b j) (b i) : ℤ) : ℝ) = ((β (b i) (b j) : ℤ) : ℝ)
    rw [star_trivial, hs]
  have hpsd : G.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hG ?_
    intro x
    have hd : DenseRange (Pi.map (fun (_ : Module.Free.ChooseBasisIndex ℤ X) (q : ℚ) => (q : ℝ))) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    rw [star_trivial]
    refine hd.induction_on (p := fun y => 0 ≤ y ⬝ᵥ (G *ᵥ y)) x ?_ ?_
    · refine isClosed_le continuous_const ?_
      simp only [dotProduct, mulVec]
      fun_prop
    · intro q
      obtain ⟨⟨d, hd0⟩, hq⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
      choose c hc using hq
      have hd1 : (d : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd0
      have e : (fun i => (c i : ℝ)) = (d : ℝ) • Pi.map (fun (_ : Module.Free.ChooseBasisIndex ℤ X) (q : ℚ) => (q : ℝ)) q := by
        funext i
        have h1 : (c i : ℚ) = (d : ℚ) * q i := by simpa using hc i
        have h2 : ((c i : ℚ) : ℝ) = (((d : ℚ) * q i : ℚ) : ℝ) := by rw [h1]
        simpa using h2
      have h3 : (0 : ℝ) ≤ (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ)) := by
        rw [hcast]
        by_cases hc0 : c = 0
        · simp [hc0]
        · rw [← hval]; exact_mod_cast (hp _ (hx c hc0)).le
      rw [e, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← mul_assoc] at h3
      exact (mul_nonneg_iff_of_pos_left (mul_self_pos.mpr hd1)).mp h3
  have hdef : ∀ c : Module.Free.ChooseBasisIndex ℤ X → ℝ, c ≠ 0 → 0 < c ⬝ᵥ (G *ᵥ c) := by
    intro c hc
    have h0 := hpsd.dotProduct_mulVec_nonneg c
    rw [star_trivial] at h0
    refine h0.lt_of_ne fun h1 => ?_
    have h2 : G *ᵥ c = 0 := by
      have := (hpsd.dotProduct_mulVec_zero_iff (x := c)).1
      rw [star_trivial] at this
      exact this h1.symm
    have h3 : G.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc, h2⟩
    have h4 : GZ.det = 0 := by
      have : ((GZ.det : ℤ) : ℝ) = G.det := (Int.castRingHom ℝ).map_det GZ
      exact_mod_cast this.trans h3
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h4
    have := hp _ (hx v hv)
    rw [hval, hv0, dotProduct_zero] at this
    exact lt_irrefl _ this
  refine (isPosDef_iff_basis b _).2 fun c hc => (hdef c hc).trans_eq ?_
  have hGij : ∀ i j, G i j = ((β (b i) (b j) : ℤ) : ℝ) := fun _ _ => rfl
  simp only [dotProduct, mulVec, hGij, toReal_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Poinc.Cover

namespace GlobalTheory.Poinc.Cover

theorem coeff_int {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X] {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hmem : ∀ i, γ i ∈ balForms bar X)
    (hb : IsPartOfBasis fun i => (⟨γ i, hmem i⟩ : balForms bar X)) {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hs : toReal β = ∑ i, c i • toReal (γ i)) :
    ∃ n : Fin m → ℤ, ∀ i, c i = n i := by
  classical
  obtain ⟨k, bb, hbb⟩ := hb
  refine ⟨fun i => bb.coord (Sum.inl i) ⟨β, hβ⟩, fun i => ?_⟩
  let v : Option (Fin m) → balForms bar X := fun o => o.elim ⟨β, hβ⟩ fun i => ⟨γ i, hmem i⟩
  let w : Option (Fin m) → ℝ := fun o => o.elim (-1) c
  have h : ∑ o, w o • toReal ((balForms bar X).subtype (v o)) = 0 := by
    rw [Fintype.sum_option]
    simp only [w, v, Option.elim, Submodule.subtype_apply]
    rw [← hs]; simp
  have := sum_mul_eq_zero_of_sum_toReal (j := (balForms bar X).subtype) Subtype.val_injective
    (bb.coord (Sum.inl i)) h
  rw [Fintype.sum_option] at this
  simp only [w, v, Option.elim] at this
  have hc : ∀ i' : Fin m, bb.coord (Sum.inl i) ⟨γ i', hmem i'⟩ = if i' = i then 1 else 0 := fun i' => by
    rw [show (⟨γ i', hmem i'⟩ : balForms bar X) = bb (Sum.inl i') from (hbb i').symm, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h' : i' = i
    · simp [h']
    · simp [h', Ne.symm h']
  simp only [hc] at this
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  linarith

theorem exists_cone : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X →
    ∀ β ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < β x x) → ∃ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (k : ℕ)
      (c : Fin r → ℕ), IsCone bar φ γ ∧ 0 < k ∧ (∀ j, 0 < c j) ∧ k • β = ∑ j, c j • γ j := by
  intro O _ bar φ X _ _ _ _ _ _ hF β hβ hp
  classical
  have hB : toReal β ∈ psdCone (bar := bar) (X := X) :=
    (isPosDef_toReal_of_pos hβ.1 hp).mem_psdCone (toReal_mem hβ)
  obtain ⟨m, γ, c, hγ, hc, hsum⟩ := hF.cover _ hB
  obtain ⟨nZ, hnZ⟩ := coeff_int hγ.mem hγ.basis hβ hsum
  have hn0 : ∀ i, 0 ≤ nZ i := fun i => by exact_mod_cast (hnZ i) ▸ hc i
  let n : Fin m → ℕ := fun i => (nZ i).toNat
  have hn : ∀ i, ((n i : ℤ) : ℝ) = c i := fun i => by simp [n, Int.toNat_of_nonneg (hn0 i), hnZ i]
  have heq : β = ∑ i, n i • γ i := LinearMap.ext₂ fun a b => by
    have h1 := LinearMap.congr_fun₂ hsum a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, ← hn] at h1
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact_mod_cast h1
  let S : Finset (Fin m) := Finset.univ.filter fun i => n i ≠ 0
  let e := S.orderEmbOfFin rfl
  refine ⟨S.card, fun j => γ (e j), 1, fun j => n (e j), hF.face _ _ γ e.toEmbedding hγ, one_pos,
    fun j => Nat.pos_of_ne_zero (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2, ?_⟩
  rw [one_smul, heq]
  have h2 : ∑ i ∈ S, n i • γ i = ∑ i, n i • γ i :=
    Finset.sum_filter_of_ne fun i _ h => fun h0 => h (by rw [h0, zero_smul])
  have h3 := Finset.sum_map (Finset.univ : Finset (Fin S.card)) e.toEmbedding fun i => n i • γ i
  rw [Finset.map_orderEmbOfFin_univ S rfl] at h3
  rw [← h2, h3]
  rfl

end GlobalTheory.Poinc.Cover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConeInteriorDefiniteBalancedFormStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothCone_interior_definite_balancedForm : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFanOn bar φ X → ∀ β ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < β x x) → ∃ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X) (k : ℕ) (c : Fin r → ℕ), IsCone bar φ γ ∧ 0 < k ∧ (∀ j, 0 < c j) ∧ k • β = ∑ j, c j • γ j := by
  first | exact @GlobalTheory.Poinc.Cover.exists_cone | exact GlobalTheory.Poinc.Cover.exists_cone | (intros; apply GlobalTheory.Poinc.Cover.exists_cone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReads
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReads
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

theorem closeTo_of_mul {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)}
    {g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)} {z z' : Matrix (Fin N') (Fin N) D.host.E} (m k : ℕ)
    (h : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc (m * k) g g' z z') : Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc m g g' z z' := by
  intro i j
  obtain ⟨y, hy, e⟩ := h i j
  refine ⟨(k : Formalism.MainNotions.StandardLatticesGL3.AE D) * y, ?_, by rw [e]; push_cast; ring⟩
  rw [← nsmul_eq_mul]; exact nsmul_mem hy k

theorem exists_closeTo {D : D7} {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) {N N' : ℕ} (g : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D))
    (g' : GL (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)) (z : Matrix (Fin N') (Fin N) D.host.E) (n : ℕ) (hn : 0 < n) :
    ∃ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n g g' z z' := by
  obtain ⟨c, hc1, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger (GlobalTheory.NormSum.MovedLattice.inverseHalfDifferent_ne_zero D)
  set b : D.host.E := ((c : D.host.K) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a with hb
  set_option synthInstance.maxHeartbeats 200000 in
  have hb0 : b ≠ 0 := by
    refine mul_ne_zero ?_ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 ha0)
    intro h0
    apply hc0
    have : (c : D.host.K) = 0 := by exact_mod_cast h0
    exact_mod_cast this
  obtain ⟨v, hv⟩ : ∃ v, Formalism.MainNotions.StandardLatticesGL3.inc D b * v = 1 := by
    have hb1 : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
    exact ⟨Formalism.MainNotions.StandardLatticesGL3.inc D b⁻¹, by rw [← map_mul, hb1, map_one]⟩
  set t : Matrix (Fin N') (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := (g' : Matrix (Fin N') (Fin N') (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
    z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) * ((g⁻¹ : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with ht
  choose e w hw he using fun i j => GlobalTheory.NormSum.Expand.approx (t i j * v) n hn
  refine ⟨Matrix.of fun i j => e i j * b, fun i j => ⟨Formalism.MainNotions.StandardLatticesGL3.inc D b * w i j,
    AddSubgroup.subset_closure ⟨c, hc1, _, ha, w i j, hw i j, rfl⟩, ?_⟩⟩
  have h1 : t i j * v * Formalism.MainNotions.StandardLatticesGL3.inc D b = t i j := by
    rw [mul_assoc, mul_comm v, hv, mul_one]
  rw [Matrix.sub_apply, ← ht, Matrix.map_apply, Matrix.of_apply, map_mul]
  linear_combination (Formalism.MainNotions.StandardLatticesGL3.inc D b) * he i j + h1

theorem reads_om_of_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ (c : ℂ) (f₀ : WO S T → ℂ), Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∀ f, Reads ψ θ hS hT cc δ r G f → Reads ψ θ hS hT cc δ r (c • W.Om x y G) (om (g, h) f) := by
  intro D ψ θ S T a d hS hT cc δ r hSet e0 W χS χT om hW he0 x y g h hg hh c f₀ hf₀ hc G hG f hf
  have hC := hSet.crv
  have hSD0 : ∀ N : ℕ, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hWL, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC a d
    (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d) (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  have hfix : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) v e0 = e0 := by
    intro v hv
    rw [hWL v hv]; funext w; exact he0.2 v hv w
  have heT : e0 ∈ TT D (tor0 D cc δ) a d :=
    ⟨he0.1, 1, one_pos, fun v hv => by rw [one_nsmul]; exact hfix v hv⟩
  have hTT : ∀ z, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 ∈ TT D (tor0 D cc δ) a d := by
    intro z
    obtain ⟨Q, hQ, hz⟩ := GlobalTheory.NormSum.RatExtend.exists_nsmul_mem hC.1.1 δ z
    refine ⟨GlobalTheory.NormSum.RatExtend.Wd_diff _ he0.1, Q, hQ, fun v hv => ?_⟩
    obtain ⟨m, hm⟩ := hint v hv _ hz
    rw [GlobalTheory.NormSum.RatExtend.Hf_nsmul_right, ← GlobalTheory.NormSum.RatExtend.Hf_nsmul_left] at hm
    rw [GlobalTheory.NormSum.RatExtend.Wd_comm _ _ m hm, hfix _ (nsmul_mem hv _)]
  have hRt : ∀ (F : VC D a d → ℂ) (f' : WO S T → ℂ), Reads ψ θ hS hT cc δ r F f' → ∀ z,
      Reads ψ θ hS hT cc δ r (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F)
        (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f') := by
    intro F f' hF z
    exact (GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation ψ θ S T hS hT cc δ r hSet F f' hF z).smul _
  have hR0 : Reads ψ θ hS hT cc δ r (0 : VC D a d → ℂ) (0 : WO S T → ℂ) :=
    ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  have hRsum : ∀ {k : ℕ} (rr : Fin k → ℂ) (F : Fin k → VC D a d → ℂ) (f' : Fin k → WO S T → ℂ),
      (∀ i, Reads ψ θ hS hT cc δ r (F i) (f' i)) →
        Reads ψ θ hS hT cc δ r (∑ i, rr i • F i) (∑ i, rr i • f' i) := by
    intro k rr F f' hF
    have : ∀ s : Finset (Fin k), Reads ψ θ hS hT cc δ r (∑ i ∈ s, rr i • F i) (∑ i ∈ s, rr i • f' i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hR0
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact ((hF i).smul (rr i)).add ih
    exact this Finset.univ
  have key : ∀ zz : Matrix (Fin d) (Fin a) D.host.E, ∃ z',
      W.Om x y (Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ zz) e0) =
        Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') (W.Om x y e0) ∧
      Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ zz) • om (g, h) (heisO ψ S T (finPt hS hT r zz) f₀) =
        Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z') • heisO ψ S T (finPt hS hT r z') (om (g, h) f₀) := by
    intro zz
    obtain ⟨m, hm, hl⟩ := W.lift x y zz e0 heT
    obtain ⟨n, hn, hL⟩ := GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate ψ θ S T hS hT cc δ r hSet χS χT om hW x y g h hg hh f₀ hf₀.1 zz
    obtain ⟨z', hz'⟩ := exists_closeTo hC.1.1 (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
      zz (m * n) (Nat.mul_pos hm hn)
    refine ⟨z', hl z' (closeTo_of_mul m n hz'), hL z' (closeTo_of_mul n m ?_)⟩
    rwa [mul_comm] at hz'
  choose z' hz1 hz2 using key
  obtain ⟨k, rr, z, rfl⟩ := GlobalTheory.ThetaSpan.theta_span D cc δ hC a d e0 he0 W.nz G hG
  have hfG := Reads.unique hf (hRsum rr _ _ fun i => hRt e0 f₀ hf₀ (z i))
  subst hfG
  have e1 : c • W.Om x y (∑ i, rr i • Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0) =
      ∑ i, rr i • Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z' (z i))) (c • W.Om x y e0) := by
    rw [(GlobalTheory.NormSum.RatExtend.Om_sum W x y Finset.univ rr _ fun i => hTT (z i)).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz1, GlobalTheory.NormSum.RatExtend.Wd_smul, smul_comm]
  have e2 : om (g, h) (∑ i, rr i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) •
        heisO ψ S T (finPt hS hT r (z i)) f₀)) =
      ∑ i, rr i • (Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z' (z i))) •
        heisO ψ S T (finPt hS hT r (z' (z i))) (om (g, h) f₀)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, hz2]
  rw [e1, e2]
  exact hRsum rr _ _ fun i => hRt _ _ hc (z' (z i))

end GlobalTheory.NormExact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedThetaFunctionsReadOfMovedVacuumReadsStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedThetaFunctions_read_of_movedVacuum_reads : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ (c : ℂ) (f₀ : WO S T → ℂ), Reads ψ θ hS hT cc δ r e0 f₀ → Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
  ∀ G ∈ TT D (tor0 D cc δ) a d, ∀ f, Reads ψ θ hS hT cc δ r G f → Reads ψ θ hS hT cc δ r (c • W.Om x y G) (om (g, h) f) := by
  first | exact @GlobalTheory.NormExact.reads_om_of_vacuum | exact GlobalTheory.NormExact.reads_om_of_vacuum | (intros; apply GlobalTheory.NormExact.reads_om_of_vacuum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMap
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabTan

theorem tanBasis_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ X) (x' : Sp T ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ i, IsTanAtG t x (v i)) → (∀ w, IsTanAtG t x w → ∃! cf : Fin n → S, IsCombAtG t x v cf w) → ∃ v' : Fin n → (Sp (DualNumber T) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = spMap (dualMap ψ) ≫ v i) ∧ (∀ i, IsTanAtG t' x' (v' i)) ∧ ∀ w, IsTanAtG t' x' w → ∃! cf : Fin n → T, IsCombAtG t' x' v' cf w := by
  intro E _ _ _ H X X' t t' j m S T _ _ ψ x x' hx n v hv hv'
  have := t.semi.comm
  have := t'.semi.comm
  obtain ⟨k₁, k₂⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange t ψ x n v hv hv'
  rw [← hx] at k₁ k₂
  have h₁ := isGrpPullback_pullback t'.G x'
  have hc := h₁.comp m.cart
  obtain ⟨a, b⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t (x' ≫ j) _ _ hc
  obtain ⟨-, b'⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t' x' _ _ h₁
  choose u hu using fun i => a _ (k₁ i)
  have hu' : ∀ i, (u i).left ≫ pullback.fst t'.G.hom x' ≫ m.φ = spMap (dualMap ψ) ≫ v i := hu
  have hb := (b n u).2 ⟨fun i => by rw [hu']; exact k₁ i, by rw [funext hu']; exact k₂⟩
  obtain ⟨c₁, c₂⟩ := (b' n u).1 hb
  exact ⟨fun i => (u i).left ≫ pullback.fst t'.G.hom x', fun i => by rw [Category.assoc]; exact hu' i, c₁, c₂⟩

end GlobalTheory.SabTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisMovesAlongSemiAbelianTripleMapStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentBasis_moves_along_semiAbelianTripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) (m : SABMap t' t j) (S T : Type) [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ X) (x' : Sp T ⟶ X'), x' ≫ j = spMap ψ ≫ x → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), (∀ i, IsTanAtG t x (v i)) → (∀ w, IsTanAtG t x w → ∃! cf : Fin n → S, IsCombAtG t x v cf w) → ∃ v' : Fin n → (Sp (DualNumber T) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = spMap (dualMap ψ) ≫ v i) ∧ (∀ i, IsTanAtG t' x' (v' i)) ∧ ∀ w, IsTanAtG t' x' w → ∃! cf : Fin n → T, IsCombAtG t' x' v' cf w := by
  first | exact @GlobalTheory.SabTan.tanBasis_sabMap | exact GlobalTheory.SabTan.tanBasis_sabMap | (intros; apply GlobalTheory.SabTan.tanBasis_sabMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfOneMeasure
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.CovTop.MeasRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem sgAt_mk_eq {K : Type} [Field K] (σ₀ σ : K →+* ℂ) :
    sgAt σ₀ (InfinitePlace.mk σ) = σ ∨ sgAt σ₀ (InfinitePlace.mk σ) = (starRingEnd ℂ).comp σ := by
  have hc : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
    RingHom.ext fun a => ComplexEmbedding.conjugate_coe_eq σ a
  unfold sgAt
  split_ifs with h
  · rcases InfinitePlace.mk_eq_iff.1 h with h1 | h1
    · exact Or.inl h1.symm
    · right; rw [← h1, hc]
  · rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact Or.inl h1
    · right; rw [h1, hc]

theorem phiC_congr {T : CoreJ D} {j : ℕ} {σ₁ σ₂ : T.Q.c.F →+* ℂ} (e : σ₁ = σ₂) {W : Formalism.BasicNotions.TH.HSp D}
    (h₁ : T.V j σ₁ = W) (h₂ : T.V j σ₂ = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC T h₁ a f = phiC T h₂ a f := by
  subst e; rfl

end GlobalTheory.CovTop.MeasRd

namespace GlobalTheory.CovTop.MeasRd


end GlobalTheory.CovTop.MeasRd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingElementarySymmetricUnit
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM

namespace GlobalTheory


open Polynomial in
theorem exists_isUnit_esymm_of_eq_one :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [Fintype A] (y : A → R) (a₀ : A),
      y a₀ = 1 → ∃ k : ℕ, 1 ≤ k ∧ k ≤ Fintype.card A ∧
        IsUnit ((Finset.univ.val.map y).esymm k) := by
  intro R _ _ A _ y a₀ h
  by_contra hne
  push_neg at hne
  set s := Finset.univ.val.map y with hs
  have hcard : Multiset.card s = Fintype.card A := by simp [s, Finset.card_univ]
  have key := congrArg (Polynomial.eval (1 : R)) (Multiset.prod_X_sub_X_eq_sum_esymm s)
  have h0 : ((s.map fun t => X - C t).prod).eval 1 = 0 := by
    rw [Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map, Multiset.mem_map]
    exact ⟨y a₀, by simp [s], by simp [h]⟩
  rw [h0, Polynomial.eval_finsetSum, Finset.sum_range_succ'] at key
  simp only [eval_mul, eval_pow, eval_neg, eval_one, eval_C, eval_X, one_pow, mul_one,
    pow_zero, one_mul] at key
  have he0 : s.esymm 0 = 1 := by simp [Multiset.esymm, Multiset.powersetCard_zero_left]
  rw [he0] at key
  have hmem : ∑ j ∈ Finset.range (Multiset.card s), (-1 : R) ^ (j + 1) * s.esymm (j + 1)
      ∈ IsLocalRing.maximalIdeal R := by
    apply Ideal.sum_mem
    intro j hj
    apply Ideal.mul_mem_left
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    apply hne (j + 1) (by omega)
    rw [← hcard]; exact Finset.mem_range.mp hj
  have h1 : (1 : R) = -∑ j ∈ Finset.range (Multiset.card s), (-1 : R) ^ (j + 1) * s.esymm (j + 1) := by
    linear_combination -key
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [h1]; exact neg_mem hmem
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)

end GlobalTheory
end
