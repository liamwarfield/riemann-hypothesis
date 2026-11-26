module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetAt0ProdSubstDisjointVariables

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPart
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPart
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit

namespace GlobalTheory.ActionEnd

variable {C : Type} [Field C]

theorem germ_comp1_zero_point_left {dd n : ℕ} (a : Pt C n dd) (ha : GP a) : comp1 (pt C dd (0 : Fin 1)) a = a := by
  funext i
  rw [germComp1_eq_subst]
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) _

theorem actK_self [CharZero C] {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (B : FB C dd O) (a : O) :
    B.actK C a = B.A.act a := by
  funext i
  show MvPowerSeries.map (RingHom.id C) _ = _
  rw [MvPowerSeries.map_id]; rfl

theorem exists_isEnd_act : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I) (a : O), ∃ M M' : Matrix (Fin dd) (Fin dd) C, (∀ v, M.mulVec v = linAct (Y.B.A.act a) v) ∧ (∀ v, M'.mulVec v = linAct (Y.B.A.act (star a)) v) ∧ IsEnd (Y.raw p) V M M' ∧ un1 (Y.B.hL C Y.h a) = hEnd (Y.raw p) 1 M := by
  intro C _ _ V O _ _ dd Y d _ I _ p a
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine ⟨dLin (Y.B.A.act a), dLin (Y.B.A.act (star a)), fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · refine isEnd_of_hom Y p _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
    have h := Y.gauge.ad a
    rw [actK_self, actK_self] at h
    rw [← h]
    have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
      show MvPowerSeries.map (RingHom.id C) _ = _
      rw [MvPowerSeries.map_id]; rfl
    rw [e]
    exact Y.intAd a
  · have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
    have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
    have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
    have hs : MvPowerSeries.HasSubst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
    have e1 := matrixEnd_eq_subst Y p (pt C dd 0) q0 (by
      rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
    rw [germLinearPart_coordinatePoint_zero] at e1
    have e2 := matrixEnd_eq_subst Y p _ (g a) (Y.B.A.hom a) _ hX
    have e3 : comp1 (Y.B.A.act a) (pt C dd (0 : Fin 1)) = Y.B.A.act a := by
      funext i
      rw [germComp1_eq_subst]
      have : (fun q : Fin 1 × Fin dd => pt C dd (0 : Fin 1) q.2) = MvPowerSeries.X := by
        funext ⟨s, x⟩
        obtain rfl : s = 0 := Subsingleton.elim _ _
        rfl
      rw [this, MvPowerSeries.subst_self]; rfl
    have e4 : un1 (Y.B.hL C Y.h a) = MvPowerSeries.subst
        (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) (Y.B.hL C Y.h a) := by
      rw [← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]; rfl
    rw [e4, FB.hL, actK_self, e3, ev, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 2 × Fin dd => pair_points_zero_constant q0 (g a) q.1 q.2) hs,
      hEnd, hAt]
    show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
    congr 1
    funext ⟨s, x⟩
    fin_cases s
    · exact (e1 x).symm
    · exact (e2 x).symm

end GlobalTheory.ActionEnd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralEndOfActionLinearPartStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralEnd_of_action_linearPart : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I) (a : O), ∃ M M' : Matrix (Fin dd) (Fin dd) C, (∀ v, M.mulVec v = linAct (Y.B.A.act a) v) ∧ (∀ v, M'.mulVec v = linAct (Y.B.A.act (star a)) v) ∧ IsEnd (Y.raw p) V M M' ∧ un1 (Y.B.hL C Y.h a) = hEnd (Y.raw p) 1 M := by
  first | exact @GlobalTheory.ActionEnd.exists_isEnd_act | exact GlobalTheory.ActionEnd.exists_isEnd_act | (intros; apply GlobalTheory.ActionEnd.exists_isEnd_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasLenExistsMonoFp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hasLen_of_fp {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (M : Type) [AddCommGroup M] [Module O M]
    (h : Module.FinitePresentation O M) : ∃ x, HasLen v O M x := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O M
  have hk : (LinearMap.ker f).FG := Module.FinitePresentation.fg_ker f hf
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hk
  have hsmith : ∀ (b : ℕ) {idx : Type} [Fintype idx] (g : idx → Fin b → O),
      ∃ c : Fin b → O, Nonempty (((Fin b → O) ⧸ Submodule.span O (Set.range g)) ≃ₗ[O]
        ((i : Fin b) → O ⧸ Ideal.span {c i})) := by
    intro b
    induction b with
    | zero =>
      intro idx _ g
      exact ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    | succ b ih =>
      intro idx _ g
      obtain ⟨i0, a, u, s, hu, hau, hs, -, -⟩ := Smith.exists_pivot hv g
      obtain ⟨e1⟩ := Smith.pivot_equiv g i0 a u s hu hau hs
      obtain ⟨c, ⟨e2⟩⟩ := ih (fun j => Fin.removeNth i0 (g j - s j • a • u))
      exact ⟨Fin.cons a c, ⟨(e1.trans ((LinearEquiv.refl O _).prodCongr e2)).trans
        (Smith.consEquiv a c)⟩⟩
  obtain ⟨c, e⟩ := hsmith n g
  have hc : HasLen v O ((Fin n → O) ⧸ Submodule.span O (Set.range g))
      (∏ i, v (algebraMap O C (c i))) := ⟨n, c, e, rfl⟩
  exact ⟨_, hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hg).trans
    (f.quotKerEquivOfSurjective hf)).symm hc⟩

private theorem hasLen_mono {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M M' : Type} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M') {z z' : NNReal} (hf : Function.Surjective f)
    (hz : HasLen v R M z) (hz' : HasLen v R M' z') : z ≤ z' := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, hzc⟩ := hz
  obtain ⟨r, q, ⟨e'⟩, hzq⟩ := hz'
  let π : M →ₗ[R] ((t : Fin r) → R ⧸ Ideal.span {q t}) := e'.toLinearMap ∘ₗ f
  have hπ : Function.Surjective π := e'.surjective.comp hf
  let y : Fin m → ((t : Fin r) → R ⧸ Ideal.span {q t}) :=
    fun i => π (e.symm (Pi.single i 1))
  have hspan : Submodule.span R (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := hπ w
    have hx := eq_sum_single c (e x)
    have : x = ∑ i, (Quotient.out (e x i) : R) • e.symm (Pi.single i 1) := by
      calc x = e.symm (e x) := (e.symm_apply_apply x).symm
        _ = e.symm (∑ i, (Quotient.out (e x i) : R) • (Pi.single i (1 : R ⧸ Ideal.span {c i}) :
            (i : Fin m) → R ⧸ Ideal.span {c i})) := congrArg e.symm hx
        _ = _ := by simp only [map_sum, map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • y i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, y]
      rw [← map_smul, ← map_smul, single_smul_self, map_zero, map_zero]
    · intro b _ hb; rw [Matrix.diagonal_apply_ne _ (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hdet := det_mem_span_prod r q m y hspan (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at hdet
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hdet
  have hle := hv.le_of_dvd (⟨w, by rw [← hw, mul_comm]⟩ : ∏ t : Fin r, q t ∣ ∏ i, c i)
  rw [map_prod, map_prod, map_prod, map_prod] at hle
  rw [← hzc, ← hzq]
  exact hle

private theorem fp_quot {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) (n : ℕ) (M N : Submodule O (Fin n → O)) (hM : M.FG)
    (hN : N.FG) (hle : N ≤ M) : Module.FinitePresentation O (M ⧸ N.comap M.subtype) := by
  have : IsDomain O := hv.hom_inj.isDomain
  have : IsFractionRing O C := hv.isFractionRing
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : Module.Finite O M := Module.Finite.iff_fg.2 hM
  have : Module.Flat O M := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have : Module.Free O M := Module.free_of_flat_of_isLocalRing
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  refine Module.finitePresentation_of_surjective (N.comap M.subtype).mkQ
    (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  refine Submodule.fg_of_fg_map_injective M.subtype M.injective_subtype ?_
  rwa [Submodule.map_comap_subtype, inf_eq_right.2 hle]

theorem hasLen_exists_mono_fp : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → (∀ (M : Type) [AddCommGroup M] [Module O M], Module.FinitePresentation O M → ∃ x, HasLen v O M x) ∧ (∀ (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') (x x' : NNReal), Function.Surjective f → HasLen v O M x → HasLen v O M' x' → x ≤ x') ∧ ∀ (n : ℕ) (M N : Submodule O (Fin n → O)), M.FG → N.FG → N ≤ M → Module.FinitePresentation O (M ⧸ N.comap M.subtype) :=
  fun _ _ _ _ _ _ hv => ⟨fun M _ _ h => hasLen_of_fp hv M h,
    fun _ _ _ _ _ _ f _ _ hf hx hx' => hasLen_mono hv f hf hx hx',
    fun n M N hM hN hle => fp_quot hv n M N hM hN hle⟩

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HopfPointMem
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hopfPoint_mem {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [Unique N] (f : N → C) (hf : f ∈ L2.intFun (C := C) R N) :
    ∃ r : R, f = r • (1 : N → C) := by
  obtain ⟨r, hr⟩ := hf default
  refine ⟨r, funext fun x => ?_⟩
  rw [Subsingleton.elim x default, ← hr]
  simp [Algebra.smul_def]

private theorem hopfPoint_one {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) : (1 : N → C) ∈ L2.intFun (C := C) R N := fun _ => ⟨1, by simp⟩

private def hopfPoint {C : Type} [Field C] (R : Type) [CommRing R] [Algebra R C]
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] [Unique N] :
    L2.HopfOrder (C := C) R N where
  carrier := L2.intFun R N
  lat := by
    refine ⟨1, by simp, le_antisymm ?_ ?_⟩
    · intro f hf
      obtain ⟨r, rfl⟩ := hopfPoint_mem R N f hf
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, ?_⟩)
      funext x
      rw [Subsingleton.elim x default]
      simp
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩ x
      refine ⟨1, ?_⟩
      rw [Subsingleton.elim x j]
      simp
  le_int := le_rfl
  one_mem := hopfPoint_one R N
  mul_mem := by
    intro f g hf hg x
    obtain ⟨r, hr⟩ := hf x
    obtain ⟨s, hs⟩ := hg x
    exact ⟨r * s, by simp [hr, hs]⟩
  comul := by
    intro f hf
    refine Submodule.subset_span ⟨f, hf, 1, hopfPoint_one R N, ?_⟩
    funext q
    change f (q.1 + q.2) = f q.1 * 1
    rw [_root_.mul_one, Subsingleton.elim (q.1 + q.2) q.1]
  antipode := fun f hf x => hf (-x)

theorem htd_dim_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (cp : O), Nonempty (HodgeTateDatum p 0 v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ OE _ _ cp
  let _ : Unique (Nb p 0) := Pi.uniqueOfIsEmpty _
  have hS : Subsingleton (LieDualModP p O 0) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  refine ⟨{
    ρ :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _
        commutes' := fun _ => Subsingleton.elim _ _ }
    ρL :=
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := Subsingleton.elim _ _
        map_add' := fun _ _ => Subsingleton.elim _ _ }
    P := 0
    PL := 0
    E := 0
    E_alternating := ⟨Subsingleton.elim _ _, fun _ => rfl⟩
    isUnit_det_E := by simp
    E_equivariant := fun _ => Subsingleton.elim _ _
    projectors := ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    Ht := 0
    Bt := 0
    Ht_equivariant := ⟨fun _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    form_eq_alt := Subsingleton.elim _ _
    AA := hopfPoint O (Nb p 0)
    h3 := fun a f hf => ⟨f, hf, fun t => congrArg f (Subsingleton.elim _ _)⟩
    h4 := fun k => k.elim0
    h5 := fun _ s => ⟨1, hopfPoint_one O _, fun t => by
      have h0 : Up.pair p 0 0 s t = 0 := by simp [Up.pair]
      rw [h0, map_zero, ZMod.val_zero, pow_zero, Pi.one_apply]⟩
    φ := 0
    cotangent_surjective := fun y => ⟨0, Subsingleton.elim _ _⟩
    cotangent_ker_eq := ?_
    cotangent_linear := fun _ _ _ _ _ _ => Subsingleton.elim _ _ }⟩
  rw [LinearMap.ker_zero, eq_comm, eq_top_iff]
  intro f _
  have : f = 0 := by
    apply Subtype.ext
    funext x
    rw [Subsingleton.elim x 0]
    exact f.2.2
  rw [this]
  exact Submodule.zero_mem _

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartOfNilpotentChart
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartOfNilpotentChart
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem exists_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : Geo.Tor.IsGrpPullback G' G f φ) {Z : Scheme.{0}}
    (t' : Z ⟶ S') (t : Z ⟶ S) (ht : t' ≫ f = t) :
    ∃ P : (Over.mk t' ⟶ G') →* (Over.mk t ⟶ G), (∀ x, (P x).left = x.left ≫ φ) ∧ Function.Bijective P := by
  subst ht
  let p : (Over.mk t' ⟶ G') → (Over.mk (t' ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      have := Over.w x
      simp only [Over.mk_hom] at this ⊢
      rw [Category.assoc, h.1.w, ← Category.assoc, this])
  refine ⟨MonoidHom.mk' p fun x y => Over.OverMorphism.ext (h.2 (Over.mk t') x y (p x) (p y) rfl rfl).symm,
    fun _ => rfl, fun x y hxy => ?_, fun z => ?_⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact congrArg (fun z => z.left) hxy
    · exact (Over.w x).trans (Over.w y).symm
  · refine ⟨Over.homMk (h.1.lift z.left t' (Over.w z)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _

private theorem spec_comp {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) :
    Spec.map (CommRingCat.ofHom s.1.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type))) =
      Spec.map (CommRingCat.ofHom (algebraMap R₀ (R : Type))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact s.1.comp_algebraMap

theorem bxChart_of_nilChart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  intro R₀ _ G _ _ B e hb hm hn O G' _ _ φ hφ g F X hX
  have h0 : ∀ R, e R 0 = 1 := fun R => by
    have := hm R 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  choose P hP hPb using fun (R : LAlg R₀) (s : LHom O R) => exists_push hφ _ _ (spec_comp s)
  let X' : ∀ R : LAlg R₀, ∀ s : LHom O R, (Fin g → (R : Type)) →
      (Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G') := fun R s a =>
    @X R _ s.1.toRingHom.toAlgebra a
  choose Y hY using fun (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)) => (hb R).2 (P R s (X' R s a))
  have hYl : ∀ R s a, (e R (Y R s a)).left = (X' R s a).left ≫ φ := fun R s a => by rw [hY, hP]
  refine ⟨Y, ⟨fun R s => ?_, fun R R' s f a ha => ?_, fun R s a b ha hb' hab => ?_,
    fun R S s π σ hπσ hσ hπ x hx => ?_, fun R s a b ha hb' => ?_⟩, fun f α A hr hA R s a ha => ?_⟩
  · apply (hb R).1
    rw [hY, h0]
    letI := s.1.toRingHom.toAlgebra
    have : X' R s 0 = 1 := hX.zero R
    rw [this, map_one]
  · apply (hb R').1
    apply Over.OverMorphism.ext
    rw [hn, Over.comp_left, hYl, hYl]
    letI := s.1.toRingHom.toAlgebra
    letI := (f.comp s).1.toRingHom.toAlgebra
    let f' : (R : Type) →ₐ[(O : Type)] (R' : Type) := ⟨f.1.toRingHom, fun _ => rfl⟩
    have := congrArg (fun z => z.left ≫ φ) (hX.nat R R' f' a ha)
    exact (Category.assoc _ _ _).symm.trans this
  · letI := s.1.toRingHom.toAlgebra
    refine hX.inj R a b ha hb' ((hPb R s).1 ?_)
    exact (hY R s a).symm.trans ((congrArg (e R) hab).trans (hY R s b))
  · obtain ⟨z, hz⟩ := (hPb R s).2 (e R x)
    letI := s.1.toRingHom.toAlgebra
    letI := (π.comp s).1.toRingHom.toAlgebra
    let ρ : (R : Type) →ₐ[(O : Type)] (S : Type) := ⟨π.1.toRingHom, fun _ => rfl⟩
    let σ' : (S : Type) →ₐ[(O : Type)] (R : Type) :=
      ⟨σ.1.toRingHom, fun r => congrArg (fun u : LHom O R => u.1 r) hσ⟩
    have h1 : ρ.comp σ' = AlgHom.id _ _ := AlgHom.ext fun r => congrArg (fun u : LHom S S => u.1 r) hπσ
    have h2 : IsNilpotent (RingHom.ker ρ) := ⟨2, hπ.2⟩
    have h3 : spMap ρ ≫ z = 1 := by
      apply (hPb S (π.comp s)).1
      refine Eq.trans ?_ (map_one (P S (π.comp s))).symm
      rw [← h0, ← hx, hn, ← hz]
      apply Over.OverMorphism.ext
      rw [hP, Over.comp_left, Over.comp_left, hP]
      exact Category.assoc _ _ _
    obtain ⟨a, ha, hza⟩ := hX.surj R S ρ σ' h1 h2 z h3
    refine ⟨a, ha, (hb R).1 ?_⟩
    rw [hY, ← hz, hza]
  · apply (hb R).1
    letI := s.1.toRingHom.toAlgebra
    rw [hm, hY, hY, hY, ← map_mul]
    exact congrArg (P R s) (hX.law R a b ha hb')
  · apply (hb R).1
    apply Over.OverMorphism.ext
    letI := s.1.toRingHom.toAlgebra
    rw [← hA s (Y R s a) (X' R s a) (hYl R s a).symm, hYl]
    exact congrArg (fun z => z.left ≫ φ) (hr.2 R a ha)

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianFunctorNilChartOfNilpotentChartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianFunctorNilChart_of_nilpotent_chart : ∀ (R₀ : Type) [CommRing R₀] (G : Over (Spec (CommRingCat.of R₀))) [GrpObj G] [IsCommMonObj G] (B : BX R₀) (e : ∀ R : LAlg R₀, B.G R → (sp (R₀ := R₀) (R : Type) ⟶ G)), (∀ R, Function.Bijective (e R)) → (∀ R x y, e R (x + y) = e R x * e R y) → (∀ {R S : LAlg R₀} (f : LHom R S) (x : B.G R), e S (B.map f x) = spMap f.1 ≫ e R x) → ∀ (O : LAlg R₀) (G' : Over (Spec (CommRingCat.of (O : Type)))) [GrpObj G'] [IsCommMonObj G'] (φ : G'.left ⟶ G.left), Geo.Tor.IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R₀ (O : Type)))) φ → ∀ (g : ℕ) (F : Fin g → PS (O : Type) 2 g) (X : Fam G' g), NilChart G' F X → ∃ Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R, BXChart B O F Y ∧ ∀ (f : G' ⟶ G') (α : Fin g → PS (O : Type) 1 g) (A : OEnd B O), Reads X X f α → (∀ {R : LAlg R₀} (s : LHom O R) (x : B.G R) (x' : Over.mk (Spec.map (CommRingCat.ofHom s.1.toRingHom)) ⟶ G'), x'.left ≫ φ = (e R x).left → (x' ≫ f).left ≫ φ = (e R (A.f s x)).left) → ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a]) := by
  first | exact @GlobalTheory.ChF.bxChart_of_nilChart | exact GlobalTheory.ChF.bxChart_of_nilChart | (intros; apply GlobalTheory.ChF.bxChart_of_nilChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JacobianMulTangentChartMatrixIntertwines
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JacobianMulTangentChartMatrixIntertwines
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem nv_lin {R S : Type} [CommRing R] [CommRing S] (s : R →+* S) {n d : ℕ} (f : PS R n d)
    (hf : MvPowerSeries.constantCoeff f = 0) (a : Fin n → Fin d → S)
    (h : ∀ i j i' j', a i j * a i' j' = 0) :
    nv s f a = ∑ i, ∑ j, s (MvPowerSeries.coeff (Finsupp.single (i, j) 1) f) * a i j := by
  have ha : ∀ i j, IsNilpotent (a i j) := fun i j => ⟨2, by rw [pow_two, h]⟩
  rw [(nv_calculus R S s n d a ha).2.2.2.2.2 h f, hf, map_zero, zero_add, Fintype.sum_prod_type]

private theorem chart_add {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ} {F : FGLaw (O : Type) g}
    {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R} (hY : BXChart B O F.F Y)
    (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0) (v w : Fin g → (R : Type)) :
    Y R s (fun k => v k * e) + Y R s (fun k => w k * e) = Y R s (fun k => (v k + w k) * e) := by
  have hn : ∀ x : (R : Type), IsNilpotent (x * e) := fun x =>
    ⟨2, by rw [mul_pow, pow_two e, he, mul_zero]⟩
  have hl : ∀ v w : Fin g → (R : Type), Y R s (fun k => v k * e) + Y R s (fun k => w k * e) =
      Y R s (fun k => (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single (0, j) 1) (F.F k)) * v j +
        ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single (1, j) 1) (F.F k)) * w j) * e) := by
    intro v w
    rw [hY.law R s _ _ (fun _ => hn _) (fun _ => hn _)]
    congr 1
    funext k
    rw [nv_lin _ _ (F.const k)]
    · simp [Fin.sum_univ_two, add_mul, Finset.sum_mul, _root_.mul_assoc]
    · have hx : ∀ x y : (R : Type), x * e * (y * e) = 0 := fun x y => by
        rw [_root_.mul_mul_mul_comm, he, mul_zero]
      intro i j i' j'
      fin_cases i <;> fin_cases i' <;> exact hx _ _
  have h0 : Y R s (fun k => (0 : Fin g → (R : Type)) k * e) = 0 := by
    simp only [Pi.zero_apply, zero_mul]
    exact hY.zero R s
  have h1 := hl v 0
  have h2 := hl 0 w
  rw [h0, add_zero] at h1
  rw [h0, zero_add] at h2
  have h1' := hY.inj R s _ _ (fun _ => hn _) (fun _ => hn _) h1
  have h2' := hY.inj R s _ _ (fun _ => hn _) (fun _ => hn _) h2
  rw [hl]
  congr 1
  funext k
  have e1 := congrFun h1' k
  have e2 := congrFun h2' k
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at e1 e2
  rw [add_mul, add_mul, e1, e2]

private theorem chart_sum {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ} {F : FGLaw (O : Type) g}
    {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R} (hY : BXChart B O F.F Y)
    (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0) {κ : Type} (t : Finset κ)
    (v : κ → Fin g → (R : Type)) :
    ∑ i ∈ t, Y R s (fun k => v i k * e) = Y R s (fun k => (∑ i ∈ t, v i k) * e) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, zero_mul]
    exact (hY.zero R s).symm
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, ih, chart_add hY R s e he]
    simp only [Finset.sum_insert ha]

theorem lin_mul_tanMat : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (O : Type)), TanMat B O Y gb S → ∀ (A : OEnd B O) (α : Fin g → PS (O : Type) 1 g) (ρ : Matrix (Fin g) (Fin g) (O : Type)), (∀ j, MvPowerSeries.constantCoeff (α j) = 0) → (∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a])) → (∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (ρ k l) * i) → A.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) → lin α * S = S * ρ := by
  intro R₀ _ B O g F Y hY gb S hS A α ρ hα hA hρ
  let Dp : DualPair O := DualNum.dualPair O
  have hπ : Dp.π.SqZero := Dp.π.sqZero_of_span Dp.η (fun r => ⟨Dp.σ.1 r, Dp.sect r⟩) Dp.ker_eq Dp.η_sq
  have hn : ∀ x : (Dp.D : Type), IsNilpotent (x * Dp.η) := fun x =>
    ⟨2, by rw [mul_pow, pow_two Dp.η, Dp.η_sq, mul_zero]⟩
  have hη : Dp.η ∈ Dp.π.ker := by simpa using Dp.ση_mem 1
  ext j l
  have h := hρ Dp.σ Dp.π hπ l ⟨Dp.η, hη⟩ (fun k => ⟨Dp.σ.1 (ρ k l) * Dp.η, Dp.ση_mem _⟩) (fun _ => rfl)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hS _ _ Dp.σ, hA _ _ _ (fun _ => hn _)] at h
  simp only [hS _ _ Dp.σ, ← _root_.mul_assoc] at h
  rw [chart_sum hY _ _ _ Dp.η_sq] at h
  have hv : (fun j => nv Dp.σ.1.toRingHom (α j) ![fun k => Dp.σ.1 (S k l) * Dp.η]) =
      fun j => Dp.σ.1 ((lin α * S) j l) * Dp.η := by
    funext j
    rw [nv_lin _ _ (hα j)]
    · simp [Matrix.mul_apply, lin, Finset.sum_mul, _root_.mul_assoc]
    · intro i j i' j'
      fin_cases i; fin_cases i'
      show Dp.σ.1 _ * Dp.η * (Dp.σ.1 _ * Dp.η) = 0
      rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  rw [hv] at h
  have h2 := congrFun (hY.inj _ _ _ _ (fun _ => hn _) (fun _ => hn _) h) j
  rw [← sub_eq_zero]
  apply Dp.free
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, sub_mul, h2, Matrix.mul_apply, map_sum]
  simp only [map_mul, sub_self]

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JacobianMulTangentChartMatrixIntertwinesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobian_mul_tangentChartMatrix_intertwines : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (O : Type)), TanMat B O Y gb S → ∀ (A : OEnd B O) (α : Fin g → PS (O : Type) 1 g) (ρ : Matrix (Fin g) (Fin g) (O : Type)), (∀ j, MvPowerSeries.constantCoeff (α j) = 0) → (∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → A.f s (Y R s a) = Y R s (fun j => nv s.1.toRingHom (α j) ![a])) → (∀ {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g) (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (ρ k l) * i) → A.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k)) → lin α * S = S * ρ := by
  first | exact @GlobalTheory.ChF.lin_mul_tanMat | exact GlobalTheory.ChF.lin_mul_tanMat | (intros; apply GlobalTheory.ChF.lin_mul_tanMat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusMemTypicalCurveSet
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemCvOfSubstXPow
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem isCv_of_subst_X_pow {C : Type} [Field C] (V : VF C) {σ : Type} {m : ℕ} (hm : 0 < m)
    (δ γ : σ → PowerSeries C) (hγ : IsCv V γ)
    (h : ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (δ i) = γ i) : IsCv V δ := by
  intro i
  have hc : ∀ n, PowerSeries.coeff n (δ i) = PowerSeries.coeff (m * n) (γ i) := by
    intro n
    rw [← h i, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hm]
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hc, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hγ i).1
  · rw [hc]
    exact (hγ i).2 _

theorem cvRoot_alongCv_comp {C : Type} [Field C] {σ τ : Type} [Finite σ] [Finite τ] {γ : τ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {f : σ → MvPowerSeries τ C}
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) (F : MvPowerSeries σ C) :
    alongCv (fun i => alongCv γ (f i)) F = alongCv γ (MvPowerSeries.subst f F) := by
  unfold alongCv
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hf)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ)]

theorem cvRoot_alongCv_X {C : Type} [Field C] {τ : Type} [Finite τ] {γ : τ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : τ) :
    alongCv γ (MvPowerSeries.X i : MvPowerSeries τ C) = γ i := by
  unfold alongCv
  exact MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ) i

theorem mem_Cv_of_subst_X_pow : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (m : ℕ), 0 < m → ∀ a : ((κ → PowerSeries C) × (JJ I g → PowerSeries C)), ((fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i), fun q => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.2 q)) : ((κ → PowerSeries C) × (JJ I g → PowerSeries C))) ∈ Cv X V g → a ∈ Cv X V g := by
  intro C _ V d _ I _ κ _ X H g m hm a ha
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := ha
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  have hτ : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ m) = 0 := by simp [hm.ne']
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, H.lin i 0 (by simp)]
    simp
  have h1' : ∀ i, alongCv γ (X.lg i) = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i) := h1
  have h2' : ∀ q, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.2 q) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) := h2
  have ha0 : ∀ i, PowerSeries.constantCoeff (a.1 i) = 0 := by
    intro i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hm, ← h1' i, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (τ := Unit) hγ0 (hlg i)
  have hsub : ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (alongCv a.1 (X.ex i)) = γ i := by
    intro i
    rw [← alongCv_repar ha0 hτ]
    have : (fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ m) (a.1 i)) =
        fun i => alongCv γ (X.lg i) := funext fun i => (h1' i).symm
    rw [this, cvRoot_alongCv_comp hγ0 hlg, H.exlg, cvRoot_alongCv_X hγ0]
  have hcv : IsCv V (fun i => alongCv a.1 (X.ex i)) := isCv_of_subst_X_pow V hm _ γ hγ hsub
  refine ⟨fun i => alongCv a.1 (X.ex i),
    fun q => a.2 q + alongCv (fun i => alongCv a.1 (X.ex i)) (X.sg (X.u (1 - g) q)), hcv,
    isCv_of_subst_X_pow V hm _ lam hlam ?_, ?_, ?_⟩
  · intro q
    rw [PowerSeries.subst_add hS, h2', ← alongCv_repar (fun i => (hcv i).1) hτ, funext hsub, sub_add_cancel]
  · intro i
    rw [cvRoot_alongCv_comp ha0 H.exc, H.lgex, cvRoot_alongCv_X ha0]
  · intro q
    simp

end GlobalTheory.RowLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusMemTypicalCurveSet
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.FrobCurve

variable {C : Type} [Field C]

theorem sum_rescale_tyS {l : ℕ} (hl : l.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ j ∈ Finset.range l, PowerSeries.rescale (ζ ^ j) (tyS l a) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, PowerSeries.coeff_rescale, ← Finset.sum_mul]
  by_cases hn : l ∣ n
  · obtain ⟨q, rfl⟩ := hn
    have h1 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ (l * q) = (l : C) := by
      have : ∀ j, (ζ ^ j) ^ (l * q) = 1 := fun j => by
        rw [← pow_mul, mul_left_comm, pow_mul, hζ.pow_eq_one, one_pow]
      simp [this]
    rw [h1, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hl.pos]
    by_cases hq : ∃ s, l ^ s = q
    · obtain ⟨s, rfl⟩ := hq
      rw [coeff_tyS_pow hl.two_le, ← pow_succ', coeff_tyS_pow hl.two_le]
    · push Not at hq
      rw [coeff_tyS_of_ne _ _ hq, coeff_tyS_of_ne, mul_zero]
      intro s hs
      cases s with
      | zero =>
        rw [pow_zero] at hs
        exact hl.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hs.symm)
      | succ s =>
        rw [pow_succ'] at hs
        exact hq s (Nat.eq_of_mul_eq_mul_left hl.pos hs)
  · have hc : n.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hn).symm
    have h0 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ n = 0 := by
      rw [← (hζ.pow_of_coprime n hc).geom_sum_eq_zero hl.one_lt]
      exact Finset.sum_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h0, zero_mul, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow_of_not_dvd hl.pos _ _ hn]

theorem ge_zero_of_pow_eq_one (V : VF C) {ζ : C} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) : V.Ge 0 ζ := by
  have h1 : n • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe r =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, nsmul_eq_mul] at h1
    have : r = 0 := (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn.ne')
    rw [this]

theorem rescale_smul' (s c : C) (f : PowerSeries C) :
    PowerSeries.rescale s (c • f) = c • PowerSeries.rescale s f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem frob_mem_tySet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g := by
  classical
  intro C _ V d _ I _ κ _ X hX g x hx
  haveI := hX.charZero
  haveI := hX.closed
  have hl := V.l_prime
  haveI : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  haveI : NeZero V.l := ⟨hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  obtain ⟨h0, hadd, -, hres⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g
  let lo : (I g ⊕ JJ I g → PowerSeries C) → (κ → PowerSeries C) × (JJ I g → PowerSeries C) := fun A =>
    (fun i => ∑ c : I g, X.u g c i • A (Sum.inl c),
     fun q => A (Sum.inr q) - ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • A (Sum.inl c) else 0)
  have hiff : ∀ y : ℕ → I g ⊕ JJ I g → C,
      y ∈ X.TySet V g ↔ lo (fun n => tyS V.l fun s => y s n) ∈ Cv X V g := fun y => by
    constructor
    · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
      exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.2 (h2 q)⟩
    · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
      exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.1 (h2 q)⟩
  have hsum : ∀ (M : ℕ) (f : ℕ → (κ → PowerSeries C) × (JJ I g → PowerSeries C)),
      (∀ j, f j ∈ Cv X V g) → ∑ j ∈ Finset.range M, f j ∈ Cv X V g := fun M f hf =>
    Finset.sum_induction f (· ∈ Cv X V g) (fun a b ha hb => hadd a ha b hb) h0 fun j _ => hf j
  have hint : ∀ j, V.Ge 0 (ζ ^ j) := fun j => (ge_zero_of_pow_eq_one V hl.pos hζ.pow_eq_one).pow j
  have hS := hsum V.l _ fun j => hres (ζ ^ j) (hint j) _ ((hiff x).1 hx)
  rw [hiff]
  refine GlobalTheory.RowLaw.mem_Cv_of_subst_X_pow C V d I κ X hX g V.l hl.pos _ ?_
  have hsub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ V.l) :=
    PowerSeries.HasSubst.X_pow hl.ne_zero
  have key : ∀ n, PowerSeries.substAlgHom (R := C) hsub (tyS V.l fun s => Fs V.l x s n) =
      ∑ j ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ j) (tyS V.l fun s => x s n) := fun n => by
    rw [PowerSeries.coe_substAlgHom]
    exact sum_rescale_tyS hl hζ fun s => x s n
  convert hS using 1
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [lo, Prod.fst_sum, Finset.sum_apply, ← PowerSeries.coe_substAlgHom hsub, map_sum, map_smul, key,
      rescale_smul', Finset.smul_sum]
      exact Finset.sum_comm
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [lo, Prod.snd_sum, Finset.sum_apply, ← PowerSeries.coe_substAlgHom hsub, map_sum, map_sub, key,
      Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs
      · simp only [map_smul, key, rescale_smul', Finset.smul_sum]
      · simp

end GlobalTheory.RowLaw.FrobCurve
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusMemTypicalCurveSetStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_mem_typicalCurveSet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g := by
  first | exact @GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet | exact GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet | (intros; apply GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet <;> assumption)
end
end
