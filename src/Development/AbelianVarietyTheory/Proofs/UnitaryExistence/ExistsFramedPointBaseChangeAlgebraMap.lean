module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointEigenbasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGenerates
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic
public import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompleteIsAlgClosedAddValuation
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.FramedBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) = ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem tan_bc {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_spMap, dualMap_comp_alg, ← spMap_comp_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap, ← spMap_comp_spMap, Category.assoc, h2]
    have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
      simp [Hom.one_def]
    rw [← e, Over.comp_left]
    rfl

theorem eig_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, ← spMap_comp_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

theorem exists_frMap : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap φ y z := by
  intro hB E _ _ _ H Dw l Xo c S _ _ T _ _ φ y
  obtain ⟨s', hs', -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S T φ.toRingHom 1 y.x (spMap φ.toRingHom ≫ y.x) rfl y.s
  have hnz : SecNZ y.x y.s := GlobalTheory.T.fibreSectionNowhereZero_of_generates hB E H Dw l Xo S y.x y.s y.gen
  have hnz' : SecNZ (spMap φ.toRingHom ≫ y.x) s' := fun p' =>
    (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S T φ.toRingHom y.x _ rfl y.s s' hs' p').2 (hnz _)
  have hgen : SecGen (spMap φ.toRingHom ≫ y.x) s' := GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hB E H Dw l Xo T _ s' hnz'
  refine ⟨{ x := spMap φ.toRingHom ≫ y.x
            x_over := ?_
            u := fun τ i => spMap (dualMap φ.toRingHom) ≫ y.u τ i
            tan := fun τ i => tan_bc φ.toRingHom (y.tan τ i)
            eig := fun τ i => eig_bc φ τ (y.eig τ i)
            basis := fun τ w hw he => GlobalTheory.T.framedPoint_eigenbasis_baseChange E H Dw l Xo c S T φ y τ w hw he
            s := s'
            gen := hgen }, rfl, fun _ _ => rfl, ?_⟩
  · rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  · obtain ⟨pm, h1, h2, h3⟩ := hs'
    refine ⟨pm, h1, h2, fun i h => ?_⟩
    have h4 := h3 i h
    have h5 : scal y.x (1 : S) i = 1 := by
      unfold scal
      rw [map_one]
      simp [Out.liftFun]
    rw [h5, _root_.one_mul] at h4
    exact h4

end GlobalTheory.Frames.FramedBaseChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_baseChange_algebraMap : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap φ y z := by
  first | exact @GlobalTheory.Frames.FramedBaseChange.exists_frMap | exact GlobalTheory.Frames.FramedBaseChange.exists_frMap | (intros; apply GlobalTheory.Frames.FramedBaseChange.exists_frMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedParts
noncomputable section

namespace GlobalTheory.UnitaryGlue

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem cT_map {R A : Type} [CommRing R] [CommRing A] (p : R →+* A) (s : R →+* R) (t : A →+* A)
    (h : ∀ z, p (s z) = t (p z)) (M : Matrix n n R) :
    (Formalism.UG.cT s M).map p = Formalism.UG.cT t (M.map p) := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem exists_glue {ι R : Type} [CommRing R] {A : ι → Type} [∀ i, CommRing (A i)] (p : ∀ i, R →+* A i)
    (hp : Function.Bijective fun (z : R) (i : ι) => p i z) (s : R →+* R) (t : ∀ i, A i →+* A i)
    (h : ∀ i z, p i (s z) = t i (p i z)) (J : Matrix n n R) (g : ∀ i, GL n (A i))
    (hg : ∀ i, g i ∈ Formalism.UG.UJ (t i) (J.map (p i))) :
    ∃ x ∈ Formalism.UG.UJ s J, ∀ i, Formalism.UG.bc (p i) x = g i := by
  have inj : ∀ M N : Matrix n n R, (∀ i, M.map (p i) = N.map (p i)) → M = N := by
    intro M N hMN
    ext a b
    exact hp.1 (funext fun i => congrFun (congrFun (hMN i) a) b)
  have sur : ∀ u : ∀ i, Matrix n n (A i), ∃ M : Matrix n n R, ∀ i, M.map (p i) = u i := by
    intro u
    choose M hM using fun a b => hp.2 (fun i => u i a b)
    exact ⟨Matrix.of M, fun i => by ext a b; exact congrFun (hM a b) i⟩
  obtain ⟨M, hM⟩ := sur fun i => (g i).1
  obtain ⟨N, hN⟩ := sur fun i => ((g i)⁻¹).1
  have h1 : ∀ i, (1 : Matrix n n R).map (p i) = 1 := fun i => Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨M, N, inj _ _ fun i => ?_, inj _ _ fun i => ?_⟩, ?_, fun i => Units.ext (hM i)⟩
  · rw [Matrix.map_mul, hM, hN, h1, Units.mul_inv]
  · rw [Matrix.map_mul, hM, hN, h1, Units.inv_mul]
  · refine inj (Formalism.UG.cT s M * J * M) J fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (p i) s (t i) (h i), hM]
    exact hg i

theorem exists_glue₂ {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (p : R →+* A) (q : R →+* B)
    (e : R ≃+* A × B) (he : ∀ z, (e z).1 = p z ∧ (e z).2 = q z) (s : R →+* R) (t : A →+* A) (t' : B →+* B)
    (h : ∀ z, p (s z) = t (p z)) (h' : ∀ z, q (s z) = t' (q z)) (J : Matrix n n R) (g : GL n A) (g' : GL n B)
    (hg : g ∈ Formalism.UG.UJ t (J.map p)) (hg' : g' ∈ Formalism.UG.UJ t' (J.map q)) :
    ∃ x ∈ Formalism.UG.UJ s J, Formalism.UG.bc p x = g ∧ Formalism.UG.bc q x = g' := by
  have inj : ∀ M N : Matrix n n R, M.map p = N.map p → M.map q = N.map q → M = N := by
    intro M N h1 h2
    ext a b
    refine e.injective (Prod.ext ?_ ?_)
    · rw [(he _).1, (he _).1]; exact congrFun (congrFun h1 a) b
    · rw [(he _).2, (he _).2]; exact congrFun (congrFun h2 a) b
  have sur : ∀ (u : Matrix n n A) (v : Matrix n n B), ∃ M : Matrix n n R, M.map p = u ∧ M.map q = v := by
    intro u v
    refine ⟨Matrix.of fun a b => e.symm (u a b, v a b), ?_, ?_⟩
    · ext a b
      simp [← (he _).1]
    · ext a b
      simp [← (he _).2]
  obtain ⟨M, hM, hM'⟩ := sur g.1 g'.1
  obtain ⟨N, hN, hN'⟩ := sur (g⁻¹).1 (g'⁻¹).1
  have h1 : (1 : Matrix n n R).map p = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : (1 : Matrix n n R).map q = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨⟨M, N, inj _ _ ?_ ?_, inj _ _ ?_ ?_⟩, ?_, Units.ext hM, Units.ext hM'⟩
  · rw [Matrix.map_mul, hM, hN, h1, Units.mul_inv]
  · rw [Matrix.map_mul, hM', hN', h2, Units.mul_inv]
  · rw [Matrix.map_mul, hM, hN, h1, Units.inv_mul]
  · rw [Matrix.map_mul, hM', hN', h2, Units.inv_mul]
  · refine inj (Formalism.UG.cT s M * J * M) J ?_ ?_
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map p s t h, hM]
      exact hg
    · rw [Matrix.map_mul, Matrix.map_mul, cT_map q s t' h', hM']
      exact hg'

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) : V.gram.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : ∀ i, V.hT (V.frame i) (V.frame.equivFun.symm v) = 0 := by
    intro i
    have := congrFun hz i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Module.Basis.equivFun_symm_apply, map_sum, ← this]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, mul_comm]
  have h2 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← V.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_zero fun i _ => by
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h1, smul_zero]
  exact hv (V.frame.equivFun.symm.injective (h2.trans (map_zero _).symm))

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ z) =
      sigR S σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_map_inclR (f : R →ₐ[F] S) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) :
    (J.map (inclR R)).map (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom = J.map (inclR S) := by
  ext i j
  simp [inclR]

end Tens

theorem exists_inf_fin {D : D7} (V : HSp D) (gi : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E))
    (gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hi : gi ∈ HR (Ainf D.host.F) D.sp.cm.sig V.gram) (hf : gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram) :
    ∃ g : GA D V, infHom V g = gi ∧ finHom V g = gf := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨x, hx, h1, h2⟩ := exists_glue₂
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom e he
    (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig) (sigR _ D.sp.cm.sig) (map_sigR _ _) (map_sigR _ _)
    (JR (AF D.host.F) V.gram) gi gf
    (by rw [JR, map_map_inclR]; exact hi) (by rw [JR, map_map_inclR]; exact hf)
  exact ⟨⟨x, hx⟩, h1, h2⟩

theorem adelic_glue : ∀ (D : D7) (V : HSp D), (∀ gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram → ∃ g ∈ GfC V, finHom V g = gf) ∧ ∀ (Ψ : Finset (D.host.E →+* ℂ)) (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ)) → (∀ g : GA D V, (∀ τ, archM V (th τ) g = 1) → g ∈ GfC V) ∧ (∀ γ ∈ GQ V, ∃ γ₀ : GL (Fin V.rank) D.host.E, (∀ τ, archM V (th τ) γ = (γ₀ : Matrix _ _ D.host.E).map τ.1) ∧ (finHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (Af D.host.F))) ∧ (∀ τ, Continuous (archM V (th τ))) ∧ ∀ u : Ψ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, ((u τ).map (starRingEnd ℂ)).transpose * V.gram.map τ.1 * u τ = V.gram.map τ.1) → ∃ h ∈ GinfC V, ∀ τ, archM V (th τ) h = u τ := by
  intro D V
  letI := D.host.cmStar
  refine ⟨fun gf hf => ?_, fun Ψ th hΨ hth => ?_⟩
  · obtain ⟨g, h1, h2⟩ := exists_inf_fin V 1 gf (one_mem _) hf
    exact ⟨g, h1, h2⟩
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  have hτ : ∀ (τ : D.host.E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := fun τ x =>
    IsCMField.complexEmbedding_complexConj D.host.E τ x
  have hc : c ≠ 1 := fun h => IsCMField.complexConj_ne_one D.host.E (AlgEquiv.ext fun x => AlgEquiv.congr_fun h x)
  obtain ⟨hex, hall⟩ := GlobalTheory.InfAdeleCM.infAdele_tensor_bijective D.host.F D.host.E c D.sp.cm.deg2 hc
    D.sp.cm.totReal hτ
  choose θ₀ hθ₀ using hex
  classical
  let θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :=
    fun τ => if h : τ ∈ Ψ then th ⟨τ, h⟩ else θ₀ τ
  have hθt : ∀ τ : Ψ, θ τ.1 = th τ := fun τ => dif_pos τ.2
  obtain ⟨hcont, hconj, hbij⟩ := hall θ (fun τ => by
    by_cases h : τ ∈ Ψ
    · rw [hθt ⟨τ, h⟩]; exact hth ⟨τ, h⟩
    · have : θ τ = θ₀ τ := dif_neg h
      rw [this]; exact hθ₀ τ)
  have hb : Function.Bijective fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : Ψ) => th τ z := by
    have := hbij (Ψ : Set _) hΨ
    have e : (fun (z : Ainf D.host.F ⊗[D.host.F] D.host.E) (τ : Ψ) => th τ z) =
        fun z (τ : Ψ) => θ τ.1 z := by
      funext z τ; rw [hθt]
    rw [e]; exact this
  have hinc : ∀ (τ : Ψ) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
      (M.map (inclR (Ainf D.host.F))).map (th τ) = M.map τ.1 := by
    intro τ M
    ext i j
    exact (hth τ).1 _
  refine ⟨fun g hg => ?_, fun γ hγ => ?_, fun τ => ?_, fun u hu => ?_⟩
  · refine Units.ext (Matrix.ext fun a b => hb.1 (funext fun τ => ?_))
    have h1 := congrFun (congrFun (hg τ) a) b
    have h2 : (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).map (th τ) = 1 :=
      Matrix.map_one _ (map_zero _) (map_one _)
    exact h1.trans (congrFun (congrFun h2 a) b).symm
  · obtain ⟨γ₀, -, h0⟩ := Subgroup.mem_subgroupOf.1 hγ
    have h1 : (matHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (AF D.host.F)) :=
      (congrArg Units.val h0).symm
    refine ⟨γ₀, fun τ => ?_, ?_⟩
    · rw [← hinc, ← map_map_inclR (fstA D.host.F), ← h1]; rfl
    · rw [← map_map_inclR (sndA D.host.F), ← h1]; rfl
  · obtain ⟨e, he, hec, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    refine continuous_matrix fun a b => ?_
    have h1 : Continuous (th τ) := hθt τ ▸ hcont τ.1
    have h2 : Continuous fun g : GA D V => (matHom V g).1 a b :=
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem a b
    have h3 : (fun g : GA D V => archM V (th τ) g a b) = fun g => th τ (e ((matHom V g).1 a b)).1 := by
      funext g
      rw [(he _).1]; rfl
    rw [h3]
    exact h1.comp (continuous_fst.comp (hec.comp h2))
  · have hdet : ∀ τ, (u τ).det ≠ 0 := by
      intro τ h0
      have := congrArg Matrix.det (hu τ)
      rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact gram_det_ne_zero V (τ.1.injective (by rw [map_zero, this]))
    obtain ⟨x, hx, hxu⟩ := exists_glue (A := fun _ : Ψ => ℂ) th hb (sigR _ D.sp.cm.sig) (fun _ => starRingEnd ℂ)
      (fun τ z => hθt τ ▸ hconj τ.1 z) (JR (Ainf D.host.F) V.gram)
      (fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (u τ) (hdet τ))
      (fun τ => by rw [JR, hinc]; exact hu τ)
    obtain ⟨g, h1, h2⟩ := exists_inf_fin V x 1 hx (one_mem _)
    refine ⟨g, h2, fun τ => ?_⟩
    rw [archM, h1]
    exact congrArg Units.val (hxu τ)

end GlobalTheory.UnitaryGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts : ∀ (D : D7) (V : HSp D), (∀ gf : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E), gf ∈ HR (Af D.host.F) D.sp.cm.sig V.gram → ∃ g ∈ GfC V, finHom V g = gf) ∧ ∀ (Ψ : Finset (D.host.E →+* ℂ)) (th : Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th τ)) → (∀ g : GA D V, (∀ τ, archM V (th τ) g = 1) → g ∈ GfC V) ∧ (∀ γ ∈ GQ V, ∃ γ₀ : GL (Fin V.rank) D.host.E, (∀ τ, archM V (th τ) γ = (γ₀ : Matrix _ _ D.host.E).map τ.1) ∧ (finHom V γ).1 = (γ₀ : Matrix _ _ D.host.E).map (inclR (Af D.host.F))) ∧ (∀ τ, Continuous (archM V (th τ))) ∧ ∀ u : Ψ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, ((u τ).map (starRingEnd ℂ)).transpose * V.gram.map τ.1 * u τ = V.gram.map τ.1) → ∃ h ∈ GinfC V, ∀ τ, archM V (th τ) h = u τ := by
  first | exact @GlobalTheory.UnitaryGlue.adelic_glue | exact GlobalTheory.UnitaryGlue.adelic_glue | (intros; apply GlobalTheory.UnitaryGlue.adelic_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cmData_sig_ne_id {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) : ∃ a, hc.sig a ≠ a := by
  by_contra h
  push Not at h
  have hs : Function.Surjective (algebraMap F E) := fun a => (hc.fixed a).1 (h a)
  have h1 : Module.finrank F E = 1 :=
    (LinearEquiv.ofBijective (Algebra.linearMap F E)
      ⟨(algebraMap F E).injective, hs⟩).finrank_eq.symm.trans (Module.finrank_self F)
  have := hc.deg2
  omega

theorem exists_isDetRoot : ∀ (D : D7) (V : HSp D) (g : GA D V), ∃ x, IsDetRoot V g x := by
  intro D V g
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig
      (AlgHom.ext fun a => star_star a) (AlgHom.ext fun a => star_star a)
  have hc1 : c ≠ 1 := by
    obtain ⟨a, ha⟩ := cmData_sig_ne_id D.sp.cm
    intro h
    exact ha (congrArg (fun f : D.host.E ≃ₐ[D.host.F] D.host.E => f a) h)
  have hu := det_conj_mul V g
  rw [mul_comm] at hu
  exact GlobalTheory.AdLat.hilbert90_adeleRing_tensor_quadratic D.host.F D.host.E c D.sp.cm.deg2 hc1 (Formalism.L2.Theta.mt V g).det hu

end GlobalTheory.RecDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmallClosedField

open Cardinal

theorem mk_le_of_denseRange {A C : Type} [MetricSpace C] (f : A → C) (hf : DenseRange f) :
    #C ≤ #A ^ ℵ₀ := by
  have h : ∀ x : C, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := by
    intro x
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (hxy ▸ hs y)
  simpa using mk_le_of_injective hinj

theorem mk_le_continuum_of_finite_residueField (V : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [Finite (ResidueField V)] : #V ≤ 𝔠 := by
  have hfin : ∀ n : ℕ, Finite (V ⧸ maximalIdeal V ^ n) := fun n =>
    haveI : Finite (V ⧸ maximalIdeal V) := inferInstanceAs (Finite (ResidueField V))
    Ideal.finite_quotient_pow (maximalIdeal V).fg_of_isNoetherianRing n
  let f : V → ∀ n : ℕ, V ⧸ maximalIdeal V ^ n := fun x n => Ideal.Quotient.mk _ x
  have hinj : Function.Injective f := by
    intro x y hxy
    have : x - y ∈ ⨅ n : ℕ, maximalIdeal V ^ n :=
      Ideal.mem_iInf.2 fun n => Ideal.Quotient.eq.1 (congrFun hxy n)
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top] at this
    exact sub_eq_zero.1 this
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n => mk_le_aleph0).trans ?_
  simp

theorem exists_small_closed_subfield {K C : Type} [Field K] [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra K C] (hK : #K ≤ 𝔠)
    {x : K} (hx : 1 < ‖algebraMap K C x‖) :
    ∃ L : Subfield C, (∀ y : K, algebraMap K C y ∈ L) ∧ IsClosed (L : Set C) ∧ IsAlgClosed L ∧
      #L ≤ 𝔠 := by
  let A := algebraicClosure K C
  let L : Subfield C := A.toSubfield.topologicalClosure
  have hAL : A.toSubfield ≤ L := A.toSubfield.le_topologicalClosure
  have hKL : ∀ y : K, algebraMap K C y ∈ L := fun y => hAL (A.algebraMap_mem y)
  have hcl : IsClosed (L : Set C) := A.toSubfield.isClosed_topologicalClosure
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL x⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  letI : Algebra A L := (Subfield.inclusion hAL : A.toSubfield →+* L).toAlgebra
  have hd : DenseRange (algebraMap A L) :=
    (denseRange_inclusion_iff (s := (A.toSubfield : Set C)) (t := (L : Set C)) hAL).2 subset_rfl
  haveI : IsAlgClosed A := IsAlgClosure.isAlgClosed K
  refine ⟨L, hKL, hcl, isAlgClosed_of_denseRange hd, (mk_le_of_denseRange _ hd).trans ?_⟩
  have hA : #A ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max K A).trans (max_le hK aleph0_le_continuum)
  exact (power_le_power_right hA).trans continuum_power_aleph0.le

theorem exists_scf_isometry {p : ℕ} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [CompleteSpace C] [IsAlgClosed C] [CharZero C] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹) (hC : #C ≤ 𝔠) :
    ∃ (D : SCF p) (e : C →+* ↥D.S), ∀ x, ‖e x‖ = ‖x‖ := by
  have hle : #C ≤ #BigT := by
    refine hC.trans ?_
    rw [mk_set, mk_set, mk_real]
    exact (cantor _).le.trans (cantor _).le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hle
  let S : Set BigT := Set.range j
  let e : S ≃ C := (Equiv.ofInjective j j.injective).symm
  letI : Field S := e.field
  let r : S ≃+* C := e.ringEquiv
  letI : NormedField S := NormedField.induced S C r r.injective
  have hn : ∀ x : S, ‖x‖ = ‖r x‖ := fun _ => rfl
  have hn' : ∀ x : C, ‖r.symm x‖ = ‖x‖ := fun x => by rw [hn, r.apply_symm_apply]
  letI : NontriviallyNormedField S :=
    { (inferInstance : NormedField S) with
      non_trivial := by
        obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := C)
        exact ⟨r.symm x, (hn' x).symm ▸ hx⟩ }
  haveI : IsUltrametricDist S :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hn, hn, hn, map_add (f := _)]; exact IsUltrametricDist.norm_add_le_max _ _
  haveI : IsAlgClosed S := IsAlgClosed.of_ringEquiv C S r.symm
  have hiso : Isometry r := AddMonoidHomClass.isometry_of_norm r fun x => (hn x).symm
  haveI : CompleteSpace S :=
    (hiso.isUniformInducing.completeSpace_congr r.surjective).2 inferInstance
  haveI : CharZero S := charZero_of_injective_ringHom (f := r.symm.toRingHom) r.symm.injective
  exact ⟨{ S := S, norm_p := by rw [hn, map_natCast, hp] }, r.symm.toRingHom, hn'⟩

theorem exists_extension_intO {V W C : Type} [CommRing V] [IsDomain V] [CommRing W] [IsDomain W]
    [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (g : V →+* intO C) (φ : V →+* W)
    (hg : Function.Injective g) (hφ : Function.Injective φ) (hf : φ.Finite) :
    ∃ g' : W →+* intO C, g'.comp φ = g ∧ Function.Injective g' := by
  letI : Algebra V W := φ.toAlgebra
  letI : Algebra V C := ((intO C).subtype.comp g).toAlgebra
  haveI : Module.Finite V W := hf
  have hgC : Function.Injective (algebraMap V C) := Subtype.val_injective.comp hg
  haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).2 hφ
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective V C).2 hgC
  let l : W →ₐ[V] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hl : Function.Injective l := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := V) ?_
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, l.commutes] at ha
    exact (map_eq_zero_iff _ hgC).1 ha
  have hmem : ∀ a : W, l a ∈ intO C := by
    intro a
    have hO := normIntegers_integers C
    obtain ⟨q, hq, hqa⟩ := (Algebra.IsIntegral.isIntegral (R := V) a).map l
    let g₀ : V →+* normIntegers C := (algebraMap V C).codRestrict (normIntegers C) fun v =>
      mem_normIntegers_iff.2 (g v).2
    have hint : IsIntegral (normIntegers C) (l a) :=
      ⟨q.map g₀, hq.map g₀, by rw [Polynomial.eval₂_map]; exact hqa⟩
    exact mem_normIntegers_iff.1 (hO.mem_of_integral hint)
  refine ⟨l.toRingHom.codRestrict (intO C) hmem, ?_, fun a b h => hl (congrArg Subtype.val h)⟩
  ext a
  exact l.commutes a

theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

theorem exists_embedding_and_extension :
    ∀ (T : CDVR) (p : ℕ), p.Prime → T.FinRes → (p : T.V) ∈ maximalIdeal T.V → (∃ (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧ ∀ (C : SCF p) (g : T.V →+* intO ↥C.S) (T' : CDVR) (φ : T.V →+* T'.V), Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → Function.Injective φ → φ.Finite → ∃ g' : T'.V →+* intO ↥C.S, g'.comp φ = g ∧ Function.Injective g' ∧ ∀ a ∈ maximalIdeal T'.V, ‖((g' a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  intro T p hp hfin hpm
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  refine ⟨?_, fun C g T' φ hg hgm hφ hf => ?_⟩
  · obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
      exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0 hpm
        (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
    haveI : Finite (ResidueField T.V) := hfin
    have hK : #T.Fr ≤ 𝔠 :=
      (IsLocalization.cardinalMk_le (nonZeroDivisors T.V)).trans
        (mk_le_continuum_of_finite_residueField T.V)
    have hx : 1 < ‖algebraMap T.Fr C (algebraMap T.V T.Fr p)⁻¹‖ := by
      rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
    obtain ⟨L, hKL, hcl, hac, hL⟩ := exists_small_closed_subfield hK hx
    letI : NontriviallyNormedField L :=
      { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
    haveI : CompleteSpace L := hcl.completeSpace_coe
    haveI : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
    let i : T.Fr →+* L := (algebraMap T.Fr C).codRestrict L hKL
    have hi : ∀ y, ‖i y‖ = ‖algebraMap T.Fr C y‖ := fun _ => rfl
    haveI : CharZero L := charZero_of_injective_ringHom i.injective
    have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
      rw [← map_natCast i, hi, ← map_natCast (algebraMap T.V T.Fr), hCp]
    obtain ⟨D, e, he⟩ := exists_scf_isometry hLp hL
    have hle : ∀ a : T.V, ‖(e.comp i) (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => by
      rw [RingHom.comp_apply, he, hi]; exact (hC _).2 ⟨a, rfl⟩
    refine ⟨D, e.comp i, hle, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((e.comp i).comp (algebraMap T.V T.Fr)) hle hp0 ?_ ha
    rw [map_natCast, D.norm_p]
    exact inv_lt_one_of_one_lt₀ h1
  · obtain ⟨g', hc, hinj⟩ := exists_extension_intO g φ hg hφ hf
    refine ⟨g', hc, hinj, fun a ha => ?_⟩
    refine norm_lt_one_of_mem_maximalIdeal ((intO ↥C.S).subtype.comp g') (fun b => (g' b).2)
      ((map_ne_zero_iff φ hφ).2 hp0) ?_ ha
    have := hgm p hpm
    rw [← hc] at this
    exact this

end GlobalTheory.SmallClosedField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrierStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.DIV.Cons
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier : ∀ (T : CDVR) (p : ℕ), p.Prime → T.FinRes → (p : T.V) ∈ maximalIdeal T.V → (∃ (C : SCF p) (eF : T.Fr →+* ↥C.S), (∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1) ∧ ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1) ∧ ∀ (C : SCF p) (g : T.V →+* intO ↥C.S) (T' : CDVR) (φ : T.V →+* T'.V), Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → Function.Injective φ → φ.Finite → ∃ g' : T'.V →+* intO ↥C.S, g'.comp φ = g ∧ Function.Injective g' ∧ ∀ a ∈ maximalIdeal T'.V, ‖((g' a : intO ↥C.S) : ↥C.S)‖ < 1 := by
  first | exact @GlobalTheory.SmallClosedField.exists_embedding_and_extension | exact GlobalTheory.SmallClosedField.exists_embedding_and_extension | (intros; apply GlobalTheory.SmallClosedField.exists_embedding_and_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyFrPtComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem nonempty_frPt_complex : N1c → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ σ : c.F →+* ℂ, Nonempty (FrPt Xo c (CAt σ)) := by
  intro hN hT E _ _ _ H Dw l Xo c h σ
  classical
  obtain ⟨L, _, _, j, x, hx⟩ := GlobalTheory.T.xoNumPt_of_p_add_q_pos hN E H Dw l Xo c h
  let _ : Algebra c.F L := j.toAlgebra
  let _ : Algebra c.F ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic c.F L := by
    have : IsScalarTower ℚ c.F L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    exact Algebra.IsAlgebraic.tower_top (K := ℚ) c.F
  let φ : L →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let _ : Algebra L ℂ := φ.toRingHom.toAlgebra
  obtain ⟨_, y, _⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := L) (L' := ℂ) hT
    (fun r => (φ.commutes r).symm) x hx (fun τ i j => if i = j then 1 else 0)
    (fun τ i => by simp) (fun τ i j hij => by simp [hij.ne'])
  exact ⟨y⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.LevelOpen

theorem exists_cut {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (e : A)
    (he : e * e = e) (hσ : σ e = e) (g : GL (Fin n) A) (hg : g ∈ Formalism.UG.UJ σ J) :
    ∃ k ∈ Formalism.UG.UJ σ J, k.1 = e • g.1 + (1 - e) • (1 : Matrix (Fin n) (Fin n) A) := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, h1, one_mul, sub_zero]
  have key : ∀ X Y Z W : Matrix (Fin n) (Fin n) A,
      (e • X + (1 - e) • Z) * (e • Y + (1 - e) • W) = e • (X * Y) + (1 - e) • (Z * W) := by
    intro X Y Z W
    simp only [add_mul, mul_add, smul_mul_smul_comm, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  have one : ∀ X : Matrix (Fin n) (Fin n) A, e • X + (1 - e) • X = X := by
    intro X; rw [← add_smul, add_sub_cancel, one_smul]
  refine ⟨⟨e • g.1 + (1 - e) • 1, e • (g⁻¹).1 + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩
  · rw [key, Units.mul_inv, one_mul, one]
  · rw [key, Units.inv_mul, one_mul, one]
  · have hg' : Formalism.UG.cT σ g.1 * J * g.1 = J := hg
    change Formalism.UG.cT σ (e • g.1 + (1 - e) • 1) * J * (e • g.1 + (1 - e) • 1) = J
    have hc : Formalism.UG.cT σ (e • g.1 + (1 - e) • (1 : Matrix (Fin n) (Fin n) A)) =
        e • Formalism.UG.cT σ g.1 + (1 - e) • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Formalism.UG.cT, hσ]
      · simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
    rw [hc]
    conv_lhs => rw [← one J]
    rw [key, key, hg', one_mul, mul_one, one]

theorem congr_mem_nhds (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (N : ℕ) (hN : 0 < N) :
    {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) | ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) := _root_.GlobalTheory.Mem.Vol.StabGroup.congr_mem_nhds F E n L hfg hL N hN

theorem continuous_fin (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) : AF F ⊗[F] E → Af F ⊗[F] E) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(sndA F).toRingHom] Af F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((sndA F).toRingHom : AF F → Af F) := continuous_snd
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem exists_finPart_mat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    ∃ k ∈ HR (AF F) σ J, Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom k = 1 ∧
      Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom k =
        Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom g := by
  let e : AF F ⊗[F] E := pairA F 0 1 ⊗ₜ 1
  have he : e * e = e := by
    simp only [e, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    congr 1
    exact Prod.ext (mul_zero _) (mul_one _)
  have hσ : sigR (AF F) σ e = e := by
    simp [e, sigR]
  obtain ⟨k, hk, hke⟩ := exists_cut _ (JR (AF F) J) e he hσ g hg
  have h0 : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) e = 0 :=
    TensorProduct.zero_tmul _ _
  have h1 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) e = 1 := rfl
  refine ⟨k, hk, Units.ext ?_, Units.ext ?_⟩
  · change k.1.map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1
    ext i j
    rw [hke]
    by_cases h : i = j
    · subst h; simp [h0]
    · simp [h0, Matrix.one_apply_ne h]
  · ext i j
    change Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (k.1 i j) =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (g.1 i j)
    rw [hke]
    simp [h1]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_finPart (D : D7) (V : HSp D) (g : GA D V) : ∃ k ∈ GfC V, finHom V k = finHom V g := by
  let g' : HR (AF D.host.F) D.sp.cm.sig V.gram := g
  obtain ⟨k, hk, h1, h2⟩ := exists_finPart_mat D.sp.cm.sig V.gram (matHom V g) g'.2
  let k' : HR (AF D.host.F) D.sp.cm.sig V.gram := ⟨k, hk⟩
  exact ⟨k', h1, h2⟩

theorem level_mem_nhds : ∀ (D : D7) (V : HSp D) (N : ℕ) (Kf : Subgroup (GA D V)), 0 < N → IsLevelK V N Kf → ∀ g₀ : GA D V, {g : GA D V | ∃ k ∈ Kf, ∃ h ∈ GinfC V, g = g₀ * k * h} ∈ 𝓝 g₀ := by
  intro D V N Kf hN hK g₀
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  let ψ : V.V →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) :=
    V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)
  let L := V.L0.map ψ
  have hfg : L.FG := V.standardTuple_isLattice.fg.map ψ
  have hL : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have h := congrArg (Submodule.map (V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)))
      hspan
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at h
    exact h
  have hhat : GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) = latHat V := by
    unfold GlobalTheory.AdLat.hat latHat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
  have hn := congr_mem_nhds D.host.F D.host.E V.rank L hfg hL N hN
  rw [hhat] at hn
  have hm : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hf : Continuous fun g : GA D V => (finHom V g).1 := hm.matrix_map (continuous_fin D.host.F D.host.E)
  have hc : Continuous fun g : GA D V => (finHom V (g₀⁻¹ * g)).1 := hf.comp (continuous_const_mul g₀⁻¹)
  have h1 := hc.continuousAt.preimage_mem_nhds (x := g₀) (by rw [inv_mul_cancel, map_one]; exact hn)
  refine Filter.mem_of_superset h1 fun g hg => ?_
  obtain ⟨k, hk, hkg⟩ := exists_finPart D V (g₀⁻¹ * g)
  refine ⟨k, (hK k).mpr ⟨hk, by rw [hkg]; exact hg⟩, k⁻¹ * (g₀⁻¹ * g), ?_, by group⟩
  change finHom V _ = 1
  rw [map_mul, map_inv, hkg, inv_mul_cancel]

end GlobalTheory.LevelOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.RecDict

theorem level_good_and_sign : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ ∀ τ : D.host.E →+* ℂ, τ (Q.H.rt : D.host.E) = Q.H.rt0 → (τ (-D.host.xi0)).im < 0 := by
  rintro D Q ⟨⟨-, hrt, hrt0, -⟩, ⟨hM, hA⟩, -, -⟩
  refine ⟨fun p hp => ?_, hA, fun τ hτ => ?_⟩
  · have hodd := Q.l.odd
    rw [hM] at hodd
    have h3 : ∀ a : ℕ, a.Prime → Odd a → 3 ≤ a := fun a ha ho => by
      have h2 := ha.two_le
      obtain ⟨k, hk⟩ := ho
      omega
    have ha := h3 _ (D.host.g_prime 0) (Nat.Odd.of_mul_left hodd)
    have hb := h3 _ (D.host.g_prime 1) (Nat.Odd.of_mul_right hodd)
    have hab : (D.host.g 0).Coprime (D.host.g 1) :=
      (Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    have hM0 : Q.l.M ≠ 0 := by have := Q.l.three_le; omega
    have key : ∀ c, 3 ≤ c → c ∣ Q.l.M → ¬ p ∣ c → 3 ≤ Q.l.M / p ^ Q.l.M.factorization p :=
      fun c hc hd hn => hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
    by_cases h : p ∣ D.host.g 0
    · refine key _ hb (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
      exact Nat.eq_one_of_dvd_coprimes hab h h'
    · exact key _ ha (hM ▸ dvd_mul_right _ _) h
  · rw [hrt, hrt0] at hτ
    have h1 := xi0_embedding_im_pos D τ ((mem_cm_type_iff D τ).2 hτ)
    have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    have hpos : 0 < (D.host.φ₀ D.host.sqrtMinusD).im := by
      rw [hφ]
      have hd : (0 : ℝ) < D.host.d := by exact_mod_cast d_pos D
      simpa using hd
    rw [if_pos hpos, Int.cast_one, _root_.one_mul] at h1
    rw [map_neg, Complex.neg_im]
    linarith

end GlobalTheory.RecDict
end
