module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmEllipticCurveIntegersWithPeriod
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyDescendsToNumberField
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmTensorLatticeCurvePrincipalTriple
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open Formalism.L2.Pj hiding dualMap_alg
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LetterInt

open GlobalTheory.IntLie

theorem prod_pull {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T' : Over S') (T : Over S₀) (g : T.left ⟶ T'.left)
    (hg : g ≫ T'.hom ≫ f = T.hom) {m : ℕ} (a : Fin m → (T' ⟶ G')) (a₀ : Fin m → (T ⟶ G))
    (ha : ∀ j, (a₀ j).left = g ≫ (a j).left ≫ φ) :
    ((List.ofFn a₀).prod).left = g ≫ ((List.ofFn a).prod).left ≫ φ := by
  let δ : Over.mk (g ≫ T'.hom) ⟶ T' := Over.homMk g rfl
  have h1 := prod_push h (Over.mk (g ≫ T'.hom)) T (𝟙 _)
    ((Category.id_comp _).trans (hg.symm.trans (Category.assoc _ _ _).symm)) (fun j => δ ≫ a j) a₀
    (fun j => (Category.assoc _ _ _).trans ((ha j).symm.trans (Category.id_comp _).symm))
  have h2 : ∀ {m : ℕ} (a : Fin m → (T' ⟶ G')), (List.ofFn fun j => δ ≫ a j).prod = δ ≫ (List.ofFn a).prod := by
    intro m a
    induction m with
    | zero => simp [MonObj.comp_one]
    | succ m ih => rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, MonObj.comp_mul, ih]
  rw [h2] at h1
  exact ((Category.id_comp _).symm.trans h1.symm).trans (Category.assoc _ _ _)

theorem comb_match {V K F : Type} [CommRing V] [CommRing K] [CommRing F] {X : Scheme.{0}} {B : Over X} [GrpObj B]
    {G₁ : Over (Sp V)} [GrpObj G₁] {G₂ : Over (Sp K)} [GrpObj G₂] {f₁ : Sp V ⟶ X} {f₂ : Sp K ⟶ X}
    {φ₁ : G₁.left ⟶ B.left} {φ₂ : G₂.left ⟶ B.left} (h₁ : IsGrpPullback G₁ B f₁ φ₁) (h₂ : IsGrpPullback G₂ B f₂ φ₂)
    (α : V →+* F) (β : K →+* F) (hf : spMap α ≫ f₁ = spMap β ≫ f₂) {m : ℕ} {v₁ : Fin m → (epsR V ⟶ G₁)}
    {v₂ : Fin m → (epsR K ⟶ G₂)}
    (hv : ∀ i, spMap (dualMap α) ≫ (v₁ i).left ≫ φ₁ = spMap (dualMap β) ≫ (v₂ i).left ≫ φ₂)
    {c₁ : Fin m → V} {c₂ : Fin m → K} (hc : ∀ i, α (c₁ i) = β (c₂ i)) {w₁ : epsR V ⟶ G₁} {w₂ : epsR K ⟶ G₂}
    (hw₁ : IsLieComb c₁ v₁ w₁) (hw₂ : IsLieComb c₂ v₂ w₂) :
    spMap (dualMap α) ≫ w₁.left ≫ φ₁ = spMap (dualMap β) ≫ w₂.left ≫ φ₂ := by
  obtain ⟨u₁, hu₁, rfl⟩ := hw₁
  obtain ⟨u₂, hu₂, rfl⟩ := hw₂
  let T : Over X := Over.mk (spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁)
  have e₁ : spMap (dualMap α) ≫ spMap (algebraMap V (DualNumber V)) ≫ f₁ =
      spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁ := by
    rw [← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_alg]
  have e₂ : spMap (dualMap β) ≫ spMap (algebraMap K (DualNumber K)) ≫ f₂ =
      spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁ := by
    rw [hf, ← Category.assoc, ← Category.assoc, spMap_comp₂, spMap_comp₂, dualMap_alg]
  let Z : Fin m → (T ⟶ B) := fun i => Over.homMk (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) (by
    show (spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁) ≫ B.hom = spMap (algebraMap F (DualNumber F)) ≫ spMap α ≫ f₁
    rw [Category.assoc, Category.assoc, h₁.1.w, ← Category.assoc (u₁ i).left, Over.w (u₁ i)]
    exact e₁)
  have k₁ := prod_pull h₁ (epsR V) T (spMap (dualMap α)) e₁ u₁ Z (fun _ => rfl)
  have k₂ := prod_pull h₂ (epsR K) T (spMap (dualMap β)) e₂ u₂ Z (fun i => by
    show spMap (dualMap α) ≫ (u₁ i).left ≫ φ₁ = _
    have a₁ : spMap (dualMap α) ≫ spMap (epsScaleR (c₁ i)) = spMap (epsMul (α (c₁ i))) ≫ spMap (dualMap α) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]; rfl
    have a₂ : spMap (dualMap β) ≫ spMap (epsScaleR (c₂ i)) = spMap (epsMul (β (c₂ i))) ≫ spMap (dualMap β) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]; rfl
    rw [hu₁ i, hu₂ i, Category.assoc, Category.assoc, reassoc_of% a₁, reassoc_of% a₂, hv i, hc i])
  exact k₁.symm.trans k₂

theorem comb_eq_scale {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
    {v wK : Fin n → (epsR K ⟶ G)} (hv : ∀ i, IsTangent (v i)) {A : Matrix (Fin n) (Fin n) K} (hA : A.det ≠ 0)
    (hw : ∀ i, IsLieComb (A i) v (wK i)) {U : Fin n → K} {w : epsR K ⟶ G} (hU : IsLieComb U v w) (cl : K)
    {s : epsR K ⟶ G} (hs : IsLieComb (Matrix.vecMul (cl • U) A⁻¹) wK s) :
    s.left = spMap (epsMul cl) ≫ w.left := by
  obtain ⟨h1, -, h3, -⟩ := LieComb.lieComb_algebra K G n v hv
  let s' : epsR K ⟶ G := Over.homMk (spMap (epsMul cl) ≫ w.left) (by
    show (spMap (epsMul cl) ≫ w.left) ≫ G.hom = spMap (algebraMap K (DualNumber K))
    rw [Category.assoc, Over.w w]
    exact (spMap_comp₂ _ _).trans (congrArg spMap (epsMul_alg cl)))
  have a₁ := h3 n A wK _ s hw hs
  have a₂ := h3 1 (fun _ => U) (fun _ => w) (fun _ => cl) s' (fun _ => hU) ⟨fun _ => s', fun _ => rfl, by simp⟩
  have e : ∑ i, Matrix.vecMul (cl • U) A⁻¹ i • A i = ∑ _i : Fin 1, cl • U := by
    rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hA), Matrix.vecMul_one]
    simp
  rw [e] at a₁
  rw [(h1 _).unique a₁ a₂]
  rfl

theorem epsMul_comm {R : Type} [CommRing R] (a b : R) :
    spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsMul a) := by
  rw [spMap_comp₂, spMap_comp₂]
  congr 1
  apply RingHom.ext
  intro r
  ext <;> simp [epsMul, mul_left_comm]

theorem dualMap_inj {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (dualMap f) := by
  intro a b h
  have h₁ := congrArg TrivSqZeroExt.fst h
  have h₂ := congrArg TrivSqZeroExt.snd h
  simp [dualMap] at h₁ h₂
  exact TrivSqZeroExt.ext (hf h₁) (hf h₂)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem coord_eq {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (b : E →+* ℂ)
    (u' : Fin (Dw.mult b) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S)
    (hg : IsUnit g.det) (hu : ∀ i, IsCombAt y.x (y.u b) (g i) (u' i)) (r : S) (j : Fin (Dw.mult b))
    (a : Fin (Dw.mult b) → S) (ha : IsCombAt y.x u' a (spMap (epsMul r) ≫ y.u b j)) (k : Fin (Dw.mult b)) :
    r * g⁻¹ j k = a k := by
  classical
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, hsm⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  choose β hβ using fun i => (htan _).1 (y.tan b i)
  have hy : y.u b = fun i => v (β i) := funext fun i => (hβ i).symm
  have hu' : u' = fun i => v (∑ j, g i j • β j) := funext fun i => (hcomb _ β _ _).1 (hy ▸ hu i)
  have hw : spMap (epsMul r) ≫ y.u b j = v (r • β j) := by rw [hsm, hβ]
  have ht : IsTanAt y.x (spMap (epsMul r) ≫ y.u b j) := (htan _).2 ⟨_, hw.symm⟩
  have he : IsEigAt c b (spMap (epsMul r) ≫ y.u b j) := fun a => by
    rw [Category.assoc, y.eig b j a, ← Category.assoc, epsMul_comm, Category.assoc]
  have h1 := (hcomb _ (fun i => ∑ j, g i j • β j) _ _).1 (hu' ▸ ha)
  have h2 : IsCombAt y.x (y.u b) (Matrix.vecMul a g) (spMap (epsMul r) ≫ y.u b j) := by
    rw [hy]
    refine (hcomb _ β _ _).2 ((hy ▸ h1).trans (congrArg v ?_))
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have h3 : IsCombAt y.x (y.u b) (Pi.single j r) (spMap (epsMul r) ≫ y.u b j) := by
    rw [hw, hy]
    refine (hcomb _ β _ _).2 (congrArg v ?_)
    simp [Pi.single_apply]
  have h4 := (y.basis b _ ht he).unique h2 h3
  have h5 : a = Matrix.vecMul (Pi.single j r) g⁻¹ := by
    rw [← h4, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hg, Matrix.vecMul_one]
  rw [h5]
  simp [Matrix.vecMul, dotProduct, Pi.single_apply]

theorem isEigV_of_generic {V K : Type} [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Algebra c.F K]
    {x : Sp K ⟶ Xo.X} {G : SAB H (Sp V)} [IsSeparated G.G.hom] {t : SAB H (Sp K)} (m₁ : SABMap t Xo.univ.t x)
    (m₂ : SABMap t G (spMap (algebraMap V K))) (b : E →+* ℂ) (w : epsOver V V ⟶ G.G)
    (w' : Sp (DualNumber K) ⟶ t.G.left) (hw : w' ≫ m₂.φ = spMap (dualMap (algebraMap V K)) ≫ w.left)
    (ho : w' ≫ t.G.hom = spMap (algebraMap K (DualNumber K))) (he : IsEigAt c b (w' ≫ m₁.φ)) :
    IsEigV c (algebraMap c.F K) G b w := by
  intro a z hz
  have h1 : w' ≫ (t.act.act a).left = spMap (epsMul (algebraMap V K z)) ≫ w' := by
    apply m₁.cart.1.hom_ext
    · rw [Category.assoc, m₁.act a, ← Category.assoc, he a, hz, Category.assoc]
    · rw [Category.assoc, Over.w, Category.assoc, ho, spMap_comp₂, epsMul_alg]
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom (dualMap (algebraMap V K)))
    (dualMap_inj _ (IsFractionRing.injective V K))
  refine ExtUnique.hom_ext_of_dominant G.G.hom ?_ (spMap (dualMap (algebraMap V K))) ?_
  · rw [Over.w, Category.assoc, Over.w]
    exact ((spMap_comp₂ _ _).trans (congrArg spMap (epsMul_alg z))).symm
  · have a₁ : spMap (dualMap (algebraMap V K)) ≫ spMap (epsMul z) =
        spMap (epsMul (algebraMap V K z)) ≫ spMap (dualMap (algebraMap V K)) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]
    rw [Over.comp_left, ← reassoc_of% hw, ← m₂.act a, reassoc_of% h1, reassoc_of% a₁, ← hw]


set_option maxHeartbeats 1000000 in
theorem letter_integral_in_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → (∀ b, IsUnit (g b).det) → LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → ∀ (b : E →+* ℂ) (j k : Fin (Dw.mult b)) (cl : z.K), IsLocGen p cl (z.ℓ (z.e ⟨b, j⟩)).I → iK cl * (g b)⁻¹ j k ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz p T iK M hval
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint b j k cl hcl
  obtain ⟨hobj, hlet, -, hx, -, hu⟩ := hz
  obtain ⟨A, hA, -⟩ := hobj.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  have hcint := LamF.letter_integral_of_isLocGen E H l c _ _ f z.obj La hobj z.letters hlet p A hA (z.e ⟨b, j⟩) cl hcl
  obtain ⟨vV, hvV, hvw⟩ := GlobalTheory.T.exists_lieBasis_local_model E H Dw l Xo c z p T iK M hval A hA
  choose wK hwK hwV using hvw
  have hdet : A.det ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ := hA
    exact h
  choose cV hcV using fun m => (hval _).2 (hcint m)
  obtain ⟨w, hw, hwu⟩ := hu b j
  obtain ⟨w₀, hw₀, hU⟩ := hlet.2.2.1 (z.e ⟨b, j⟩)
  obtain rfl : w₀ = w := by
    refine Over.OverMorphism.ext (z.m'.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    unfold LamF.LamLetters.IsLetter at hw hw₀
    generalize z.letters.src (z.e ⟨b, j⟩) = s at hw hw₀
    rcases s with q | q
    · exact hw₀.trans hw.symm
    · exact hw₀.trans hw.symm
  have hK := LieComb.lieComb_algebra z.K z.Φ.T.t.G _ z.Φ.v z.Φ.basis.1
  obtain ⟨s, hs, -⟩ := (LieComb.lieComb_algebra z.K z.Φ.T.t.G _ wK (fun i => hK.2.1 _ _ (hwK i))).1
    (Matrix.vecMul (cl • z.U (z.e ⟨b, j⟩)) A⁻¹)
  have hV := LieComb.lieComb_algebra T.V M.G.t.G _ vV hvV.1
  obtain ⟨W, hW, -⟩ := hV.1 cV
  have hWt := hV.2.1 _ _ hW
  have hbase : spMap (algebraMap T.V T.Fr) ≫ spMap M.ρ = spMap iK ≫ spMap (algebraMap (𝓞 z.K) z.K) := by
    rw [spMap_comp₂, spMap_comp₂, M.hρ]
  have hmatch := comb_match M.n.cart z.m'.cart (algebraMap T.V T.Fr) iK hbase hwV hcV hW hs
  have hsl := comb_eq_scale z.Φ.basis.1 hdet hwK hU cl hs
  have hsq : (spMap (dualMap iK) ≫ s.left) ≫ z.Φ.T.t.G.hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap iK := by
    rw [Category.assoc, Over.w s]
    exact (spMap_comp₂ _ _).trans ((congrArg spMap (dualMap_alg iK)).trans (spMap_comp₂ _ _).symm)
  let s' : Sp (DualNumber T.Fr) ⟶ M.t'.t.G.left := M.n'.cart.1.lift _ _ hsq
  have hs1 : s' ≫ M.n'.φ = spMap (dualMap iK) ≫ s.left := M.n'.cart.1.lift_fst _ _ _
  have hs2 : s' ≫ M.t'.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := M.n'.cart.1.lift_snd _ _ _
  let W' : epsOver T.V T.V ⟶ M.G.t.G := Over.homMk W.left (Over.w W)
  have hm2 : s' ≫ M.m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ W'.left := by
    apply M.n.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc]
      refine Eq.trans ?_ hmatch.symm
      exact (congrArg (s' ≫ ·) M.h2).trans (by rw [reassoc_of% hs1])
    · rw [Category.assoc, M.m2.cart.1.w, reassoc_of% hs2, Category.assoc, Over.w W']
      exact (spMap_comp₂ _ _).trans ((congrArg spMap (dualMap_alg _).symm).trans (spMap_comp₂ _ _).symm)
  have hm1 : s' ≫ M.m1.φ = spMap (epsMul (iK cl)) ≫ yT.u b j := by
    have a₁ : spMap (dualMap iK) ≫ spMap (epsMul cl) = spMap (epsMul (iK cl)) ≫ spMap (dualMap iK) := by
      rw [spMap_comp₂, spMap_comp₂, ← dualMap_epsMul]
    rw [M.h1, reassoc_of% hs1, hsl, Category.assoc, reassoc_of% a₁, hmap.2.1 b j, hφ, hwu]
  have hW't : IsTan W' := by
    unfold IsTan
    refine hWt.trans ?_
    have e : (1 : ptOver T.V T.V ⟶ M.G.t.G) = toUnit _ ≫ η[M.G.t.G] := rfl
    rw [e, Over.comp_left]
    have e2 : (toUnit (ptOver T.V T.V)).left = 𝟙 (Sp T.V) := by
      have := Over.w (toUnit (ptOver T.V T.V))
      exact ((Category.comp_id _).symm.trans this).trans (Spec.map_id _)
    rw [e2]
    exact (Category.id_comp _).symm
  have := M.G.ab.proper
  have hW'e : IsEigV c (iK.comp (algebraMap c.F z.K)) M.G.t b W' :=
    isEigV_of_generic M.m1 M.m2 b W' s' hm2 hs2 (fun a => by
      rw [hm1, Category.assoc, yT.eig b j a, ← Category.assoc, epsMul_comm, Category.assoc])
  obtain ⟨ub, -, -, hb, hl⟩ := hint
  obtain ⟨aV, haV, -⟩ := hb b W' hW't hW'e
  choose u' hu1 hu2 using hl b
  have hgen := comb_generic M.m1 M.m2 (ub b) u' hu2 W' s' hm2 aV haV
  have hxT : spMap iK ≫ z.x = yT.x := by rw [hmap.1, hφ, hx]
  rw [hm1, funext hu1] at hgen
  have hgen' : IsCombAt yT.x (y'.u b) (fun j => algebraMap T.V T.Fr (aV j))
      (spMap (epsMul (iK cl)) ≫ yT.u b j) := hxT ▸ hgen
  exact ⟨aV k, (coord_eq yT b (y'.u b) (g b) (hg b) (hchg.2.1 b) (iK cl) j _ hgen' k).symm⟩

end GlobalTheory.LamT.LetterInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open Formalism.L2.Pj hiding dualMap_alg
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (p : HeightOneSpectrum (𝓞 z.K)) (T : CDVR) (iK : z.K →+* T.Fr) (M : LocMod z T iK), (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → letI := (iK.comp (algebraMap c.F z.K)).toAlgebra; ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr) (g : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr)) (a : T.Fr), φ.toRingHom = iK → FrMap φ z.y yT → FrChg g a yT y' → (∀ b, IsUnit (g b).det) → LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u → ∀ (b : E →+* ℂ) (j k : Fin (Dw.mult b)) (cl : z.K), IsLocGen p cl (z.ℓ (z.e ⟨b, j⟩)).I → iK cl * (g b)⁻¹ j k ∈ Set.range (algebraMap T.V T.Fr) := by
  first | exact @GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis | exact GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis | (intros; apply GlobalTheory.LamT.LetterInt.letter_integral_in_eigenbasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationDetLeOneOfEntries
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem valuation_det_le_one_of_entries {K G J : Type} [Field K] [LinearOrderedCommGroupWithZero G]
    [Fintype J] [DecidableEq J] (v : Valuation K G) (N : Matrix J J K) (h : ∀ i j, v (N i j) ≤ 1) :
    v N.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le fun σ _ => ?_
  have hp : v (∏ i, N (σ i) i) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one' fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hp
  · rw [hs, Units.neg_smul, one_smul, Valuation.map_neg]; exact hp

theorem valuation_prod_mul_det_le {K G J : Type} [Field K] [LinearOrderedCommGroupWithZero G]
    [Fintype J] [DecidableEq J] (v : Valuation K G) (U M : Matrix J J K) (c : J → K) (hM : M.det ≠ 0)
    (h : ∀ k m, v (Matrix.vecMul (c k • U k) M⁻¹ m) ≤ 1) :
    v ((∏ k, c k) * U.det) ≤ v M.det := by
  have hN : v (Matrix.diagonal c * U * M⁻¹).det ≤ 1 := by
    refine valuation_det_le_one_of_entries v _ fun k m => ?_
    have hk : (Matrix.diagonal c * U) k = c k • U k := by
      funext j
      simp [Matrix.diagonal_mul]
    have : (Matrix.diagonal c * U * M⁻¹) k m = Matrix.vecMul (c k • U k) M⁻¹ m := by
      rw [← hk]; rfl
    rw [this]; exact h k m
  have hvM : v M.det ≠ 0 := (Valuation.ne_zero_iff v).2 hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
    map_mul, map_inv₀, ← div_eq_mul_inv, div_le_one₀ (zero_lt_iff.2 hvM)] at hN
  exact hN

theorem letters_det_valuation_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (p : HeightOneSpectrum (𝓞 o.K₁)) (cd : o.K₁) (cl : Fin o.xB.P.g → o.K₁), IsLocGen p cd o.LamL.I → (∀ k, IsLocGen p (cl k) (L.ℓ k).I) → p.valuation o.K₁ ((∏ k, cl k) * L.U.det) ≤ p.valuation o.K₁ cd := by
  intro E _ _ _ _ H l c nΨ n' f o La ho L hL p cd cl hcd hcl
  obtain ⟨M, hM, hdet⟩ := ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  have hv : p.valuation o.K₁ M.det = p.valuation o.K₁ cd := by
    rw [(isLocGen_iff_valuation_eq p _ _).1 hdet, (isLocGen_iff_valuation_eq p _ _).1 hcd]
  rw [← hv]
  exact valuation_prod_mul_det_le _ L.U M cl hdet.1 fun k m =>
    GlobalTheory.T.lieLetter_integral_of_local_generator E H l c nΨ n' f o La ho L hL p M hM k (cl k) (hcl k) m

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekind
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekind
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.AmpleDedekind

theorem range_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Set.range (spMap (algebraMap R K)) = {genericPoint (Sp R)} := by
  have h : ∀ p : Sp K, spMap (algebraMap R K) p = genericPoint (Sp R) := fun p => by
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap R K) (PrimeSpectrum.asIdeal p) = ⊥
    have hp : PrimeSpectrum.asIdeal p = ⊥ := Ideal.eq_bot_of_prime (K := K) _ (h := p.isPrime)
    rw [hp]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  exact Set.eq_singleton_iff_unique_mem.2
    ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), h _⟩, by rintro _ ⟨p, rfl⟩; exact h p⟩

theorem relAmple_of_generic_of_isogenous : Out.Laws → Out.Laws2 → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (B : Over (Sp R)) [GrpObj B] (Ψ : P.A ⟶ B) (M : LB B.left) (B₀ : Over (Sp K)) [GrpObj B₀] (φ : B₀.left ⟶ B.left) (M₀ : LB B₀.left), IsAbelianScheme B → M.IsLB → M₀.IsLB → IsFinite Ψ.left → Flat Ψ.left → Surjective Ψ.left → IsGrpPullback B₀ B (spMap (algebraMap R K)) φ → LBIso M₀ (M.pull φ) → Out.RelAmple B₀ M₀ → Out.RelAmple B M := by
  intro h₁ h₂ R K _ _ _ _ _ P B _ Ψ M B₀ _ φ M₀ hB hM hM₀ hfin hfl hsurj hpb hiso hamp
  have := hB.proper
  have := P.isAb.proper
  have hsq := hpb.1
  have : IsProper B₀.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have a₀ : IsAmpleLB (M.pull φ) :=
    (isAmpleLB_congr hM₀ (LB.isLB_pull hM φ) hiso).1 ((relAmple_iff_isAmpleLB_of_isAffine B₀ hM₀).1 hamp)
  let x := spMap (algebraMap R K)
  let g : pullback P.A.hom x ⟶ B₀.left :=
    hsq.lift (pullback.fst P.A.hom x ≫ Ψ.left) (pullback.snd P.A.hom x)
      (by rw [Category.assoc, Over.w Ψ]; exact pullback.condition)
  have e₁ : g ≫ φ = pullback.fst P.A.hom x ≫ Ψ.left := hsq.lift_fst _ _ _
  have e₂ : g ≫ B₀.hom = pullback.snd P.A.hom x := hsq.lift_snd _ _ _
  have sq : IsPullback (pullback.fst P.A.hom x) g Ψ.left φ := by
    refine IsPullback.of_bot ?_ e₁.symm hsq
    rw [e₂, Over.w Ψ]
    exact IsPullback.of_hasPullback _ _
  have : IsFinite g := MorphismProperty.of_isPullback (P := @IsFinite) sq hfin
  have hΨ := LB.isLB_pull hM Ψ.left
  have a₁ : IsAmpleLB ((M.pull Ψ.left).pull (pullback.fst P.A.hom x)) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM φ) g) (LB.isLB_pull hΨ _)
      (FiniteAmple.lbIso_pull_pull φ hM e₁)).1 (a₀.pull_of_isFinite g)
  have : IsProper ((Over.pullback x).obj P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd P.A.hom x))
  have a₂ : Out.RelAmple P.A (M.pull Ψ.left) :=
    AmpleSpecialisation.relAmple_of_genericFibre h₁ h₂ (Sp R) P (M.pull Ψ.left) K x hΨ (range_spMap_fractionRing R K)
      ((relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback x).obj P.A) (LB.isLB_pull hΨ _)).2 a₁)
  exact (relAmple_finite_pow_iso (Sp R) P.A B Ψ M 1 one_pos P.isAb hB hM hfin).2.2.1 hfl hsurj a₂

end GlobalTheory.AmpleDedekind
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekindStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_of_generic_isogenous_dedekind : Out.Laws → Out.Laws2 → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (B : Over (Sp R)) [GrpObj B] (Ψ : P.A ⟶ B) (M : LB B.left) (B₀ : Over (Sp K)) [GrpObj B₀] (φ : B₀.left ⟶ B.left) (M₀ : LB B₀.left), IsAbelianScheme B → M.IsLB → M₀.IsLB → IsFinite Ψ.left → Flat Ψ.left → Surjective Ψ.left → IsGrpPullback B₀ B (spMap (algebraMap R K)) φ → LBIso M₀ (M.pull φ) → Out.RelAmple B₀ M₀ → Out.RelAmple B M := by
  first | exact @GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous | exact GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous | (intros; apply GlobalTheory.AmpleDedekind.relAmple_of_generic_of_isogenous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DegOfLatRankEqZero
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.DegBound

section Lattice

variable {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

end Lattice

variable {K : Type} [Field K] [NumberField K] {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [NumberField K] in
theorem eigLat_le {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {O : Type} [CommRing O] (act : OAct O P.A)
    (τ : O →+* 𝓞 K) : F.eigLat act τ ≤ F.lieLat :=
  Submodule.span_mono fun _ ⟨u, hu, _⟩ => ⟨u, hu⟩

theorem eigLat_fg {P : Out.PolAV (Sp (𝓞 K))} (F : GenFib P) {O : Type} [CommRing O] (act : OAct O P.A)
    (τ : O →+* 𝓞 K) : (F.eigLat act τ).FG := by
  have := isNoetherian_of_fg_of_noetherian _ (LieLattice.lieLat_fg_and_span_eq_top K P F).1
  exact Submodule.FG.of_le_of_isNoetherian (eigLat_le F act τ)

end GlobalTheory.CM.DegBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamLenOfIsHerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem lamLen_of_isHerm : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (hf : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB) (h : HermFam o.K₁ (Fin o.xB.P.g → o.K₁)), (GenFib.mk o.xB.P o.φB hf o.xB.v o.xB.basis : GenFib o.B).IsHerm h → ∀ (σ : o.K₁ →+* ℂ), o.LamL.n σ = Real.sqrt (h.gram σ (fun i : Fin o.xB.P.g => Pi.single i 1)).det.re ∧ ∀ k, (h.form σ (L.U k) (L.U k)).re ≤ (La * (L.ℓ k).n σ) ^ 2 := by
  intro hU hL E _ _ _ _ H l c nΨ n' f o La hG L hLg hp h Hh σ
  obtain ⟨-, -, -, -, hΨ, hA', -, -, -, tΨ, t', -, -, hI, hP, hb, vΨ, v', -, hgood, -, harch, -⟩ := hG
  refine ⟨?_, fun k => ?_⟩
  · have := GlobalTheory.CM.TopLieVector.sq_eq_det_gram hU hL o.K₁ o.B o.xB o.φB hp h Hh o.Tl o.LamL σ (harch σ)
    exact ((congrArg Real.sqrt this).symm.trans (Real.sqrt_sq (hgood.2 σ).le)).symm
  · obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 k
    have h4 := hLg.2.2.2 k
    unfold LamLetters.IsLetter at hw1
    cases hs : L.src k with
    | inl q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.AΨ o.B o.oaΨ o.xΨ o.φΨg (S := psiSet H) o.τΨ _ hΨ tΨ
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φΨ q.1) (hI.1 _) (o.hΨ q.1) (hP.2.2.1 q.1) La
        (hb.1 q.1) q.2 _ (vΨ q.2) _ w hw2 hw1 σ
    | inr q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.A' o.B o.oa' o.x' o.φ'g (S := (psiSet H)ᶜ) o.τ' _ hA' t'
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φ' q.1) (hI.2.1 _) (o.h' q.1) (hP.2.2.2 q.1) La
        (hb.2 q.1) q.2 _ (v' q.2) _ w hw2 hw1 σ

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorDecompositionPureTypeCmTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyTensorOfOntoFullFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyTensorOfOntoFullFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem OntoAt.exists_eq_comp {S : Scheme.{0}} {I : Type} {B : I → Over S} {A A' : Over S} [GrpObj A] [GrpObj A']
    {φ : ∀ i, B i ⟶ A} {k : Type} [Field k] {t : Sp k ⟶ S} (hφ : OntoAt φ t) (Φ : A' ⟶ A) [IsMonHom Φ]
    (χ : ∀ i, B i ⟶ A') (e : ∀ i, χ i ≫ Φ = φ i) (y : Over.mk t ⟶ A) : ∃ x : Over.mk t ⟶ A', y = x ≫ Φ := by
  obtain ⟨n, i, x, rfl⟩ := hφ y
  refine ⟨(List.ofFn fun m => x m ≫ χ (i m)).prod, ?_⟩
  let F : (Over.mk t ⟶ A') →* (Over.mk t ⟶ A) :=
    MonoidHom.mk' (fun z => z ≫ Φ) fun z w => MonObj.mul_comp z w Φ
  change _ = F _
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext m
  simp [F, e]

theorem nonempty_isTen_of_isFam_top : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (σ : R →+* ℂ) (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (ψ : (⊤ : Submodule (𝓞 E) D.La) → (C.P.A ⟶ T.t.G)), Function.Injective σ → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → IsFam C T h ⊤ ψ → OntoAt ψ (spMap σ) → Nonempty (IsTen C D h T) := by
  intro hL E _ _ _ H R _ _ _ σ ω C D ε h T ψ hσ hh hpos hfam honto
  obtain ⟨T₁, ⟨t⟩, -⟩ := GlobalTheory.T.exists_cm_tensor_lattice_curve_principal_triple hL E H R ω C D ε h hh hpos
  obtain ⟨Φ, hlin, htm, hlam⟩ := GlobalTheory.T.exists_tensorProduct_hom_of_cmCurveHomFamily E H R ω C D D ε h h T₁ T t ⊤ ψ
    (Submodule.topEquiv.symm : D.La ≃ₗ[𝓞 E] (⊤ : Submodule (𝓞 E) D.La)).toLinearMap 1 hh hh
    (fun a b => by rw [one_smul]; rfl) hfam
  rw [T₁.t.act.one] at hlam
  have hm : IsMonHom Φ := hlin.isMonHom
  have hsurj := (GlobalTheory.T.abelianScheme_surjective_of_onto_complex_points R σ hσ T.t.G T₁.t.G Φ T.ab T₁.ab
    (honto.exists_eq_comp Φ (fun a => t.ten.tmul a.1) fun a => htm a.1)).1
  have hred : IsReduced (Sp R) := inferInstanceAs (IsReduced (Spec (CommRingCat.of R)))
  have hiso : IsIso Φ := GlobalTheory.T.isIso_of_surjective_principalPairing (Sp R) T₁.t.G T.t.G T₁.t.PP.L T.t.PP.L Φ T₁.ab T.ab T₁.t.PP.isLB T.t.PP.isLB hm
    T₁.ktriv hlam hsurj
  have key : ∀ a, (t.ten.ofIso (b' := Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (asIso Φ)
      ⟨hm, fun c => hlin.comm _⟩).tmul a = ψ ⟨a, trivial⟩ := fun a => htm a
  refine ⟨⟨t.ten.ofIso (asIso Φ) ⟨hm, fun c => hlin.comm _⟩, fun s a => ?_, fun a b => ?_⟩⟩
  · rw [key, key]
    exact hfam.2.2.1 s ⟨a, trivial⟩
  · rw [key, key]
    exact hfam.2.2.2 ⟨a, trivial⟩ ⟨b, trivial⟩

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyTensorOfOntoFullFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_tensor_of_onto_full_family : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (σ : R →+* ℂ) (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (ψ : (⊤ : Submodule (𝓞 E) D.La) → (C.P.A ⟶ T.t.G)), Function.Injective σ → IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → IsFam C T h ⊤ ψ → OntoAt ψ (spMap σ) → Nonempty (IsTen C D h T) := by
  first | exact @GlobalTheory.CM.nonempty_isTen_of_isFam_top | exact GlobalTheory.CM.nonempty_isTen_of_isFam_top | (intros; apply GlobalTheory.CM.nonempty_isTen_of_isFam_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorDecompositionPureTypeCmTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Recog

theorem ontoAt_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {I : Type} {B A : Over S} {B' A' : Over S'}
    [GrpObj A] [GrpObj A'] {φ : B'.left ⟶ B.left} {χ : A'.left ⟶ A.left} (hφ : φ ≫ B.hom = B'.hom ≫ f)
    (hχ : IsGrpPullback A' A f χ) {ψ : I → (B ⟶ A)} {ψ' : I → (B' ⟶ A')}
    (hψ : ∀ i, (ψ' i).left ≫ χ = φ ≫ (ψ i).left) {k : Type} [Field k] {t' : Sp k ⟶ S'} {t : Sp k ⟶ S}
    (ht : t = t' ≫ f) (h : OntoAt (B := fun _ => B') ψ' t') : OntoAt (B := fun _ => B) ψ t := by
  intro y
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hχ t' t ht
  obtain ⟨n, i, x, hx⟩ := h (e.symm y)
  refine ⟨n, i, fun m => Over.homMk ((x m).left ≫ φ) ?_, ?_⟩
  · have hw := Over.w (x m)
    simp only [Over.mk_hom] at hw ⊢
    rw [Category.assoc, hφ, ← Category.assoc, hw, ht]
  · calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = (List.ofFn fun m => e (x m ≫ ψ' (i m))).prod := by
        rw [hx, map_list_prod, List.map_ofFn]; rfl
      _ = _ := by
        congr 1
        refine List.ofFn_inj.mpr (funext fun m => ?_)
        apply Over.OverMorphism.ext
        rw [he, Over.comp_left, Over.comp_left, Category.assoc, hψ]
        rfl

private lemma spMap_comp_moduli_spaces {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_isTen_of_hasType : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [NumberField k] (ω : 𝓞 k) (C : Ell H (𝓞 k) ω) (T : PAT H (Sp (𝓞 k))) (r : ℕ), C.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) → HasType H T.t.act (2 * ω - 1) r 0 →
  ∃ (k₁ : IntermediateField ℚ ℂ) (_ : NumberField k₁) (hk : k ≤ k₁) (ω₁ : 𝓞 k₁) (C₁ : Ell H (𝓞 k₁) ω₁) (φ : C₁.P.A.left ⟶ C.P.A.left) (T₁ : PAT H (Sp (𝓞 k₁))) (_ : SABMap T₁.t T.t (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom))) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), EllMap C₁ C (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) φ ∧ D.p + D.q = r ∧ IsKForm D ε h ∧ (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ Nonempty (IsTen C₁ D h T₁) := by
  intro hU hL hD E _ _ _ H k _ ω C T r hP hT
  have hB : Out.PolBaseChangeSt := hL.polBaseChange

  obtain ⟨Ck, φk, hCk⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k) ω C k (algebraMap (𝓞 k) k)
  obtain ⟨Tk, mk, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap (𝓞 k) k)) T
  obtain ⟨Cc, φc, hCc⟩ := GlobalTheory.CM.exists_ellMap hB E H k _ Ck ℂ (algebraMap k ℂ)
  obtain ⟨Tc, mc, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap k ℂ)) Tk
  have hPk : Ck.IsPrincipalAt (algebraMap k ℂ) :=
    (GlobalTheory.CM.EllComp.ellMap_comp E H (𝓞 k) ω C k _ Ck (algebraMap (𝓞 k) k) φk hCk).2.1 _ hP
  have hPc : Cc.IsPrincipalAt (RingHom.id ℂ) :=
    (GlobalTheory.CM.EllComp.ellMap_comp E H k _ Ck ℂ _ Cc (algebraMap k ℂ) φc hCc).2.1 _ (by rwa [RingHom.id_comp])
  obtain ⟨nc, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mk mc
  rw [spMap_comp_moduli_spaces] at nc
  have hinj : Function.Injective ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    rw [RingHom.coe_comp]
    exact (algebraMap k ℂ).injective.comp (IsFractionRing.injective (𝓞 k) k)
  have hTc := (GlobalTheory.CM.hasType_baseChange E H (𝓞 k) ℂ _ T.t Tc.t nc (2 * ω - 1) r 0).1 hinj hT
  have hωc : ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) (2 * ω - 1) =
      2 * algebraMap k ℂ (algebraMap (𝓞 k) k ω) - 1 := by
    simp only [map_sub, map_mul, map_ofNat, map_one, RingHom.comp_apply]
  rw [hωc] at hTc

  obtain ⟨D, ε, h, ψc, hpq, hK, hpos, hFc, hOc⟩ := GlobalTheory.T.exists_homFamily_of_pureType_complex_triple hU hL E H _ Cc Tc r hPc hTc

  obtain ⟨k₁, hfin, hk, huniv⟩ := GlobalTheory.T.cmFamily_descends_to_numberField hU hL E H k _ Ck D h Tk ⊤ _ Cc φc Tc mc ψc hCc hFc
  have : FiniteDimensional ℚ k₁ := hfin
  have : NumberField k₁ := ⟨⟩
  obtain ⟨C₁, φ₁, hC₁⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k) ω C (𝓞 k₁)
    (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom)
  obtain ⟨T₁, m₁, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _
    (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom)) T
  obtain ⟨C₂, φa, hC₂⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k₁) _ C₁ k₁ (algebraMap (𝓞 k₁) k₁)
  obtain ⟨T₂, ma, -⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ (spMap (algebraMap (𝓞 k₁) k₁)) T₁
  have hring : (algebraMap (𝓞 k₁) k₁).comp
      (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) =
      (IntermediateField.inclusion hk).toRingHom.comp (algebraMap (𝓞 k) k) := by
    ext x; rfl
  have hring' : (algebraMap k₁ ℂ).comp (IntermediateField.inclusion hk).toRingHom = algebraMap k ℂ := by
    ext x; rfl
  have h21 := (GlobalTheory.CM.EllComp.ellMap_comp E H (𝓞 k) ω C (𝓞 k₁) _ C₁ _ φ₁ hC₁).1 k₁ _ C₂ _ φa hC₂
  rw [hring] at h21
  obtain ⟨φ₂, hφ₂, -⟩ := GlobalTheory.CM.Factor.ellMap_cancel hCk h21
  have hCc' : EllMap Cc Ck ((algebraMap k₁ ℂ).comp (IntermediateField.inclusion hk).toRingHom) φc := by
    rw [hring']; exact hCc
  obtain ⟨φ₃, hφ₃, hφ₃c⟩ := GlobalTheory.CM.Factor.ellMap_cancel hφ₂ hCc'
  obtain ⟨n21, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ ma
  obtain ⟨m₂, -⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H k k k₁ (RingHom.id k)
    (IntermediateField.inclusion hk).toRingHom).2 _ _ _ T.t Tk.t T₂.t mk n21
    (by rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, hring])
  obtain ⟨m₃, hm₃⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H k₁ k₁ ℂ (RingHom.id k₁)
    (algebraMap k₁ ℂ)).2 _ _ _ Tk.t T₂.t Tc.t m₂ mc (by rw [spMap_comp_moduli_spaces, hring'])
  obtain ⟨ψ₂, hF₂, hψ₂⟩ := huniv k₁ hk le_rfl _ C₂ φ₂ φ₃ T₂ m₂ m₃ hφ₂ hφ₃ hφ₃c hm₃

  obtain ⟨ψ₁, hF₁, hψ₁⟩ := GlobalTheory.T.cmFamily_extends_over_dedekindDomain hL hD E H (𝓞 k₁) k₁ _ C₁ D h T₁ ⊤ _ C₂ φa T₂ ma ψ₂ hC₂ hF₂

  obtain ⟨n1, hn1⟩ := GlobalTheory.ObjMaps.exists_sab_comp ma m₃
  obtain ⟨-, ⟨-, ⟨hsq3, -⟩, -⟩, -⟩ := hφ₃
  obtain ⟨-, ⟨-, ⟨hsqa, -⟩, -⟩, -⟩ := hC₂
  have hOnto : OntoAt ψ₁ (spMap ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁))) := by
    refine ontoAt_of_isGrpPullback (φ := φ₃ ≫ φa) (χ := n1.φ) ?_ n1.cart (fun a => ?_) ?_ hOc
    · rw [Category.assoc, hsqa.w, ← Category.assoc, hsq3.w, Category.assoc]
    · rw [hn1, ← Category.assoc, hψ₂ a, Category.assoc, hψ₁ a, Category.assoc]
    · rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, RingHom.id_comp]
  have hinj₁ : Function.Injective ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁)) := by
    rw [RingHom.coe_comp]
    exact (algebraMap k₁ ℂ).injective.comp (IsFractionRing.injective (𝓞 k₁) k₁)
  exact ⟨k₁, inferInstance, hk, _, C₁, φ₁, T₁, m₁, D, ε, h, hC₁, hpq, hK, hpos,
    GlobalTheory.T.nonempty_tensor_of_onto_full_family hL E H (𝓞 k₁) _ _ C₁ D ε h T₁ ψ₁ hinj₁ hK hpos hF₁ hOnto⟩

end GlobalTheory.CM.Recog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorDecompositionPureTypeCmTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_decomposition_pure_type_cm_triple : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [NumberField k] (ω : 𝓞 k) (C : Ell H (𝓞 k) ω) (T : PAT H (Sp (𝓞 k))) (r : ℕ), C.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) → HasType H T.t.act (2 * ω - 1) r 0 →
  ∃ (k₁ : IntermediateField ℚ ℂ) (_ : NumberField k₁) (hk : k ≤ k₁) (ω₁ : 𝓞 k₁) (C₁ : Ell H (𝓞 k₁) ω₁) (φ : C₁.P.A.left ⟶ C.P.A.left) (T₁ : PAT H (Sp (𝓞 k₁))) (_ : SABMap T₁.t T.t (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom))) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), EllMap C₁ C (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) φ ∧ D.p + D.q = r ∧ IsKForm D ε h ∧ (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ Nonempty (IsTen C₁ D h T₁) := by
  first | exact @GlobalTheory.CM.Recog.exists_isTen_of_hasType | exact GlobalTheory.CM.Recog.exists_isTen_of_hasType | (intros; apply GlobalTheory.CM.Recog.exists_isTen_of_hasType <;> assumption)
end
end
