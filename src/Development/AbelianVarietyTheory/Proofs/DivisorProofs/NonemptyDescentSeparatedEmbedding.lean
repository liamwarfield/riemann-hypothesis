module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBasepointFreeSectionsLeOneFubiniStudy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsChartEqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapIntegralSchemeToGradedProjModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionToGradedModelFlatBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemCodimOneRegularChartStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsEqSpanRegularLattic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsEqSpanRegularLattic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.DescSpan

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (g : S →+* T) (h : R →+* S) :
    spMap (g.comp h) = spMap g ≫ spMap h := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem gp_comp {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (Desc.cst p) := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, gp, Scheme.fromSpecStalk_appTop]
  rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of X.functionField)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.ΓSpecIso_naturality]
  ext r
  simp [Desc.cst, Cartier.fnOf]

theorem cst_comp_spMap {X : Scheme.{0}} [IsIntegral X] {R S : Type} [CommRing R] [CommRing S] (p : X ⟶ Sp S)
    (g : R →+* S) : Desc.cst (p ≫ spMap g) = (Desc.cst p).comp g := by
  have h : spMap (Desc.cst (p ≫ spMap g)) = spMap ((Desc.cst p).comp g) := by
    rw [spMap_comp', ← gp_comp, ← gp_comp, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem regAt_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (q : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (Desc.cst q r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

theorem theta_c₀ (σ : Setup) (x : Sp σ.R) (r : σ.R) :
    σ.θ x (σ.c₀ r) = Desc.cst (σ.C x).G.hom (σ.ρ x r) := by
  obtain ⟨l, h1, h2⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    rw [spMap_comp', spMap_comp', Setup.c₀, ← gp_comp, ← gp_comp, ← Category.assoc, ← h2, Category.assoc,
      (σ.cart x).w, ← Category.assoc, ← Category.assoc, h1, Category.assoc]
  exact congrArg (fun q : σ.R →+* _ => q r) (congrArg CommRingCat.Hom.hom (Spec.map_injective e))

theorem mem_W_mul (σ : Setup) (x : Sp σ.R) {u : σ.A.left.functionField} (hu : u ∈ σ.W x) (r : σ.R) :
    σ.c₀ r * u ∈ σ.W x := fun z hz => by
  rw [map_mul, theta_c₀]
  exact (regAt_cst _ _ _).mul (hu z hz)

section Sec

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {k : ℕ}

theorem sec_zero : (0 : X.functionField) ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [zero_mul]; exact regAt_zero x)

theorem sec_add {u v : X.functionField} (hu : u ∈ Sec D k) (hv : v ∈ Sec D k) : u + v ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [add_mul]; exact (hg.regularAt_iff.1 (hu x)).add (hg.regularAt_iff.1 (hv x)))

theorem sec_mul {u c : X.functionField} (hu : u ∈ Sec D k) (hc : ∀ x, RegAt x c) : c * u ∈ Sec D k := fun x => by
  obtain ⟨g, hg⟩ := (k • D).exists_isEqn x
  exact hg.regularAt_iff.2 (by rw [_root_.mul_assoc]; exact (hc x).mul (hg.regularAt_iff.1 (hu x)))

end Sec

theorem finite_vert (σ : Setup) :
    {p : Sp σ.R | p.asIdeal.height = 1 ∧ σ.f ∈ p.asIdeal}.Finite := by
  have hfin := (Ideal.span {σ.f}).finite_minimalPrimes_of_isNoetherianRing
  refine (hfin.preimage fun a _ b _ h => PrimeSpectrum.ext h).subset fun p hp => ?_
  obtain ⟨h1, hf⟩ := hp
  have : p.asIdeal.FiniteHeight := (Ideal.finiteHeight_iff _).2 (Or.inr (by rw [h1]; exact ENat.one_ne_top))
  refine Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 hf) ?_
  rw [h1]
  exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero σ.hf)

end GlobalTheory.DescSpan


open GlobalTheory.DescSpan in
theorem GlobalTheory.Desc.sec_eq_spanBy_N : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  intro σ k
  have hc₀ : σ.c₀ = (Desc.cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := cst_comp_spMap _ _
  ext u
  constructor
  · intro hu
    choose m hm using fun p : Sp σ.R => GlobalTheory.T.exists_pow_mul_mem_codimOne_regular_chart' σ p u
    let M := ∑ p ∈ (finite_vert σ).toFinset, m p
    let v := σ.c₀ (σ.f ^ M) * u
    have hv : v ∈ σ.N k := by
      refine ⟨sec_mul hu fun x => by rw [hc₀]; exact regAt_cst _ _ _, (GlobalTheory.T.forall_mem_regularChart_iff_heightOne_primes σ v).2 fun p h1 hf => ?_⟩
      have hle : m p ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        ((finite_vert σ).mem_toFinset.2 ⟨h1, hf⟩)
      have e : v = σ.c₀ (σ.f ^ (M - m p)) * (σ.c₀ σ.f ^ m p * u) := by
        simp only [v, map_pow]
        rw [← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      rw [e]
      exact mem_W_mul σ p (hm p) _
    refine ⟨1, fun _ => IsLocalization.Away.invSelf σ.f ^ M, fun _ => v, fun _ => hv, ?_⟩
    rw [Fin.sum_univ_one]
    simp only [v, hc₀, RingHom.comp_apply, map_pow]
    rw [← _root_.mul_assoc, ← mul_pow, ← map_mul, mul_comm (IsLocalization.Away.invSelf σ.f),
      IsLocalization.Away.mul_invSelf, map_one, one_pow, _root_.one_mul]
  · rintro ⟨n, r, t, ht, rfl⟩
    exact Finset.sum_induction _ (· ∈ Sec σ.D k) (fun _ _ => sec_add) sec_zero
      fun i _ => sec_mul (ht i).1 fun x => regAt_cst _ _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsEqSpanRegularLatticStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierMultipleGlobalSections_eq_span_regularLattice : ∀ (σ : Setup) (k : ℕ), Sec σ.D k = spanBy (GlobalTheory.Desc.cst σ.A.hom) (σ.N k) := by
  first | exact @GlobalTheory.Desc.sec_eq_spanBy_N | exact GlobalTheory.Desc.sec_eq_spanBy_N | (intros; apply GlobalTheory.Desc.sec_eq_spanBy_N <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSeparatedProjModelGradedFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAlgebraMap
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial HomogeneousLocalization
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Desc.GrSpec

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F}

def ring (hN : GradedFam c₀ N) : Subring F[X] where
  carrier := {p | ∀ k, p.coeff k ∈ N k}
  mul_mem' {p q} hp hq k := by
    rw [coeff_mul]
    refine Finset.sum_induction _ (· ∈ N k) (fun a b ha hb => hN.add k a ha b hb) (hN.zero k) ?_
    rintro ⟨i, j⟩ hij
    have hij' : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hij
    subst hij'
    exact hN.mul i j _ (hp i) _ (hq j)
  one_mem' k := by
    rw [coeff_one]
    split_ifs with h
    · subst h; exact hN.one
    · exact hN.zero k
  add_mem' {p q} hp hq k := by rw [coeff_add]; exact hN.add k _ (hp k) _ (hq k)
  zero_mem' k := by rw [coeff_zero]; exact hN.zero k
  neg_mem' {p} hp k := by
    rw [coeff_neg]
    have := hN.smul k (-1) _ (hp k)
    simpa using this

theorem monomial_mem (hN : GradedFam c₀ N) {k : ℕ} {b : F} (hb : b ∈ N k) : monomial k b ∈ ring hN := by
  intro j
  rw [coeff_monomial_apply]
  split_ifs with h
  · subst h; exact hb
  · exact hN.zero j

def piece (hN : GradedFam c₀ N) (k : ℕ) : AddSubgroup (ring hN) where
  carrier := {p | ∀ j, j ≠ k → (p : F[X]).coeff j = 0}
  add_mem' {p q} hp hq j hj := by
    rw [Subring.coe_add, coeff_add, hp j hj, hq j hj, add_zero]
  zero_mem' j _ := by rw [Subring.coe_zero, coeff_zero]
  neg_mem' {p} hp j hj := by rw [Subring.coe_neg, coeff_neg, hp j hj, neg_zero]

theorem mem_piece_iff (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} :
    p ∈ piece hN k ↔ (p : F[X]) = monomial k ((p : F[X]).coeff k) := by
  constructor
  · intro hp
    ext j
    rw [coeff_monomial_apply]
    split_ifs with h
    · rw [h]
    · exact hp j (Ne.symm h)
  · intro hp j hj
    rw [hp, coeff_monomial_of_ne _ hj]

def hel (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) : ring hN := ⟨monomial k b, monomial_mem hN hb⟩

@[simp] theorem coe_hel (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) :
    (hel hN k b hb : F[X]) = monomial k b := rfl

theorem hel_mem (hN : GradedFam c₀ N) (k : ℕ) (b : F) (hb : b ∈ N k) : hel hN k b hb ∈ piece hN k := by
  rw [mem_piece_iff, coe_hel, coeff_monomial_same]

theorem hel_ne_zero (hN : GradedFam c₀ N) {k : ℕ} {b : F} (hb : b ∈ N k) (h : b ≠ 0) : hel hN k b hb ≠ 0 := by
  intro e
  have := congrArg (fun p : ring hN => (p : F[X]).coeff k) e
  simp at this
  exact h this

def comp (hN : GradedFam c₀ N) (k : ℕ) : ring hN →+ piece hN k where
  toFun p := ⟨⟨monomial k ((p : F[X]).coeff k), monomial_mem hN (p.2 k)⟩, by
    intro j hj; exact coeff_monomial_of_ne _ hj⟩
  map_zero' := by ext; simp
  map_add' p q := by ext; simp

theorem comp_eq_zero (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} (h : (p : F[X]).coeff k = 0) : comp hN k p = 0 := by
  ext; simp [comp, h]

theorem comp_of_mem (hN : GradedFam c₀ N) {k : ℕ} {p : ring hN} (h : p ∈ piece hN k) : (comp hN k p : ring hN) = p := by
  ext1; exact ((mem_piece_iff hN).1 h).symm

def dec (hN : GradedFam c₀ N) (p : ring hN) : DirectSum ℕ (fun k => piece hN k) :=
  ∑ k ∈ (p : F[X]).support, DirectSum.of (fun k => piece hN k) k (comp hN k p)

theorem dec_eq (hN : GradedFam c₀ N) (p : ring hN) (S : Finset ℕ) (hS : (p : F[X]).support ⊆ S) :
    dec hN p = ∑ k ∈ S, DirectSum.of (fun k => piece hN k) k (comp hN k p) := by
  refine Finset.sum_subset hS fun k _ hk => ?_
  rw [comp_eq_zero hN (notMem_support_iff.1 hk), map_zero]

def decHom (hN : GradedFam c₀ N) : ring hN →+ DirectSum ℕ (fun k => piece hN k) where
  toFun := dec hN
  map_zero' := by simp [dec]
  map_add' p q := by
    classical
    set S := (p : F[X]).support ∪ (q : F[X]).support ∪ ((p + q : ring hN) : F[X]).support
    rw [dec_eq hN _ S (fun x hx => Finset.mem_union_right _ hx),
      dec_eq hN p S (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)),
      dec_eq hN q S (fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add (f := _), map_add (f := _)]

instance gradedMonoid (hN : GradedFam c₀ N) : SetLike.GradedMonoid (piece hN) where
  one_mem j hj := by
    change (1 : F[X]).coeff j = 0
    rw [coeff_one, if_neg hj]
  mul_mem i j a b ha hb := by
    rw [mem_piece_iff] at ha hb
    intro l hl
    rw [Subring.coe_mul, ha, hb, monomial_mul_monomial, coeff_monomial_of_ne _ hl]

instance gradedRing (hN : GradedFam c₀ N) : GradedRing (piece hN) :=
  { gradedMonoid hN with
    toDecomposition := DirectSum.Decomposition.ofAddHom (piece hN) (decHom hN)
      (by
        refine AddMonoidHom.ext fun p => Subtype.ext ?_
        change (((DirectSum.coeAddMonoidHom (piece hN)) (dec hN p) : ring hN) : F[X]) = p
        set_option synthInstance.maxHeartbeats 100000 in
          rw [dec, map_sum]
        simp only [DirectSum.coeAddMonoidHom_of]
        rw [AddSubmonoidClass.coe_finsetSum]
        exact (as_sum_support _).symm)
      (by
        refine DirectSum.addHom_ext fun k y => ?_
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
        change dec hN (y : ring hN) = DirectSum.of _ k y
        rw [dec_eq hN _ {k} (fun j hj => by
          by_contra h'
          exact (mem_support_iff.1 hj) (y.2 j (by simpa using h')))]
        rw [Finset.sum_singleton]
        congr 1
        exact Subtype.ext (comp_of_mem hN y.2)) }

section Frac


variable (F) in
def cL : F →+* FractionRing F[X] := (algebraMap F[X] (FractionRing F[X])).comp C

theorem cL_injective : Function.Injective (cL F) :=
  (IsFractionRing.injective F[X] (FractionRing F[X])).comp C_injective

def toL (hN : GradedFam c₀ N) : ring hN →+* FractionRing F[X] :=
  (algebraMap F[X] (FractionRing F[X])).comp (ring hN).subtype

theorem toL_injective (hN : GradedFam c₀ N) : Function.Injective (toL hN) :=
  (IsFractionRing.injective F[X] (FractionRing F[X])).comp Subtype.val_injective

variable (hN : GradedFam c₀ N) (P : Ideal (ring hN)) [P.IsPrime]

def liftAt : Localization.AtPrime P →+* FractionRing F[X] :=
  IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) (g := toL hN) fun s =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (toL_injective hN)).2 fun h => s.2 (h ▸ P.zero_mem))

def valL : AtPrime (piece hN) P →+* FractionRing F[X] :=
  (liftAt hN P).comp (algebraMap (AtPrime (piece hN) P) (Localization.AtPrime P))

theorem valL_mk (g : NumDenSameDeg (piece hN) P.primeCompl) :
    valL hN P (mk g) = cL F (((g.num : ring hN) : F[X]).coeff g.deg / ((g.den : ring hN) : F[X]).coeff g.deg) := by
  have hnum := (mem_piece_iff hN).1 g.num.2
  have hden := (mem_piece_iff hN).1 g.den.2
  have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
    intro h0
    apply g.den_mem
    have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
    rw [this]; exact P.zero_mem
  change liftAt hN P (mk g).val = _
  rw [val_mk, Localization.mk_eq_mk', liftAt, IsLocalization.lift_mk'_spec]
  change algebraMap F[X] _ ((g.num : ring hN) : F[X]) =
    algebraMap F[X] _ ((g.den : ring hN) : F[X]) * algebraMap F[X] _ (C _)
  rw [← map_mul]
  congr 1
  rw [hnum, hden, coeff_monomial_same, coeff_monomial_same, monomial_mul_C, mul_div_cancel₀ _ hs]


variable (F) in
def eqR : F ≃+* (cL F).range :=
  RingEquiv.ofBijective (cL F).rangeRestrict
    ⟨fun a b h => cL_injective (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩

def valR : AtPrime (piece hN) P →+* (cL F).range :=
  (valL hN P).codRestrict (cL F).range fun y => by
    obtain ⟨g, rfl⟩ := mk_surjective y
    exact ⟨_, (valL_mk hN P g).symm⟩

def psiAt : AtPrime (piece hN) P →+* F := (eqR F).symm.toRingHom.comp (valR hN P)

theorem cL_psiAt (y : AtPrime (piece hN) P) : cL F (psiAt hN P y) = valL hN P y :=
  congrArg Subtype.val ((eqR F).apply_symm_apply (valR hN P y))

theorem psiAt_mk (g : NumDenSameDeg (piece hN) P.primeCompl) :
    psiAt hN P (mk g) = ((g.num : ring hN) : F[X]).coeff g.deg / ((g.den : ring hN) : F[X]).coeff g.deg :=
  cL_injective (by rw [cL_psiAt, valL_mk])

end Frac

section Scheme

variable (hN : GradedFam c₀ N)

instance isPrime_point (x : Proj (piece hN)) : x.asHomogeneousIdeal.toIdeal.IsPrime :=
  ProjectiveSpectrum.isPrime x

def gen {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) : Proj (piece hN) :=
  ⟨⊥, Ideal.isPrime_bot, fun h => hel_ne_zero hN hb h0 (by
    have : hel hN k b hb ∈ HomogeneousIdeal.irrelevant (piece hN) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (piece hN) (hel_mem hN k b hb) (by omega)]
    exact h this)⟩

theorem isIntegral {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) : IsIntegral (Proj (piece hN)) := by
  have hred : IsReduced (Proj (piece hN)) := by
    have (x : Proj (piece hN)) : _root_.IsReduced ((Proj (piece hN)).presheaf.stalk x) := by
      let x' : ProjectiveSpectrum (piece hN) := x
      have h1 : _root_.IsReduced (HomogeneousLocalization.AtPrime (piece hN) x'.asHomogeneousIdeal.toIdeal) :=
        isReduced_of_injective (algebraMap _ (Localization.AtPrime x'.asHomogeneousIdeal.toIdeal))
          (HomogeneousLocalization.val_injective _)
      exact isReduced_of_injective (Proj.stalkIso' (piece hN) x') (Proj.stalkIso' (piece hN) x').injective
    exact isReduced_of_isReduced_stalk _
  have hcl : closure ({gen hN hk hb h0} : Set (ProjectiveSpectrum (piece hN))) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    exact (ProjectiveSpectrum.le_iff_mem_closure (piece hN) (gen hN hk hb h0) y).1 (by
      show (⊥ : HomogeneousIdeal (piece hN)) ≤ y.asHomogeneousIdeal
      exact bot_le)
  have hirr : IrreducibleSpace (ProjectiveSpectrum (piece hN)) := by
    refine (irreducibleSpace_def _).2 ?_
    rw [Set.top_eq_univ, ← hcl]
    exact (isIrreducible_singleton (x := gen hN hk hb h0)).closure
  have : IrreducibleSpace (Proj (piece hN)) := hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def toZero : R →+* piece hN 0 where
  toFun r := ⟨⟨C (c₀ r), by
      have : c₀ r * 1 ∈ N 0 := hN.smul 0 r 1 hN.one
      rw [mul_one] at this
      exact monomial_mem hN (k := 0) this⟩, by
    intro j hj; simp [coeff_C, hj]⟩
  map_one' := by ext1; ext1; simp
  map_mul' a b := by ext1; ext1; simp
  map_zero' := by ext1; ext1; simp
  map_add' a b := by ext1; ext1; simp

def Dp (k : ℕ) (b : F) : (Proj (piece hN)).Opens := by
  classical exact if hb : b ∈ N k then Proj.basicOpen (piece hN) (hel hN k b hb) else ⊥

theorem Dp_of_mem {k : ℕ} {b : F} (hb : b ∈ N k) : Dp hN k b = Proj.basicOpen (piece hN) (hel hN k b hb) := by
  rw [Dp, dite_eq_left hb]

def psi [IsIntegral (Proj (piece hN))] : (Proj (piece hN)).functionField →+* F :=
  (psiAt hN _).comp (Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN)))).toRingHom

theorem psi_algebraMap [IsIntegral (Proj (piece hN))] (x : Proj (piece hN)) (w : (Proj (piece hN)).presheaf.stalk x) :
    psi hN (algebraMap _ _ w) = psiAt hN _ (Proj.stalkIso' (piece hN) x w) := by
  obtain ⟨g, hg⟩ := mk_surjective (Proj.stalkIso' (piece hN) x w)
  have hw : w = (Proj.stalkIso' (piece hN) x).symm (mk g) :=
    ((Proj.stalkIso' (piece hN) x).symm_apply_apply w).symm.trans (congrArg _ hg.symm)
  subst hw
  have hsp : genericPoint (Proj (piece hN)) ⤳ x := genericPoint_specializes x
  have hle : (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal :=
    (ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ _).2 (specializes_iff_mem_closure.1 hsp)
  have key : Proj.stalkIso' (piece hN) (genericPoint (Proj (piece hN)))
      ((Proj (piece hN)).presheaf.stalkSpecializes hsp ((Proj.stalkIso' (piece hN) x).symm (mk g))) =
      mk (⟨g.deg, g.num, g.den, fun hy => g.den_mem (hle hy)⟩ :
        NumDenSameDeg (piece hN) (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl) := by
    erw [Proj.stalkIso'_symm_mk, TopCat.Presheaf.germ_stalkSpecializes_apply, Proj.stalkIso'_germ]
    rfl
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.stalkSpecializes hsp _)) = _
  rw [key, RingEquiv.apply_symm_apply, psiAt_mk, psiAt_mk]

end Scheme

end GlobalTheory.Desc.GrSpec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSeparatedProjModelGradedFunctions
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GrSpec

open Polynomial HomogeneousLocalization

variable {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)

theorem coe_hel_pow {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) :
    ((hel hN k b hb ^ n : ring hN) : F[X]) = monomial (k * n) (b ^ n) := by
  rw [SubmonoidClass.coe_pow, coe_hel, monomial_pow]

theorem hel_pow_mem {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : hel hN k b hb ^ n ∈ piece hN (k * n) := by
  have := SetLike.pow_mem_graded n (hel_mem hN k b hb)
  rwa [smul_eq_mul, mul_comm] at this

theorem isUnit_mk_iff (P : Ideal (ring hN)) [P.IsPrime] (g : NumDenSameDeg (piece hN) P.primeCompl) :
    IsUnit (mk g : AtPrime (piece hN) P) ↔ (g.num : ring hN) ∉ P := by
  rw [← isUnit_iff_isUnit_val, val_mk, Localization.mk_eq_mk', IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem affine {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) : IsAffineOpen (Dp hN k b) := by
  rw [Dp_of_mem hN hb]
  exact Proj.isAffineOpen_basicOpen _ _ (hel_mem hN k b hb) (by omega)

theorem cover (z : Proj (piece hN)) : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, z ∈ Dp hN k b := by
  classical
  obtain ⟨y, hy, hyz⟩ := Set.not_subset.1 z.not_irrelevant_le
  have : ∃ j, (DirectSum.decompose (piece hN) y j : ring hN) ∉ z.asHomogeneousIdeal := by
    by_contra hc
    push_neg at hc
    apply hyz
    rw [← DirectSum.sum_support_decompose (piece hN) y]
    exact Ideal.sum_mem _ fun j _ => hc j
  obtain ⟨j, hj⟩ := this
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hj
    have : (DirectSum.decompose (piece hN) y 0 : ring hN) = 0 := by
      rw [← GradedRing.proj_apply]; exact (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hy
    rw [this]; exact zero_mem _
  set c := DirectSum.decompose (piece hN) y j
  have hb : ((c : ring hN) : F[X]).coeff j ∈ N j := (c : ring hN).2 j
  refine ⟨j, by omega, _, hb, ?_⟩
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen]
  have : hel hN j _ hb = (c : ring hN) := Subtype.ext ((mem_piece_iff hN).1 c.2).symm
  rw [this]; exact hj

theorem ideal_gen [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (h0 : b ≠ 0) :
    (genericPoint (Proj (piece hN))).asHomogeneousIdeal = ⊥ :=
  le_bot_iff.1 ((ProjectiveSpectrum.le_iff_mem_closure (piece hN) _ (gen hN hk hb h0)).2
    (specializes_iff_mem_closure.1 (genericPoint_specializes (show Proj (piece hN) from gen hN hk hb h0))))

theorem genMem [IsIntegral (Proj (piece hN))] (h : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) {k : ℕ} {b : F} (hb : b ∈ N k) :
    genericPoint (Proj (piece hN)) ∈ Dp hN k b ↔ b ≠ 0 := by
  obtain ⟨k', hk', b', hb', h0'⟩ := h
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen, ideal_gen hN hk' hb' h0']
  change ¬ (hel hN k b hb = 0) ↔ _
  rw [not_iff_not, Subtype.ext_iff]
  simp

theorem hel_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k} (n : ℕ)
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : hel hN k b hb ^ n ∉ z.asHomogeneousIdeal.toIdeal :=
  fun h => hz (Ideal.IsPrime.mem_of_pow_mem inferInstance n h)

theorem ne_zero_of_notMem {z : Proj (piece hN)} {k : ℕ} {b : F} {hb : b ∈ N k}
    (hz : hel hN k b hb ∉ z.asHomogeneousIdeal) : b ≠ 0 := by
  rintro rfl
  apply hz
  have : hel hN k 0 hb = 0 := Subtype.ext (by simp)
  rw [this]; exact zero_mem _

theorem mem [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (z : Proj (piece hN))
    (hz : z ∈ Dp hN k b) {l : ℕ} {a : F} (ha : a ∈ N l) :
    z ∈ Dp hN l a ↔ ∃ v, UnitAt z v ∧ psi hN v = a ^ k / b ^ l := by
  rw [Dp_of_mem hN hb, Proj.mem_basicOpen] at hz
  rw [Dp_of_mem hN ha, Proj.mem_basicOpen]
  have hfz := hel_notMem hN l hz
  have hb0 := ne_zero_of_notMem hN hz
  constructor
  · intro hg
    let nd : NumDenSameDeg (piece hN) z.asHomogeneousIdeal.toIdeal.primeCompl :=
      ⟨l * k, ⟨_, hel_pow_mem hN ha k⟩, ⟨_, by rw [mul_comm]; exact hel_pow_mem hN hb l⟩, hfz⟩
    refine ⟨algebraMap ((Proj (piece hN)).presheaf.stalk z) _ ((Proj.stalkIso' (piece hN) z).symm (mk nd)), ⟨_, ?_, rfl⟩, ?_⟩
    · exact ((isUnit_mk_iff hN _ nd).2 (hel_notMem hN k hg)).map (Proj.stalkIso' (piece hN) z).symm
    · refine (psi_algebraMap hN z _).trans ?_
      erw [RingEquiv.apply_symm_apply]
      rw [psiAt_mk]
      simp only [nd, coe_hel_pow, coeff_monomial, Finsupp.single_apply, mul_comm k l, ↓reduceIte]
  · rintro ⟨v, ⟨w, hwu, rfl⟩, hv⟩ hg
    rw [psi_algebraMap] at hv
    obtain ⟨g, hg'⟩ := mk_surjective (Proj.stalkIso' (piece hN) z w)
    rw [← hg', psiAt_mk] at hv
    have hu : IsUnit (mk g : AtPrime (piece hN) z.asHomogeneousIdeal.toIdeal) := by
      rw [hg']; exact hwu.map (Proj.stalkIso' (piece hN) z)
    rw [isUnit_mk_iff] at hu
    have hnum := (mem_piece_iff hN).1 g.num.2
    have hden := (mem_piece_iff hN).1 g.den.2
    have hs : ((g.den : ring hN) : F[X]).coeff g.deg ≠ 0 := by
      intro h0
      apply g.den_mem
      have : (g.den : ring hN) = 0 := Subtype.ext (by rw [hden, h0, map_zero]; rfl)
      rw [this]; exact zero_mem _
    have key : (g.num : ring hN) * hel hN k b hb ^ l = hel hN l a ha ^ k * (g.den : ring hN) := by
      apply Subtype.ext
      rw [Subring.coe_mul, Subring.coe_mul, coe_hel_pow, coe_hel_pow, hnum, hden, monomial_mul_monomial,
        monomial_mul_monomial, show l * k + g.deg = g.deg + k * l by ring]
      congr 1
      rw [div_eq_div_iff hs (pow_ne_zero _ hb0)] at hv
      exact hv
    have : (g.num : ring hN) * hel hN k b hb ^ l ∈ z.asHomogeneousIdeal.toIdeal := by
      rw [key]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hg _ (by omega))
    rcases Ideal.IsPrime.mem_or_mem inferInstance this with h | h
    · exact hu h
    · exact hfz h

def fracAt {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F} (ha : a ∈ N (k * m)) (x : Proj (piece hN))
    (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) : NumDenSameDeg (piece hN) x.asHomogeneousIdeal.toIdeal.primeCompl :=
  ⟨k * m, ⟨hel hN (k * m) a ha, hel_mem hN _ _ ha⟩, ⟨_, hel_pow_mem hN hb m⟩, hel_notMem hN m hx⟩

theorem psi_fracAt [IsIntegral (Proj (piece hN))] {k : ℕ} {b : F} (hb : b ∈ N k) (m : ℕ) {a : F}
    (ha : a ∈ N (k * m)) (x : Proj (piece hN)) (hx : hel hN k b hb ∉ x.asHomogeneousIdeal) :
    psi hN (algebraMap ((Proj (piece hN)).presheaf.stalk x) _
      ((Proj.stalkIso' (piece hN) x).symm (mk (fracAt hN hb m ha x hx)))) = a / b ^ m := by
  refine (psi_algebraMap hN x _).trans ?_
  erw [RingEquiv.apply_symm_apply]
  rw [psiAt_mk]
  simp only [fracAt, coe_hel, coe_hel_pow, coeff_monomial, Finsupp.single_eq_same]

theorem ringChar [IsIntegral (Proj (piece hN))] {k : ℕ} (hk : 1 ≤ k) {b : F} (hb : b ∈ N k) (hb0 : b ≠ 0) (u : F) :
    (∃ v, (∀ z ∈ Dp hN k b, RegAt z v) ∧ psi hN v = u) ↔ ∃ m, ∃ a ∈ N (k * m), u = a / b ^ m := by
  have h1 : ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0 := ⟨k, hk, b, hb, hb0⟩
  have hgen : genericPoint (Proj (piece hN)) ∈ Dp hN k b := (genMem hN h1 hb).2 hb0
  rw [Dp_of_mem hN hb] at hgen ⊢
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨s, rfl⟩ := exists_fnOf_eq hgen hv
    obtain ⟨y, rfl⟩ : ∃ y, Proj.awayToSection (piece hN) (hel hN k b hb) y = s := by
      refine ⟨(Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv s, ?_⟩
      rw [← Proj.basicOpenIsoAway_hom (piece hN) _ (hel_mem hN k b hb) (by omega)]
      exact (Proj.basicOpenIsoAway (piece hN) _ (hel_mem hN k b hb) (by omega)).inv_hom_id_apply s
    obtain ⟨nd, rfl⟩ := mk_surjective y
    obtain ⟨m, hm⟩ := nd.den_mem
    have hdeg : nd.deg = k * m := by
      have hne : (nd.den : ring hN) ≠ 0 := by
        rw [← hm]; exact pow_ne_zero _ (hel_ne_zero hN hb hb0)
      exact DirectSum.degree_eq_of_mem_mem (piece hN) nd.den.2 (hm ▸ hel_pow_mem hN hb m) hne
    refine ⟨m, ((nd.num : ring hN) : F[X]).coeff nd.deg, hdeg ▸ (nd.num : ring hN).2 nd.deg, ?_⟩
    change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hgen
      (Proj.awayToSection (piece hN) (hel hN k b hb) (mk nd)))) = _
    erw [Proj.stalkIso'_germ]
    have key : ∀ (h : Submonoid.powers (hel hN k b hb) ≤
        (genericPoint (Proj (piece hN))).asHomogeneousIdeal.toIdeal.primeCompl),
        psiAt hN _ (HomogeneousLocalization.mapId (piece hN) h (mk nd)) =
          ((nd.num : ring hN) : F[X]).coeff nd.deg / ((nd.den : ring hN) : F[X]).coeff nd.deg := by
      intro h
      exact psiAt_mk hN _ ⟨nd.deg, nd.num, nd.den, h nd.den_mem⟩
    refine (key _).trans ?_
    rw [← hm, coe_hel_pow, coeff_monomial]
    have he : (Finsupp.single (k * m) (b ^ m)) nd.deg = b ^ m := by
      rw [hdeg, Finsupp.single_eq_same]
    rw [he]
  · rintro ⟨m, a, ha, rfl⟩
    refine ⟨_, fun z hz => ⟨_, (psi hN).injective ((psi_fracAt hN hb m ha z hz).trans
      (psi_fracAt hN hb m ha _ hgen).symm)⟩, psi_fracAt hN hb m ha _ hgen⟩

def gR : CommRingCat.of R ⟶ Γ(Proj (piece hN), ⊤) :=
  CommRingCat.ofHom ((fromZeroRingHom (piece hN) _).comp (toZero hN)) ≫ Proj.awayToSection (piece hN) 1 ≫
    (Proj (piece hN)).presheaf.map (homOfLE (Proj.basicOpen_one (piece hN)).ge).op

def pstr : Proj (piece hN) ⟶ Sp R := (Proj (piece hN)).toSpecΓ ≫ Spec.map (gR hN)

theorem sep : IsSeparated (pstr hN) := inferInstance

theorem const [IsIntegral (Proj (piece hN))] : (psi hN).comp (cst (pstr hN)) = c₀ := by
  ext r
  have hg : genericPoint (Proj (piece hN)) ∈ Proj.basicOpen (piece hN) 1 := by
    rw [Proj.basicOpen_one]; trivial
  have e0 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop = gR hN := by
    rw [pstr, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]
  change psi hN (fnOf ⊤ trivial (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (pstr hN).appTop) r)) = c₀ r
  rw [e0]
  change psi hN (fnOf ⊤ trivial (resG (Proj (piece hN)) (Proj.basicOpen_one (piece hN)).ge
    (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = c₀ r
  rw [fnOf_resG (Proj.basicOpen_one (piece hN)).ge trivial]
  change psiAt hN _ (Proj.stalkIso' (piece hN) _ ((Proj (piece hN)).presheaf.germ _ _ hg
      (Proj.awayToSection (piece hN) 1 (fromZeroRingHom (piece hN) _ (toZero hN r))))) = _
  erw [Proj.stalkIso'_germ]
  refine (psiAt_mk hN _ ⟨0, toZero hN r, 1, fun h => ?_⟩).trans ?_
  · exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h)
  · simp [toZero]

end GlobalTheory.Desc.GrSpec

namespace GlobalTheory.Desc

theorem exists_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F),
    GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R)
      (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  intro R F _ _ _ c₀ N hN h
  obtain ⟨k₀, hk₀, b₀, hb₀, h₀⟩ := h
  haveI := GrSpec.isIntegral hN hk₀ hb₀ h₀
  refine ⟨Proj (GrSpec.piece hN), inferInstance, GrSpec.pstr hN, GrSpec.psi hN, GrSpec.Dp hN, ?_⟩
  exact
    { sep := GrSpec.sep hN
      const := GrSpec.const hN
      affine := fun k hk b hb => GrSpec.affine hN hk hb
      cover := GrSpec.cover hN
      gen := fun k _ b hb => GrSpec.genMem hN ⟨k₀, hk₀, b₀, hb₀, h₀⟩ hb
      ring := fun k hk b hb hb0 u => GrSpec.ringChar hN hk hb hb0 u
      mem := fun k hk b hb z hz l _ a ha => GrSpec.mem hN hk hb z hz ha }

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralSeparatedProjModelGradedFunctionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_separated_projModel_gradedFunctions : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → (∃ k, 1 ≤ k ∧ ∃ b ∈ N k, b ≠ 0) → ∃ (P : Scheme.{0}) (_ : IsIntegral P) (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp := by
  first | exact @GlobalTheory.Desc.exists_model | exact GlobalTheory.Desc.exists_model | (intros; apply GlobalTheory.Desc.exists_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionLocusOfAmpleSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionLocusOfAmpleSpan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem unitAt_of_mul_right {X : Scheme.{0}} [IsIntegral X] {x : X} {a b : X.functionField}
    (ha : RegAt x a) (hb : RegAt x b) (h : UnitAt x (a * b)) : UnitAt x b := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  obtain ⟨w, hw, e⟩ := h
  rw [← map_mul] at e
  obtain rfl := IsFractionRing.injective (X.presheaf.stalk x) X.functionField e
  exact ⟨b', isUnit_of_mul_isUnit_right hw, rfl⟩

theorem regAt_cst {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (x : X) (r : R) :
    RegAt x (cst p r) :=
  regAt_fnOf (x := x) (U := ⊤) trivial trivial _

theorem exists_locus_of_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  intro R₁ F _ _ Y _ q θ N D₁ hA hS y
  obtain ⟨k, hk, u, hu, U, -, hU, hy⟩ := hA y
  have hyu : y ∈ locus D₁ k u := hU ▸ hy
  have hu' : u ∈ spanBy (cst q) (θ '' N k) := hS k ▸ hu
  obtain ⟨n, r, t, ht, rfl⟩ := hu'
  obtain ⟨g, hg⟩ := (k • D₁).exists_isEqn y
  have hunit : UnitAt y ((∑ i, cst q (r i) * t i) * g) := hg.generatesAt_iff.1 hyu
  have hsec : ∀ i, RegAt y (t i * g) := fun i => by
    have : t i ∈ Sec D₁ k := by rw [hS k]; exact subset_spanBy _ _ (ht i)
    exact hg.regularAt_iff.1 (this y)
  by_contra hne
  push_neg at hne
  apply (zeroAt_iff.1 ?_).2 hunit
  rw [Finset.sum_mul]
  refine Finset.sum_induction _ (ZeroAt y) (fun _ _ => ZeroAt.add) (zeroAt_zero y) fun i _ => ?_
  rw [_root_.mul_assoc]
  refine zeroAt_iff.2 ⟨(regAt_cst q y (r i)).mul (hsec i), fun hu => ?_⟩
  obtain ⟨b, hb, hbt⟩ := ht i
  apply hne k hk b hb
  show (k • D₁).GeneratesAt y (θ b)
  rw [hg.generatesAt_iff, hbt]
  exact unitAt_of_mul_right (regAt_cst q y (r i)) (hsec i) hu

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionLocusOfAmpleSpanStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierSectionLocus_of_ample_span : ∀ (R₁ F : Type) [CommRing R₁] [Field F] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (N : ℕ → Set F) (D₁ : CartierDiv Y), AmpleDiv D₁ → (∀ k, Sec D₁ k = spanBy (GlobalTheory.Desc.cst q) (θ '' N k)) → ∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b) := by
  first | exact @GlobalTheory.Desc.exists_locus_of_span | exact GlobalTheory.Desc.exists_locus_of_span | (intros; apply GlobalTheory.Desc.exists_locus_of_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDescentSeparatedEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.EmbeddingLemmas

theorem spMap_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    spMap (Desc.cst p) = gp X ≫ p := by
  have h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]; rfl

theorem cst_comp {X : Scheme.{0}} [IsIntegral X] {R R' : Type} [CommRing R] [CommRing R'] (q : X ⟶ Sp R') (ρ : R →+* R') :
    Desc.cst (q ≫ spMap ρ) = (Desc.cst q).comp ρ := by
  have e : spMap (Desc.cst (q ≫ spMap ρ)) = spMap ((Desc.cst q).comp ρ) := by
    rw [spMap_comp', spMap_cst, spMap_cst, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem cst_inj {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] [IsDomain R] (p : X ⟶ Sp R) [Flat p] :
    Function.Injective (Desc.cst p) := by
  have h1 : Flat (gp X) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X _
  have h2 : Flat (spMap (Desc.cst p)) := by rw [spMap_cst]; infer_instance
  have h3 : (Desc.cst p).Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h2
  algebraize [Desc.cst p]
  exact FaithfulSMul.algebraMap_injective R X.functionField

theorem baseIndexConstant_injective (σ : Setup) : Function.Injective σ.c₀ := by
  haveI := σ.ab.smooth
  exact cst_inj _

theorem abelianSchemeDescent_chart_baseConstants_comp (σ : Setup) (x : Sp σ.R) : (σ.θ x).comp σ.c₀ = (Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    rw [spMap_comp', spMap_comp', Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc,
      (σ.cart x).w]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem linDisj_A (σ : Setup) : LinDisj σ.c₀ (Desc.cst σ.A.hom) (RingHom.id _) := by
  haveI := σ.ab.proper
  have hfl : (algebraMap σ.R (Localization.Away σ.f)).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  refine (GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint σ.R _ _ hfl σ.A.left σ.A.left σ.A.left (σ.A.hom ≫ awayMap σ.f) σ.A.hom (𝟙 _) (𝟙 _)
    (RingHom.id _) inferInstance inferInstance ?_ ⟨gp _, by simp, ?_⟩ σ.D σ.D ?_).1
  · rw [Category.id_comp]
    exact IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  · have : spMap (RingHom.id σ.A.left.functionField) = 𝟙 _ := Spec.map_id _
    rw [this]; simp
  · intro v g h
    exact h

theorem linDisj_C (σ : Setup) (x : Sp σ.R) : LinDisj σ.c₀ (Desc.cst (σ.C x).G.hom) (σ.θ x) := by
  haveI := σ.ab.proper
  exact (GlobalTheory.T.cartierSections_flat_baseChange_linearlyDisjoint σ.R _ _ (σ.flat x) σ.A.left (σ.C x).G.left (σ.V x).toScheme (σ.A.hom ≫ awayMap σ.f) (σ.C x).G.hom
    (σ.V x).ι (σ.φ x) (σ.θ x) inferInstance inferInstance (σ.cart x) (σ.hθ x) σ.D (σ.D₁ x) (σ.pull x)).1

theorem compact_A (σ : Setup) : CompactSpace σ.A.left := by
  haveI := σ.ab.proper
  exact QuasiCompact.compactSpace_of_compactSpace σ.A.hom

theorem qsep_A (σ : Setup) : QuasiSeparatedSpace σ.A.left := by
  haveI := σ.ab.proper
  exact quasiSeparatedSpace_of_quasiSeparated σ.A.hom

theorem compact_C (σ : Setup) (x : Sp σ.R) : CompactSpace (σ.C x).G.left := by
  haveI := (σ.C x).semi.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom

theorem qsep_C (σ : Setup) (x : Sp σ.R) : QuasiSeparatedSpace (σ.C x).G.left := by
  haveI := (σ.C x).semi.separated
  exact quasiSeparatedSpace_of_quasiSeparated (σ.C x).G.hom

theorem cartA_of_openIn (σ : Setup) (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp σ.R) (hp : IsSeparated p)
    (i : σ.A.left ⟶ P) (h : OpenIn i σ.A.hom p (awayMap σ.f)) : IsPullback i σ.A.hom p (awayMap σ.f) := by
  obtain ⟨w, ho⟩ := h
  haveI := σ.ab.proper
  set g := pullback.lift i σ.A.hom w with hg
  have hsnd : g ≫ pullback.snd p (awayMap σ.f) = σ.A.hom := pullback.lift_snd _ _ _
  haveI : IsProper (g ≫ pullback.snd p (awayMap σ.f)) := by rw [hsnd]; infer_instance
  haveI : IsProper g := IsProper.of_comp g (pullback.snd p (awayMap σ.f))
  haveI : Nonempty (pullback p (awayMap σ.f) : Scheme.{0}) := ⟨g (genericPoint σ.A.left)⟩
  haveI : IsIntegral (pullback p (awayMap σ.f)) := isIntegral_of_isOpenImmersion (pullback.fst p (awayMap σ.f))
  have hclo : IsClopen (Set.range g) := ⟨g.isClosedMap.isClosed_range, g.isOpenEmbedding.isOpen_range⟩
  have hs : Surjective g := ⟨Set.range_eq_univ.1 (hclo.eq_univ (Set.range_nonempty _))⟩
  haveI : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).2 ⟨ho, hs⟩
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso g) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem onV_of (σ : Setup) (x : Sp σ.R) (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp σ.R) (hp : IsSeparated p)
    (ψ : P.functionField →+* σ.A.left.functionField) (i : σ.A.left ⟶ P) (hi : i ≫ p = σ.A.hom ≫ awayMap σ.f)
    (hfA : PFF (𝟙 _) i ψ) (e : (σ.C x).G.left ⟶ P) (he : e ≫ p = (σ.C x).G.hom ≫ spMap (σ.ρ x))
    (hf : PFF (𝟙 _) e ((σ.θ x).comp ψ)) : σ.φ x ≫ i = (σ.V x).ι ≫ e := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  obtain ⟨a, ha, ha'⟩ := hfA
  obtain ⟨b, hb, hb'⟩ := hf
  rw [Category.comp_id] at ha hb
  subst ha hb
  haveI : IsDominant (l ≫ (σ.V x).ι) := by
    rw [hl]
    refine ⟨?_⟩
    have hm : genericPoint (σ.C x).G.left ∈ Set.range (gp (σ.C x).G.left) :=
      ⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense {genericPoint (σ.C x).G.left} := by
      rw [dense_iff_closure_eq]; exact (genericPoint_spec _).def.trans rfl
    exact hd.mono (Set.singleton_subset_iff.2 hm)
  haveI : IsDominant l := IsDominant.of_comp_of_isOpenImmersion l (σ.V x).ι
  refine ext_of_isDominant_of_isSeparated p ?_ l ?_
  · rw [Category.assoc, Category.assoc, hi, he, (σ.cart x).w, Category.assoc]
  · rw [← Category.assoc, hl', ← Category.assoc, hl, hb', Category.assoc, ha', spMap_comp', Category.assoc]

end GlobalTheory.Desc.EmbeddingLemmas

namespace GlobalTheory.Desc


open GlobalTheory.Desc.EmbeddingLemmas in
theorem nonempty_emb : ∀ σ : Setup, σ.Common → Nonempty (Emb σ) := by
  intro σ _
  obtain ⟨hG, k₀, hk₀, b₀, hb₀, hb₀0⟩ := GlobalTheory.T.abelianSchemeDescent_gradedFamily_nonzero σ
  obtain ⟨P, hPi, p, ψ, Dp, hM⟩ := GlobalTheory.T.exists_integral_separated_projModel_gradedFunctions σ.R _ σ.c₀ σ.N hG ⟨k₀, hk₀, b₀, hb₀, hb₀0⟩
  have hinj := baseIndexConstant_injective σ

  haveI : IsDomain (Localization.Away σ.f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors σ.hf)
  have hcA : (RingHom.id _).comp σ.c₀ = (cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := by
    rw [RingHom.id_comp]; exact cst_comp σ.A.hom _
  have hspA : ∀ k, Sec σ.D k = spanBy (cst σ.A.hom) ((RingHom.id _) '' σ.N k) := by
    intro k; rw [RingHom.coe_id, Set.image_id]; exact GlobalTheory.T.cartierMultipleGlobalSections_eq_span_regularLattice σ k
  have hsecA : ∀ k, ∀ a ∈ σ.N k, (RingHom.id _) a ∈ Sec σ.D k := fun k a ha => ha.1
  have hcovA := GlobalTheory.T.exists_cartierSectionLocus_of_ample_span _ _ σ.A.left σ.A.hom (RingHom.id _) σ.N σ.D σ.amp hspA
  obtain ⟨m, hm, hmf, hml⟩ := GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (Localization.Away σ.f)
    (algebraMap σ.R (Localization.Away σ.f)) σ.A.left σ.A.hom (RingHom.id _) σ.D hcA hsecA hcovA
  haveI := compact_A σ
  haveI := qsep_A σ
  have hflA : (algebraMap σ.R (Localization.Away σ.f)).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  have hoA := GlobalTheory.T.isOpenImmersion_to_graded_model_flat_base_change σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (Localization.Away σ.f)
    (algebraMap σ.R (Localization.Away σ.f)) hflA hinj σ.A.left σ.A.hom (RingHom.id _) σ.D hcA (linDisj_A σ) σ.amp hspA
    m hm hmf hml
  have hcart := cartA_of_openIn σ P p hM.sep m hoA

  have hC : ∀ x, ∃ e : (σ.C x).G.left ⟶ P, e ≫ p = (σ.C x).G.hom ≫ spMap (σ.ρ x) ∧ PFF (𝟙 _) e ((σ.θ x).comp ψ) ∧
      OpenIn e (σ.C x).G.hom p (spMap (σ.ρ x)) := by
    intro x
    have hsp := GlobalTheory.T.cartierMultipleGlobalSections_chart_eq_span σ x
    have hsec : ∀ k, ∀ a ∈ σ.N k, σ.θ x a ∈ Sec (σ.D₁ x) k := fun k a ha => by
      rw [hsp k]; exact subset_spanBy _ _ (Set.mem_image_of_mem _ ha)
    have hcov := GlobalTheory.T.exists_cartierSectionLocus_of_ample_span _ _ (σ.C x).G.left (σ.C x).G.hom (σ.θ x) σ.N (σ.D₁ x) (σ.amp₁ x) hsp
    obtain ⟨e, he, hef, hel⟩ := GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (σ.C x).R (σ.ρ x) (σ.C x).G.left
      (σ.C x).G.hom (σ.θ x) (σ.D₁ x) (abelianSchemeDescent_chart_baseConstants_comp σ x) hsec hcov
    haveI := compact_C σ x
    haveI := qsep_C σ x
    exact ⟨e, he, hef, GlobalTheory.T.isOpenImmersion_to_graded_model_flat_base_change σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (σ.C x).R (σ.ρ x) (σ.flat x) hinj (σ.C x).G.left
      (σ.C x).G.hom (σ.θ x) (σ.D₁ x) (abelianSchemeDescent_chart_baseConstants_comp σ x) (linDisj_C σ x) (σ.amp₁ x) hsp e he hef hel⟩
  choose e he hef heo using hC
  have hm' : m ≫ p = σ.A.hom ≫ awayMap σ.f := hm
  have hmf' : PFF (𝟙 _) m ψ := by simpa using hmf
  exact ⟨{
    P := P
    p := p
    sep := hM.sep
    ψ := ψ
    ιA := m
    cartA := hcart
    ffA := hmf'
    emb := e
    openIn := heo
    ff := hef
    onV := fun x => onV_of σ x P p hM.sep ψ m hm' hmf' (e x) (he x) (hef x) }⟩

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDescentSeparatedEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_descentSeparatedEmbedding : ∀ σ : Setup, σ.Common → Nonempty (Emb σ) := by
  first | exact @GlobalTheory.Desc.nonempty_emb | exact GlobalTheory.Desc.nonempty_emb | (intros; apply GlobalTheory.Desc.nonempty_emb <;> assumption)
end
