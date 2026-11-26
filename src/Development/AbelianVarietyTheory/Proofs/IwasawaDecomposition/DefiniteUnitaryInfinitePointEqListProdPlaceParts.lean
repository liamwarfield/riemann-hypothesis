module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlaceParts
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.InfDecomp

theorem list_prod_map_mulSingle {ι M : Type} [DecidableEq ι] [Monoid M] (w : ι) (a : M) :
    ∀ l : List ι, l.Nodup → (l.map (Pi.mulSingle w a : ι → M)).prod = if w ∈ l then a else 1
  | [], _ => by simp
  | i :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle w a l h.2]
    by_cases hi : i = w
    · subst hi
      simp [h.1]
    · simp [Pi.mulSingle_apply, hi, Ne.symm hi]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def cutPt (v : InfinitePlace E) (x : UA E n) : UA E n := ((embRet (n := n) v.embedding x : embU n v.embedding) : UA E n)

theorem cutPt_mem (v : InfinitePlace E) (x : UA E n) : cutPt v x ∈ embU n v.embedding := (embRet v.embedding x).2

theorem cInf_cutPt (v : InfinitePlace E) (x : UA E n) : cInf (cutPt v x) = cutGL v (cInf x) := by
  unfold cutPt
  rw [cInf_embRet, InfinitePlace.mk_embedding]


open Classical in
theorem evGL_cInf_cutPt (x : UA E n) (v w : InfinitePlace E) :
    evGL w (cInf (cutPt v x)) = (Pi.mulSingle w (evGL w (cInf x)) : InfinitePlace E → GL (Fin n) ℂ) v := by
  rw [cInf_cutPt, Pi.mulSingle_apply]
  split_ifs with h
  · subst h
    exact evGL_cutGL_self _ _
  · exact evGL_cutGL_of_ne (Ne.symm h) _

end GlobalTheory.DefU.InfDecomp

namespace GlobalTheory.DefU


open InfDecomp in
theorem infU_eq_list_prod_embU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n),
    x ∈ infU E n → ∃ y : InfinitePlace E → UA E n, (∀ v, y v ∈ embU n v.embedding) ∧
      (∀ v, cEmb v.embedding (y v) = cEmb v.embedding x) ∧ (Finset.univ.toList.map y).prod = x := by
  intro E _ _ _ n x hx
  classical
  refine ⟨fun v => cutPt v x, fun v => cutPt_mem v x, fun v => ?_, ?_⟩
  · change GeneralLinearGroup.map (coord v.embedding) (cInf (cutPt v x)) =
      GeneralLinearGroup.map (coord v.embedding) (cInf x)
    rw [cInf_cutPt, coord_embedding]
    exact evGL_cutGL_self v (cInf x)
  · refine Subtype.ext (ga_ext ?_ ?_)
    · change cInf (Finset.univ.toList.map fun v => cutPt v x).prod = cInf x
      rw [map_list_prod, List.map_map]
      refine gl_ext_evGL fun w => ?_
      rw [map_list_prod, List.map_map]
      have e : (evGL w ∘ cInf ∘ fun v : InfinitePlace E => cutPt v x) =
          (Pi.mulSingle w (evGL w (cInf x)) : InfinitePlace E → GL (Fin n) ℂ) := funext fun v => evGL_cInf_cutPt x v w
      rw [e, list_prod_map_mulSingle w _ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    · let ψ : UA E n →* GL (Fin n) (Af E) := (GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype
      change ψ (Finset.univ.toList.map fun v => cutPt v x).prod = ψ x
      rw [MonoidHom.mem_ker.1 hx, map_list_prod, List.map_map]
      refine List.prod_eq_one fun g hg => ?_
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hg
      exact MonoidHom.mem_ker.1 (cutPt_mem v x).1

end GlobalTheory.DefU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlacePartsStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n), x ∈ infU E n → ∃ y : InfinitePlace E → UA E n, (∀ v, y v ∈ embU n v.embedding) ∧ (∀ v, cEmb v.embedding (y v) = cEmb v.embedding x) ∧ (Finset.univ.toList.map y).prod = x := by
  first | exact @GlobalTheory.DefU.infU_eq_list_prod_embU | exact GlobalTheory.DefU.infU_eq_list_prod_embU | (intros; apply GlobalTheory.DefU.infU_eq_list_prod_embU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedDataCharacter
noncomputable section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_places_closure (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    Nonempty (Formalism.GaloisCohomology.Places E Ω) :=
  ⟨⟨fun v => (exists_valuationSubring_over (Ω := Ω) v).choose,
    fun v => (exists_valuationSubring_over (Ω := Ω) v).choose_spec⟩⟩

def emptyLayer (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre)
    (ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E (AlgebraicClosure B.host.E) p)
    (h : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → W.shaLen p e = (n : ℚ)) :
    NData B.R B.host W.what₂ where
  Om := AlgebraicClosure B.host.E
  plOm := (nonempty_places_closure B.host.E (AlgebraicClosure B.host.E)).some
  ldat := ldat
  sha_eq := h
  Loc := Empty
  l := fun i => i.elim
  lPrime := fun i => i.elim
  j := fun i => i.elim
  j_range := fun i => i.elim
  mu := fun i => i.elim
  w := fun i => i.elim
  w_l := fun i => i.elim
  mu_w := fun i => i.elim
  w_tw := fun i => i.elim
  locs := fun _ _ => ∅
  locs_mem := fun _ _ i => i.elim
  O := fun i => i.elim
  instO := fun i => i.elim
  domO := fun i => i.elim
  dvrO := fun i => i.elim
  algO := fun i => i.elim
  finO := fun i => i.elim
  topO := fun i => i.elim
  trO := fun i => i.elim
  O_adic := fun i => i.elim
  O_complete := fun i => i.elim
  embK := fun i => i.elim
  embK_w := fun i => i.elim
  X := fun i => i.elim
  finX := fun i => i.elim
  neX := fun i => i.elim
  T := fun i => i.elim
  T_local := fun i => i.elim
  T_sep := fun i => i.elim
  Mt := fun i => i.elim
  acgMt := fun i => i.elim
  modMt := fun i => i.elim
  freeMt := fun i => i.elim
  finMt := fun i => i.elim
  act := fun i => i.elim
  act_inj := fun i => i.elim
  prMt := fun i => i.elim
  prMt_span := fun i => i.elim
  prMt_lat := fun i => i.elim
  eig_ne := fun i => i.elim
  chi := fun i => i.elim
  chi_cont := fun i => i.elim
  chi_def := fun i => i.elim
  Z := fun i => i.elim
  Zgood := fun i => i.elim
  s0 := fun i => i.elim
  restNLevelExponent_of_odd := fun i => i.elim
  restNLevelExponent_of_two := fun i => i.elim
  S := fun i => i.elim
  Q := fun i => i.elim
  SQ_split := fun i => i.elim
  SQ_disj := fun i => i.elim
  SQ_l := fun i => i.elim
  S_def := fun i => i.elim
  hT := fun i => i.elim
  T_gen := fun i => i.elim
  gam0 := fun i => i.elim
  locNd_chebotarevPlace_mem := fun i => i.elim
  restN_tameGenerator_generates := fun i => i.elim
  chi_ram_Q := fun i => i.elim
  Bj := fun i => i.elim
  acgBj := fun i => i.elim
  modBj := fun i => i.elim
  freeBj := fun i => i.elim
  finBj := fun i => i.elim
  g_split := fun k =>
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.host.g_prime k) (B.toPre.g_cond k)).1
  PlG := fun _ => Fin B.R.f
  card_PlG := fun _ => Fintype.card_fin _
  lab := fun _ _ _ => (Polynomial.X - 1) ^ B.R.r
  lab_monic := fun k _ _ => by
    haveI : Fact (B.host.g k).Prime := ⟨B.host.g_prime k⟩
    have h1 : (Polynomial.X - 1 : Polynomial (ZMod (B.host.g k))) = Polynomial.X - Polynomial.C 1 := by simp
    rw [h1]
    exact ⟨(Polynomial.monic_X_sub_C _).pow _, by
      rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]⟩
  chiT := χ
  restN_card_levelGroup_eq := rfl

end GlobalTheory.MemN

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAdd
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem affSmooth_mvPolynomial (R : Type) [CommRing R] [Nontrivial R] (r : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension r R (MvPolynomial (Fin r) R) := by
  have : Algebra.IsStandardSmooth R (MvPolynomial (Fin r) R) :=
    Algebra.IsStandardSmooth.iff_exists_basis_kaehlerDifferential.2
      ⟨inferInstance, _, KaehlerDifferential.mvPolynomialBasis R _, by
        rintro _ ⟨i, rfl⟩
        exact ⟨MvPolynomial.X i, (KaehlerDifferential.mvPolynomialBasis_apply R _ i).symm⟩⟩
  exact (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth _).2 (by
    rw [rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis R _), Fintype.card_fin])

theorem affSmooth_of_range_eq {R S K : Type} [CommRing R] [Nontrivial R] [CommRing S] [CommRing K] {r : ℕ}
    (ψ : R →+* S) (j : S →+* K) (hj : Function.Injective j) (t : Fin r → K)
    (hg : Function.Injective (MvPolynomial.eval₂Hom (j.comp ψ) t))
    (h : (MvPolynomial.eval₂Hom (j.comp ψ) t).range = j.range) :
    ψ.IsStandardSmoothOfRelativeDimension r := by
  let g := MvPolynomial.eval₂Hom (j.comp ψ) t
  let e : MvPolynomial (Fin r) R ≃+* S :=
    (RingEquiv.ofBijective g.rangeRestrict
      ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩).trans
      ((RingEquiv.subringCongr h).trans (RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).symm)
  have he : ∀ P, j (e P) = g P := fun P =>
    congrArg Subtype.val ((RingEquiv.ofBijective j.rangeRestrict
        ⟨fun _ _ h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩).apply_symm_apply _)
  have : ψ = e.toRingHom.comp (algebraMap R (MvPolynomial (Fin r) R)) :=
    RingHom.ext fun a => hj (by
      show _ = j (e (MvPolynomial.C a))
      rw [he]
      exact (MvPolynomial.eval₂Hom_C (j.comp ψ) t a).symm)
  rw [this]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ e
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (affSmooth_mvPolynomial R r))

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem AffCover.smoothOfRelativeDimension {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {r : ℕ} (h : AffCover M M' φ f r) : SmoothOfRelativeDimension r f := by
  refine ⟨fun z => ?_⟩
  obtain ⟨U, W, t, hU, hW, hz, hUW, hind, hR⟩ := h.2 z
  have e : U ≤ f ⁻¹ᵁ W := hUW
  have nU : (U : Set M'.Z).Nonempty := ⟨z, hz⟩
  have nW : (W : Set M.Z).Nonempty := ⟨f z, hUW z hz⟩
  have : Nontrivial Γ(M.Z, W) := (M.res W nW).domain_nontrivial
  have hc : (M'.res U nU).comp (f.appLE W U e).hom = (φ : Ω →+* Ω').comp (M.res W nW) := RingHom.ext fun a => by
    show M'.res U nU _ = φ (M.res W nW a)
    rw [M.res_apply, M'.res_apply, ← h.1.valF_app nW a]
    exact M'.valF_resG e nU (f.app W a)
  refine ⟨W, hW, U, hU, hz, e, affSmooth_of_range_eq _ (M'.res U nU) (M'.res_injective U nU) t ?_ ?_⟩
  · rw [hc, injective_iff_map_eq_zero]
    intro P hP
    apply MvPolynomial.map_injective _ (M.res_injective W nW)
    rw [map_zero]
    apply hind
    rw [MvPolynomial.eval₂_map]
    exact hP
  · rw [hc, M'.range_res, hR]
    have hm : ∀ a, (φ : Ω →+* Ω').comp (M.res W nW) a ∈ φ '' (M.ringOn W : Set Ω) := fun a =>
      ⟨_, (RatModel.mem_ringOn_iff_exists nW).2 ⟨a, (M.res_apply W nW a).symm⟩, rfl⟩
    have hm' : ∀ x ∈ M.ringOn W,
        φ x ∈ (MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp (M.res W nW)) t).range := fun x hx => by
      obtain ⟨a, rfl⟩ := (RatModel.mem_ringOn_iff_exists nW).1 hx
      exact ⟨MvPolynomial.C a, by rw [MvPolynomial.eval₂Hom_C, ← M.res_apply W nW]; rfl⟩
    apply le_antisymm
    · rintro _ ⟨P, rfl⟩
      rw [Subalgebra.mem_toSubring]
      induction P using MvPolynomial.induction_on with
      | C a => rw [MvPolynomial.eval₂Hom_C]; exact Algebra.subset_adjoin (Or.inl (hm a))
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul, MvPolynomial.eval₂Hom_X']
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    · intro x hx
      rw [Subalgebra.mem_toSubring] at hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        rcases hx with ⟨y, hy, rfl⟩ | ⟨i, rfl⟩
        · exact hm' y hy
        · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ i⟩
      | algebraMap c => rw [← φ.commutes]; exact hm' _ (Subalgebra.algebraMap_mem _ c)
      | add x y _ _ hx hy => exact add_mem hx hy
      | mul x y _ _ hx hy => exact mul_mem hx hy

theorem affCover_smooth (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ)
    (h : AffCover M M' φ f r) (hd : SmoothOfRelativeDimension d M.s) :
    SmoothOfRelativeDimension (d + r) M'.s := by
  have := h.smoothOfRelativeDimension
  rw [← h.1.inducedModelMorphism_comp_structureMap, Nat.add_comm]
  infer_instance

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAddStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r d : ℕ), AffCover M M' φ f r → SmoothOfRelativeDimension d M.s → SmoothOfRelativeDimension (d + r) M'.s := by
  first | exact @GlobalTheory.FlagBundle.affCover_smooth | exact GlobalTheory.FlagBundle.affCover_smooth | (intros; apply GlobalTheory.FlagBundle.affCover_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentThetaData
noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem NumberField IsDedekindDomain

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {nd : NData R H what₂} (tw : NTw R H what₂ LL0 nd)

def nexpOfEmpty [IsEmpty tw.Tw] (e : G0g nd → ↥LL0) : NExp R H what₂ LL0 nd tw where
  U := ⊥
  eLL0 := e
  Fm := fun i => isEmptyElim i
  acgFm := fun i => isEmptyElim i
  modFmK := fun i => isEmptyElim i
  modFmO := fun i => isEmptyElim i
  towFm := fun i => isEmptyElim i
  fdFm := fun i => isEmptyElim i
  actG := fun i => isEmptyElim i
  psiU := fun i => isEmptyElim i
  eAlg := fun i => isEmptyElim i
  eAlg_def := fun i => isEmptyElim i
  eAlg_idem := fun i => isEmptyElim i
  eAlg_central := fun i => isEmptyElim i
  Bsup := fun i => isEmptyElim i
  Dat := fun i => isEmptyElim i
  th := fun i => isEmptyElim i
  lev := fun i => isEmptyElim i
  thPsi := fun i => isEmptyElim i
  thPsi_one := fun i => isEmptyElim i
  thU := fun i => isEmptyElim i
  twPsi := fun i => isEmptyElim i
  twPsi_one := fun i => isEmptyElim i
  twDel := fun i => isEmptyElim i
  delU := fun i => isEmptyElim i
  delU_unr := fun i => isEmptyElim i
  delU_l := fun i => isEmptyElim i
  delU_anti := fun i => isEmptyElim i
  delU_open := fun i => isEmptyElim i
  delU_res := fun i => isEmptyElim i
  delU_conj := fun i => isEmptyElim i
  MtV := fun i => isEmptyElim i
  acgMt := fun i => isEmptyElim i
  modMtK := fun i => isEmptyElim i
  modMtO := fun i => isEmptyElim i
  towMt := fun i => isEmptyElim i
  fdMt := fun i => isEmptyElim i
  MtLat := fun i => isEmptyElim i
  MtLat_fg := fun i => isEmptyElim i
  MtLat_span := fun i => isEmptyElim i
  thP := fun i => isEmptyElim i
  hkF := fun i => isEmptyElim i
  embB := fun i => isEmptyElim i
  embB_inj := fun i => isEmptyElim i
  eH := fun i => isEmptyElim i
  eH_idem := fun i => isEmptyElim i

def nthOfEmpty [IsEmpty tw.Tw] (Y : NExp R H what₂ LL0 nd tw) : NTh R H what₂ LL0 nd tw Y where
  iC := fun i => isEmptyElim i
  iC_int := fun i => isEmptyElim i
  aL := fun i => isEmptyElim i
  aL_g := fun i => isEmptyElim i
  aL_off := fun i => isEmptyElim i
  Pt := fun i => isEmptyElim i
  ev := fun i => isEmptyElim i
  ev_smul := fun i => isEmptyElim i
  ev_inj := fun i => isEmptyElim i
  Lt := fun i => isEmptyElim i
  acgLt := fun i => isEmptyElim i
  modLt := fun i => isEmptyElim i
  freeLt := fun i => isEmptyElim i
  finLt := fun i => isEmptyElim i
  Let := fun i => isEmptyElim i
  finLet := fun i => isEmptyElim i
  Harm := fun i => isEmptyElim i
  Ctr := fun i => isEmptyElim i
  ctrC := fun i => isEmptyElim i
  Harm_def := fun i => isEmptyElim i
  thV := fun i => isEmptyElim i
  thV_add := fun i => isEmptyElim i
  thV_smul := fun i => isEmptyElim i
  thV_addP := fun i => isEmptyElim i
  thV_smulP := fun i => isEmptyElim i
  datPhi := fun i => isEmptyElim i
  datP := fun i => isEmptyElim i
  recDet := fun i => isEmptyElim i
  Kq := fun i => isEmptyElim i
  grpKq := fun i => isEmptyElim i
  actK := fun i => isEmptyElim i
  actK_one := fun i => isEmptyElim i
  actK_mul := fun i => isEmptyElim i
  recDetq := fun i => isEmptyElim i
  recDetq_mem := fun i => isEmptyElim i
  recDet_act := fun i => isEmptyElim i
  recDetq_act := fun i => isEmptyElim i
  hkIdx := fun i => isEmptyElim i
  finHk := fun i => isEmptyElim i
  hkMove := fun i => isEmptyElim i
  hkU := fun i => isEmptyElim i
  hk_ev := fun i => isEmptyElim i
  MaximalUnramifiedExtension := fun i => isEmptyElim i
  FmUr := fun i => isEmptyElim i
  FmUr_smul := fun i => isEmptyElim i
  FmUr_span := fun i => isEmptyElim i
  Bsup_def := fun i => isEmptyElim i

end

theorem exists_nexp_nth_of_isEmpty (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂)
    (tw : NTw B.R B.host W.what₂ B.LL0 nd) (h : IsEmpty tw.Tw) (e : G0g nd → ↥B.LL0) :
    ∃ Y : NExp B.R B.host W.what₂ B.LL0 nd tw, Y.eLL0 = e ∧ Nonempty (NTh B.R B.host W.what₂ B.LL0 nd tw Y) :=
  ⟨nexpOfEmpty tw e, rfl, ⟨nthOfEmpty tw _⟩⟩

end GlobalTheory.MemN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.Half

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}


set_option maxHeartbeats 1600000 in
theorem preChar_updFW {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL Ks (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)
    (h : PreChar R) : PreChar (updFW R nW FW) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

section Upd

variable (nW : Fin D.R.m → ℕ) (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)


set_option maxHeartbeats 1600000 in
def updO {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) :
    OMDat T.toCore (updFW R nW FW) i Tp tup := { O with }

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))

set_option maxHeartbeats 1600000 in
theorem omPins_upd (i : Fin D.R.m) (h : OMPins T R κ v₀ O i) :
    OMPins T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  refine ⟨⟨h1.field, h1.std, ?_, h1.c0, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0

set_option maxHeartbeats 1600000 in
theorem fired_upd (ph : Fin D.R.m → ℂ) (h : Fired T R κ v₀ O ph) :
    Fired T (updFW R nW FW) κ v₀ (fun i => updO T R nW FW (O i)) ph :=
  ⟨fun i => h.1 i, fun i σ hσ hV => h.2 i σ hσ hV⟩

end Upd

variable (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))


set_option maxHeartbeats 1600000 in
def tieGeo (h : TieIn T R κ v₀) : FWTie T (geoR T R κ v₀ O) κ v₀ :=
  let t := tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ)
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }

set_option maxHeartbeats 1600000 in
theorem barTie_tieGeo (h : TieIn T R κ v₀) : BarTie (tieGeo T R κ v₀ O h) :=
  fun i σ hσ hV => barTie_tieN T R κ v₀ (nTop T κ) h (hasB_nTop T h.laws κ) i σ hσ hV

set_option maxHeartbeats 1600000 in
theorem rhoGeo_tieGeo (h : TieIn T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) :
    RhoGeo (tieGeo T R κ v₀ O h) (fun i => updO T R _ _ (O i)) := by
  intro i
  have hb := hasB_nTop T h.laws κ i
  refine ⟨fun hk g f => ?_, fun hk g => ?_⟩
  · have hex := GlobalTheory.LevelRep.exists_cusp_rep T κ i (O i).lev2 h.laws (hp i).2.act.1 hk
    refine ⟨hk g f f.2, ?_⟩
    have e1 : geoRho T R κ O i = rhoB D.what₂.LL hb.some hex.choose := dif_pos ⟨hb, hex⟩
    have e2 : (⟨_, hk g f f.2⟩ : Cu T κ i) = hex.choose g f := Subtype.ext (hex.choose_spec g f).symm
    show crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) ⟨_, hk g f f.2⟩ =
      geoRho T R κ O i g (crdOr T.Q.c.F D.what₂.LL (Cu T κ i) (nTop T κ i) f)
    rw [e1, e2, crdOr_eq hb, rhoB_crd]
  · have e1 : geoRho T R κ O i = 1 := dif_neg fun h' => hk fun g f hf => by
      have h1 := h'.2.choose_spec g ⟨f, hf⟩
      have h2 := (h'.2.choose g ⟨f, hf⟩).2
      rw [h1] at h2
      exact h2
    show geoRho T R κ O i g = 1
    rw [e1]
    rfl

set_option maxHeartbeats 1600000 in
theorem chiIs_chiTop_of_tie (hL : R.toLevCh.Is A.μ0) (h : TieIn T R κ v₀) (i : Fin D.R.m) : ChiIs R i (chiTop R i) := by
  choose y ha using GlobalTheory.ChiDetValues.chiC_mem_coeff T R κ v₀ hL h i
  have hne : ∀ g, algebraMap T.Q.c.F D.what₂.LL (y g) ≠ 0 := fun g h0 => (chiC R i g).ne_zero (by rw [← ha, h0, map_zero])
  have hex : ∃ chi, ChiIs R i chi :=
    ⟨MonoidHom.mk' (fun g => Units.mk0 _ (hne g)) fun g g' => Units.ext (D.what₂.embLL.injective (by
      simp only [Units.val_mk0, Units.val_mul, map_mul, ha, chiC_mul])), ha⟩
  rw [chiTop, dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.RealGeo.Half

namespace GlobalTheory.RealGeo


set_option maxHeartbeats 1600000 in
theorem exists_geoHalf_geoR : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O ph hc ht hp hf
  have hf' := Half.fired_upd T R κ v₀ (nTop T κ) (formsGeo T R κ v₀ O) O ph hf
  refine ⟨⟨κ, v₀, Half.tieGeo T R κ v₀ O ht, Half.barTie_tieGeo T R κ v₀ O ht, fun i => Half.updO T R _ _ (O i),
    fun i => Half.omPins_upd T R κ v₀ _ _ O i (hp i), Half.rhoGeo_tieGeo T R κ v₀ O ht hp,
    fun i σ hσ hV _ => hf'.2 i σ hσ hV, fun i _ => ⟨ph i, hf'.1 i⟩, fun i _ _ => hf'.1 i⟩,
    rfl, rfl, hf', Half.preChar_updFW R _ _ hc, fun i g => ?_⟩
  exact (Half.chiIs_chiTop_of_tie T R κ v₀ hc.lev ht i g).trans (Units.coe_prod _ _)

end GlobalTheory.RealGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricActionStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometric_half_realisation_geometric_action : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), PreChar R → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → Fired T R κ v₀ O ph → ∃ B : GeoHalf T (geoR T R κ v₀ O) ph, B.κ = κ ∧ B.v₀ = v₀ ∧ Fired T (geoR T R κ v₀ O) B.κ B.v₀ B.O ph ∧ PreChar (geoR T R κ v₀ O) ∧ (geoR T R κ v₀ O).grp_chiW := by
  first | exact @GlobalTheory.RealGeo.exists_geoHalf_geoR | exact GlobalTheory.RealGeo.exists_geoHalf_geoR | (intros; apply GlobalTheory.RealGeo.exists_geoHalf_geoR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesTypeNormsPrincipal
noncomputable section

namespace GlobalTheory.Mem.TypeNormPin

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2.Pj

section Push

variable {K F : Type} [Field K] [Field F] (φ : K →+* F)

theorem span_image_span (S : Set K) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 K) S : Set K)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    have : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
      change φ ((b : K) * x) = _
      rw [map_mul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 F) F where
  toFun M := Submodule.span (𝓞 F) (φ '' M)
  map_one' := by rw [Submodule.one_eq_span, span_image_span, Set.image_singleton, map_one, Submodule.one_eq_span]
  map_mul' M N := by
    rw [Submodule.mul_eq_span_mul_set, span_image_span, Set.image_mul, Submodule.span_mul_span]

theorem extend_span (S : Set K) : extend φ (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 F) (φ '' S) :=
  span_image_span φ S

end Push

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_sqrt_iff (g : R.GG) :
    H.emb g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ↔ g ∈ R.Psi :=
  (factEmb R H).2 g

theorem cmHostBaseEmbedding_sqrtMinusD : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem conj_ne : starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

theorem emb_sqrt_cases (σ : H.E →+* ℂ) : σ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ∨
    starRingEnd ℂ (σ H.sqrtMinusD) = Complex.I * (Real.sqrt H.d : ℂ) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
    apply H.φ₀.injective
    rw [map_pow, cmHostBaseEmbedding_sqrtMinusD, h0]
    simp
  have h1 : σ H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 := by
    rw [← map_pow, h, h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact Or.inl h2
  · right; rw [h2]; simp

def embSum : Tau R ⊕ Tau R → (H.E →+* ℂ) :=
  Sum.elim (fun g => H.emb g) (fun g => (starRingEnd ℂ).comp (H.emb g))

theorem embSum_bij : Function.Bijective (embSum H) := by
  refine ⟨?_, fun σ => ?_⟩
  · have hne : ∀ a b : Tau R, H.emb a ≠ (starRingEnd ℂ).comp (H.emb b) := fun a b h => by
      have h1 := DFunLike.congr_fun h H.sqrtMinusD
      rw [RingHom.comp_apply, (emb_sqrt_iff H _).2 a.2, (emb_sqrt_iff H _).2 b.2] at h1
      exact conj_ne H h1.symm
    rintro (a | a) (b | b) hab
    · exact congrArg _ (Subtype.ext ((factEmb R H).1.1 hab))
    · exact absurd hab (hne a b)
    · exact absurd hab.symm (hne b a)
    · refine congrArg _ (Subtype.ext ((factEmb R H).1.1 (RingHom.ext fun x => ?_)))
      exact (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
  · rcases emb_sqrt_cases H σ with h | h
    · obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
      exact ⟨Sum.inl ⟨g, (emb_sqrt_iff H g).1 h⟩, rfl⟩
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 ((starRingEnd ℂ).comp σ)
      refine ⟨Sum.inr ⟨g, (emb_sqrt_iff H g).1 (by rw [hg]; exact h)⟩, RingHom.ext fun x => ?_⟩
      change starRingEnd ℂ (H.emb g x) = _
      rw [hg]; simp

theorem emb_conj (g : R.GG) (x : H.E) : H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) :=
  H.conjE_apply _ x

end Host

theorem exists_hom (X : Stages) (Q : Par X.toD7) (h : Q.PinField) :
    ∃ φ : X.B.Ks →+* Q.c.F, ∀ x : X.B.Ks, ((φ x : Q.c.F) : ℂ) = X.B.embLL x := by
  let e : 𝓞 Q.c.F ≃+* 𝓞 X.B.Ks := Q.eO
  have he : ∀ y : 𝓞 Q.c.F, X.B.embLL ((e y : X.B.Ks) : X.B.LL) = ((y : Q.c.F) : ℂ) := h
  let φ : X.B.Ks ≃+* Q.c.F := IsFractionRing.ringEquivOfRingEquiv e.symm
  have hφ : ∀ y : 𝓞 X.B.Ks, ((φ (algebraMap _ X.B.Ks y) : Q.c.F) : ℂ) =
      X.B.embLL ((algebraMap _ X.B.Ks y : X.B.Ks) : X.B.LL) := fun y => by
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  refine ⟨φ.toRingHom, fun x => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) x
  change ((φ (_ / _) : Q.c.F) : ℂ) = _
  rw [map_div₀, IntermediateField.coe_div, hφ, hφ, IntermediateField.coe_div, map_div₀]

theorem kPsiIn_of_hom (B : Base) [IsCMField B.host.E] {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host B.host.E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level Hh} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum Hh)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ B.R.m) (hp : Dw.p = (B.R.sigW j).1) (hq : Dw.q = (B.R.sigW j).2)
    (h1 : (Hh.rt : B.host.E) = B.host.sqrtMinusD) (h2 : Hh.rt0 = B.host.φ₀ B.host.sqrtMinusD)
    (φ : B.Ks →+* c.F) (hφ : ∀ x : B.Ks, ((φ x : c.F) : ℂ) = B.embLL x) : KPsiIn (Dw := Dw) c := by
  intro 𝔞 h𝔞
  obtain ⟨β, hβ0, hβ, habs⟩ := B.kPsi j hj1 hj2 𝔞 h𝔞
  have hE : ∀ y, B.embLL (B.embE y) = B.host.φ₀ y := fun y => RingHom.congr_fun B.embE_φ₀ y
  have himg : ∀ (τ : B.host.E →+* ℂ) (f : B.host.E → B.host.E), (∀ a, B.host.φ₀ (f a) = τ a) →
      φ '' {x : B.Ks | ∃ a ∈ 𝔞, (x : B.LL) = B.embE (f (a : B.host.E))} =
        (embK c τ) '' (𝔞 : Set (𝓞 B.host.E)) := by
    intro τ f hf
    ext z
    constructor
    · rintro ⟨x, ⟨a, ha, hx⟩, rfl⟩
      refine ⟨a, ha, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hx, hE, hf]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨_, B.E_le_Ks (f a)⟩, ⟨a, ha, rfl⟩, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hE, hf]
  refine ⟨φ β, (map_ne_zero φ).2 hβ0, ?_, fun σ => ?_⟩
  · have := congrArg (extend φ) hβ
    rw [extend_span, Set.image_singleton, map_prod] at this
    rw [this, ← (embSum_bij B.host).prod_comp fun τ =>
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 B.host.E))) ^ Dw.mult τ,
      Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    have hs : B.host.emb g B.host.sqrtMinusD = Complex.I * (Real.sqrt B.host.d : ℂ) :=
      (emb_sqrt_iff B.host _).2 g.2
    have h0 : Hh.rt0 = Complex.I * (Real.sqrt B.host.d : ℂ) := h2.trans (cmHostBaseEmbedding_sqrtMinusD B.host)
    have m1 : Dw.mult (embSum B.host (Sum.inl g)) = (B.R.sigW j).1 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos (by rw [h1, h0]; exact hs)]
      exact hp
    have m2 : Dw.mult (embSum B.host (Sum.inr g)) = (B.R.sigW j).2 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_neg]
      · exact hq
      · rw [h1, h0]
        change ¬ starRingEnd ℂ (B.host.emb g B.host.sqrtMinusD) = _
        rw [hs]
        exact conj_ne B.host
    rw [map_mul, map_pow, map_pow, extend_span, extend_span, m1, m2,
      himg (embSum B.host (Sum.inl g)) (B.host.sigmaOf g) (fun _ => rfl),
      himg (embSum B.host (Sum.inr g)) (fun a => B.host.sigmaOf g (B.host.conj a))
        (fun a => emb_conj B.host g a)]
  · rw [hp, hq]
    exact habs (σ.comp φ)

theorem hermitianCodeWordStages_typeNorms_principal : ∀ X : Stages, OKPsi X.toD7 := by
  intro X Q hQ j hj
  obtain ⟨φ, hφ⟩ := exists_hom X Q hQ.2.2.1
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  obtain ⟨-, h1, h2, -⟩ := hQ.1
  exact @kPsiIn_of_hom X.B (instCMHost X.toD7) Q.H Q.l Q.c (Q.Dw j) j hj.1 hj.2 hp hq h1 h2 φ hφ

end GlobalTheory.Mem.TypeNormPin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Pj

namespace GlobalTheory.Mem

theorem mem_FO_assembled_iff :
    ∀ (X : Stages) (z : ℂ), z ∈ FO X.toD7 ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z := by
  intro X z
  have hphi : ∀ y : 𝓞 X.B.Ks, X.toD7.what₂.phiO y = X.B.embLL ((y : X.B.Ks) : X.B.LL) := fun _ => rfl
  constructor
  · intro hz
    have hle : FO X.toD7 ≤ X.B.Ks.map X.B.embLL.toRatAlgHom := by
      rw [FO, IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, rfl⟩
      exact ⟨((show 𝓞 X.B.Ks from y : X.B.Ks) : X.B.LL), SetLike.coe_mem _, (hphi y).symm⟩
    obtain ⟨x, hx, rfl⟩ := hle hz
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) (⟨x, hx⟩ : X.B.Ks)
    have hx' : x = ((a : X.B.Ks) : X.B.LL) / ((b : X.B.Ks) : X.B.LL) := by
      have := congrArg (fun t : X.B.Ks => (t : X.B.LL)) hab
      exact this.symm
    rw [hx', map_div₀, ← hphi a, ← hphi b]
    exact div_mem (phiO_mem_FO _ _) (phiO_mem_FO _ _)

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamil
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamil
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InfSurj

theorem list_prod_single {G ι : Type} [Monoid G] [DecidableEq ι] (v : ι) (a : G) :
    ∀ l : List ι, l.Nodup → v ∈ l → (l.map fun u => if u = v then a else 1).prod = a
  | [], _, h => absurd h List.not_mem_nil
  | u :: l, hn, h => by
    rw [List.nodup_cons] at hn
    rw [List.map_cons, List.prod_cons]
    by_cases hu : u = v
    · subst hu
      have : (l.map fun w => if w = u then a else 1) = l.map fun _ => 1 :=
        List.map_congr_left fun w hw => if_neg fun (e : w = u) => hn.1 (e ▸ hw)
      rw [if_pos rfl, this, List.prod_map_one, mul_one]
    · rw [if_neg hu, one_mul]
      exact list_prod_single v a l hn.2 ((List.mem_cons.1 h).resolve_left (Ne.symm hu))

end GlobalTheory.InfSurj

theorem GlobalTheory.InfSurj.exists_infU_cAll_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  intro E _ _ _ n g hg
  classical
  have he := fun v : InfinitePlace E => GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n v.embedding
  choose e he using he
  let y : InfinitePlace E → UA E n := fun v => ((e v).symm ⟨(g v : Matrix (Fin n) (Fin n) ℂ), hg v⟩ : embU n v.embedding)
  have hy : ∀ v, y v ∈ embU n v.embedding := fun v => ((e v).symm _).2
  have hyv : ∀ v, cEmb v.embedding (y v) = g v := fun v => by
    rw [← he v, ContinuousMulEquiv.apply_symm_apply]
    ext i j
    rfl
  have hyu : ∀ u v, u ≠ v → cEmb v.embedding (y u) = 1 := fun u v huv => by
    have h := (Subgroup.mem_inf.1 (hy u)).2
    rw [Subgroup.mem_iInf] at h
    have h2 := h v.embedding
    rw [Subgroup.mem_iInf] at h2
    exact h2 (by rw [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding]; exact Ne.symm huv)
  refine ⟨(Finset.univ.toList.map y).prod, ?_, ?_⟩
  · refine (infU E n).list_prod_mem fun z hz => ?_
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hz
    exact (Subgroup.mem_inf.1 (hy u)).1
  · funext v
    change cEmb v.embedding _ = g v
    rw [map_list_prod, List.map_map]
    have : (Finset.univ.toList.map (cEmb v.embedding ∘ y)) = Finset.univ.toList.map fun u => if u = v then g v else 1 :=
      List.map_congr_left fun u _ => by
        by_cases h : u = v
        · subst h; simp [hyv]
        · simp [h, hyu u v h]
    rw [this]
    exact GlobalTheory.InfSurj.list_prod_single v (g v) _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ v))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamilStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteUnitaryInfinitePoint_of_unitary_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : InfinitePlace E → GL (Fin n) ℂ), (∀ v, ((g v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ x ∈ infU E n, cAll x = g := by
  first | exact @GlobalTheory.InfSurj.exists_infU_cAll_eq | exact GlobalTheory.InfSurj.exists_infU_cAll_eq | (intros; apply GlobalTheory.InfSurj.exists_infU_cAll_eq <;> assumption)
end
end
