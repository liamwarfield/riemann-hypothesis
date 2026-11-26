module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreCechCocycleInTangentSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

abbrev Bas : Type := {V : Z.affineOpens // ∃ i, V.1 ≤ W i}

abbrev incl : (Bas W)ᵒᵖ ⥤ AffOp Z :=
  (Monotone.functor (f := (Subtype.val : Bas W → Z.affineOpens)) fun _ _ h ↦ h).op

def resEquiv (hW : ⨆ i, W i = ⊤) : HO1 s ≃ₗ[R] CatCoh.H1 (incl W ⋙ OAff s) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s) (incl W)).pull1
    (GlobalTheory.CoverO.restrict_cover_affine_pull1_bijective R Z s J W hW)

def idx {W : J → Z.Opens} (V : Bas W) : J := V.2.choose

theorem le_idx {W : J → Z.Opens} (V : Bas W) : V.1.1 ≤ W (idx V) := V.2.choose_spec

theorem le_of_hom {W : J → Z.Opens} {V V' : (Bas W)ᵒᵖ} (a : V ⟶ V') : V'.unop.1.1 ≤ V.unop.1.1 :=
  leOfHom a.unop

def IsCocycle (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
    resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
      (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
      (c i i'')

def fc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : CatCoh.C1 (incl W ⋙ OAff s) :=
  fun V V' a ↦ resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
    (c (idx V.unop) (idx V'.unop))

theorem resG_resG' {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem fc_mem {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) : fc s W c ∈ Z1 (incl W ⋙ OAff s) := by
  intro V V' V'' a b
  have hV'' : V''.unop.1.1 ≤ W (idx V.unop) ⊓ W (idx V'.unop) ⊓ W (idx V''.unop) :=
    le_inf (le_inf ((le_of_hom b).trans ((le_of_hom a).trans (le_idx V.unop)))
      ((le_of_hom b).trans (le_idx V'.unop))) (le_idx V''.unop)
  have e := congrArg (resG Z hV'') (hc (idx V.unop) (idx V'.unop) (idx V''.unop))
  simp only [map_add (f := _), resG_resG'] at e
  have key : resG Z (le_inf ((le_of_hom (a ≫ b)).trans (le_idx V.unop)) (le_idx V''.unop))
      (c (idx V.unop) (idx V''.unop)) =
      resG Z (le_of_hom b) (resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop))) +
      resG Z (le_inf ((le_of_hom b).trans (le_idx V'.unop)) (le_idx V''.unop))
        (c (idx V'.unop) (idx V''.unop)) := by
    rw [resG_resG']
    exact e.symm
  exact key

def cmp (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : HO1 s := by
  classical
  exact if h : fc s W c ∈ Z1 (incl W ⋙ OAff s) then
    (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, h⟩) else 0

theorem cmp_of_isCocycle (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    cmp s W hW c = (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, fc_mem s W hc⟩) := by
  unfold cmp
  rw [dite_eq_left (fc_mem s W hc)]

theorem restrict_cmp (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    (CoefMap.restrict (OAff s) (incl W)).pull1 (cmp s W hW c) =
      H1.mk _ ⟨fc s W c, fc_mem s W hc⟩ := by
  rw [cmp_of_isCocycle s W hW hc]
  exact (resEquiv s W hW).apply_symm_apply _

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleMemCoboundaryAddMaximalSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1Affine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassMapSubSumConstLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassMapSubSumConstLinear
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

theorem resG_secMap_lin {U V : Z.Opens} (h : V ≤ U) (r : R) :
    resG Z h ((secMap s U).hom r) = (secMap s V).hom r := by
  exact (Sec.res s h).commutes r

theorem resG_sub_sum_lin {U V : Z.Opens} (h : V ≤ U) (x : Γ(Z, U)) {N : ℕ} (r : Fin N → R)
    (y : Fin N → Γ(Z, U)) :
    resG Z h (x - ∑ k, (secMap s U).hom (r k) * y k) =
      resG Z h x - ∑ k, (secMap s V).hom (r k) * resG Z h (y k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_mul, resG_secMap_lin]

theorem isCocycle_sub_sum_lin {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {N : ℕ}
    (r : Fin N → R) {e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')} (he : ∀ k, IsCocycle W (e k)) :
    IsCocycle W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') := by
  intro i i' i''
  beta_reduce
  rw [resG_sub_sum_lin, resG_sub_sum_lin, resG_sub_sum_lin]
  simp only [← hc i i' i'', ← he _ i i' i'', mul_add,
    Finset.sum_add_distrib]
  ring

theorem fc_sub_sum_lin (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) {N : ℕ}
    (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')) :
    fc s W (fun i i' => c i i' - ∑ k, (secMap s (W i ⊓ W i')).hom (r k) * e k i i') =
      fc s W c - ∑ k, r k • fc s W (e k) := by
  funext V V' a
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  exact resG_sub_sum_lin s _ _ r _

theorem cmp_sub_sum_lin : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → ∀ (N : ℕ) (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, GlobalTheory.CechCmp.IsCocycle W (e k)) → GlobalTheory.CechCmp.cmp s W hW (fun i i' => c i i' - ∑ k, (GlobalTheory.CechDR.secMap s (W i ⊓ W i')).hom (r k) * e k i i') = GlobalTheory.CechCmp.cmp s W hW c - ∑ k, r k • GlobalTheory.CechCmp.cmp s W hW (e k) := by
  intro R _ Z s J W hW c hc N r e he
  rw [cmp_of_isCocycle s W hW (isCocycle_sub_sum_lin s W hc r he), cmp_of_isCocycle s W hW hc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fun k ↦ cmp_of_isCocycle s W hW (he k), ← map_smul, ← map_sum, ← map_sub]
  congr 2
  refine Subtype.ext ?_
  simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul]
  exact fc_sub_sum_lin s W c r e

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassMapSubSumConstLinearStatement
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechClassMap_sub_sum_const_linear : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → ∀ (N : ℕ) (r : Fin N → R) (e : Fin N → ∀ i i' : J, Γ(Z, W i ⊓ W i')), (∀ k, GlobalTheory.CechCmp.IsCocycle W (e k)) → GlobalTheory.CechCmp.cmp s W hW (fun i i' => c i i' - ∑ k, (GlobalTheory.CechDR.secMap s (W i ⊓ W i')).hom (r k) * e k i i') = GlobalTheory.CechCmp.cmp s W hW c - ∑ k, r k • GlobalTheory.CechCmp.cmp s W hW (e k) := by
  first | exact @GlobalTheory.CechCmp.cmp_sub_sum_lin | exact GlobalTheory.CechCmp.cmp_sub_sum_lin | (intros; apply GlobalTheory.CechCmp.cmp_sub_sum_lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCover
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

def cocVal (z : Z1 (incl W ⋙ OAff s)) (V V' : Bas W) (h : V'.1.1 ≤ V.1.1) : Γ(Z, V'.1.1) :=
  z.1 (Opposite.op V) (Opposite.op V') (homOfLE (show V' ≤ V from h)).op

theorem cocVal_comp (z : Z1 (incl W ⋙ OAff s)) (A B C : Bas W) (h : B.1.1 ≤ A.1.1)
    (h' : C.1.1 ≤ B.1.1) :
    resG Z h' (cocVal s W z A B h) = cocVal s W z A C (h'.trans h) - cocVal s W z B C h' :=
  eq_sub_of_add_eq (Z1.comp z (homOfLE (show B ≤ A from h)).op
    (homOfLE (show C ≤ B from h')).op).symm

theorem exists_isCocycle_cmp_eq (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type)
    (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (h1 : ∀ i, IsAffineOpen (W i))
    (h2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))
    (h3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (x : GlobalTheory.CechDR.HO1 s) :
    ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCocycle W c ∧ cmp s W hW c = x := by
  obtain ⟨z, hz⟩ := H1.mk_surjective _ (resEquiv s W hW x)
  let O1 : J → Bas W := fun i ↦ ⟨⟨W i, h1 i⟩, i, le_rfl⟩
  let O2 : J → J → Bas W := fun i i' ↦ ⟨⟨W i ⊓ W i', h2 i i'⟩, i, inf_le_left⟩
  let O3 : J → J → J → Bas W := fun i i' i'' ↦
    ⟨⟨W i ⊓ W i' ⊓ W i'', h3 i i' i''⟩, i, inf_le_left.trans inf_le_left⟩
  let c : ∀ i i' : J, Γ(Z, W i ⊓ W i') := fun i i' ↦
    cocVal s W z (O1 i) (O2 i i') inf_le_left - cocVal s W z (O1 i') (O2 i i') inf_le_right
  have key : ∀ (i i' : J) (V : Bas W) (h : V.1.1 ≤ W i ⊓ W i'),
      resG Z h (c i i') = cocVal s W z (O1 i) V (h.trans inf_le_left) -
        cocVal s W z (O1 i') V (h.trans inf_le_right) := by
    intro i i' V h
    have e1 := cocVal_comp s W z (O1 i) (O2 i i') V inf_le_left h
    have e2 := cocVal_comp s W z (O1 i') (O2 i i') V inf_le_right h
    have e : resG Z h (c i i') =
        resG Z h (cocVal s W z (O1 i) (O2 i i') inf_le_left) -
          resG Z h (cocVal s W z (O1 i') (O2 i i') inf_le_right) := map_sub _ _ _
    rw [e]
    refine (congrArg₂ (· - ·) e1 e2).trans ?_
    ring
  have hc : IsCocycle W c := by
    intro i i' i''
    have e1 := key i i' (O3 i i' i'') inf_le_left
    have e2 := key i' i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have e3 := key i i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    refine (congrArg₂ (· + ·) e1 e2).trans (Eq.trans ?_ e3.symm)
    ring
  refine ⟨c, hc, ?_⟩
  rw [cmp_of_isCocycle s W hW hc, LinearEquiv.symm_apply_eq, ← hz, H1.mk_eq_mk]
  refine ⟨fun V ↦ -cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop), ?_⟩
  funext V V' a
  have e1 := key (idx V.unop) (idx V'.unop) V'.unop
    (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
  have e2 := cocVal_comp s W z (O1 (idx V.unop)) V.unop V'.unop (le_idx V.unop) (le_of_hom a)
  have goal : -cocVal s W z (O1 (idx V'.unop)) V'.unop (le_idx V'.unop) -
      resG Z (le_of_hom a) (-cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop)) =
      resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop)) - cocVal s W z V.unop V'.unop (le_of_hom a) := by
    rw [map_neg, e1, e2]
    ring
  exact goal

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCoverStatement
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → (∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) → ∀ x : GlobalTheory.CechDR.HO1 s, ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), GlobalTheory.CechCmp.IsCocycle W c ∧ GlobalTheory.CechCmp.cmp s W hW c = x := by
  first | exact @GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | exact GlobalTheory.CechCmp.exists_isCocycle_cmp_eq | (intros; apply GlobalTheory.CechCmp.exists_isCocycle_cmp_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassPullHO1EqZeroOfPullbackCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassPullHO1EqZeroOfPullbackCoboundary
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR Opposite

namespace GlobalTheory.CechCmp

abbrev PairCov {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) : Type :=
  {p : Pair ι // ∃ i, p.1.2.1 ≤ W i}

abbrev pairCovIncl {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) :
    (PairCov W ι)ᵒᵖ ⥤ (Pair ι)ᵒᵖ :=
  (Monotone.functor (f := (Subtype.val : PairCov W ι → Pair ι)) fun _ _ h ↦ h).op

abbrev pairCovSnd {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) :
    (PairCov W ι)ᵒᵖ ⥤ (Bas W)ᵒᵖ :=
  (Monotone.functor (f := fun p : PairCov W ι ↦ (⟨p.1.1.2, p.2⟩ : Bas W))
    fun _ _ h ↦ Pair.le_snd (φ := ι) h).op

def pairCovPull {R R' : Type} [CommRing R] [CommRing R'] {Z Y : Scheme.{0}} {J : Type}
    (W : J → Z.Opens) {ι : Y ⟶ Z} {s : Z ⟶ Sp R} {s' : Y ⟶ Sp R'} {σ : R →+* R'}
    (w : ι ≫ s = s' ≫ spMap σ) :
    CoefMap σ (incl W ⋙ OAff s) (pairCovIncl W ι ⋙ OPair ι s') where
  G := pairCovSnd W ι
  α p := GlobalTheory.CechDR.secPull s s' p.unop.1
  naturality {p q} a b := (GlobalTheory.CechDR.pairPull w).naturality ((pairCovIncl W ι).map a) b
  smul p := semiHom_secPull w p.unop.1

theorem pairCov_pull1_eq {R R' : Type} [CommRing R] [CommRing R'] {Z Y : Scheme.{0}} {J : Type}
    (W : J → Z.Opens) {ι : Y ⟶ Z} {s : Z ⟶ Sp R} {s' : Y ⟶ Sp R'} {σ : R →+* R'}
    (w : ι ≫ s = s' ≫ spMap σ) (x : HO1 s) :
    (CoefMap.restrict (OPair ι s') (pairCovIncl W ι)).pull1 ((GlobalTheory.CechDR.pairPull w).pull1 x) =
      (pairCovPull W w).pull1 ((CoefMap.restrict (OAff s) (incl W)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b ↦ by rw [NatTrans.id_app, mp_id]) x

theorem pairCov_restrict_injective {R' : Type} [CommRing R'] {Z Y : Scheme.{0}} [Z.IsSeparated]
    {J : Type} (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i)) (ι : Y ⟶ Z)
    (s' : Y ⟶ Sp R') :
    Function.Injective (CoefMap.restrict (OAff s') (pairCovIncl W ι ⋙ pairFst ι)).pull1 := by
  let G : (PairCov W ι)ᵒᵖ ⥤ AffOp Y := pairCovIncl W ι ⋙ pairFst ι
  have hcov : ∀ T : AffOp Y, ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp Y) (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (PairCov W ι)ᵒᵖ) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let Gs : Set Γ(Y, T.unop.1) := {f | ∃ j, Y.basicOpen f ≤ ι ⁻¹ᵁ W j}
    have hG : Ideal.span Gs = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : ι.base x ∈ ⨆ i, W i := by rw [hW]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := ι ⁻¹ᵁ W j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) =
          (F : Set Γ(Y, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(Y, T.unop.1) := (F.equivFin.symm i).1
      have hB : IsAffineOpen (Y.basicOpen f) := hT.basicOpen f
      have hBT : Y.basicOpen f ≤ T.unop.1 := Y.basicOpen_le f
      have hSB : S.unop.1 ≤ Y.basicOpen f := by
        have h1 : Y.basicOpen (Y.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          Y.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let p : Pair ι := ⟨(⟨_, hB⟩, ⟨W j, hWa j⟩), hj⟩
      let t : PairCov W ι := ⟨p, j, le_rfl⟩
      refine ⟨op t, (homOfLE (show (⟨_, hB⟩ : Y.affineOpens) ≤ T.unop from hBT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hB⟩ : Y.affineOpens) from hSB)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : (PairCov W ι)ᵒᵖ) (S : AffOp Y), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp Y) (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop.1 ≤ S.unop.1 := leOfHom u.unop
      have hS1 : S.unop.1 ≤ t₁.unop.1.1.1.1 := leOfHom h₁.unop
      have hS2 : S.unop.1 ≤ t₂.unop.1.1.1.1 := leOfHom h₂.unop
      let A : Z.affineOpens := ⟨t₁.unop.1.1.2.1 ⊓ t₂.unop.1.1.2.1,
        IsAffineOpen.inf t₁.unop.1.1.2.2 t₂.unop.1.1.2.2⟩
      have hA : S'.unop.1 ≤ ι ⁻¹ᵁ A.1 := fun y hy ↦
        ⟨t₁.unop.1.2 (hS1 (hS'S hy)), t₂.unop.1.2 (hS2 (hS'S hy))⟩
      let p₃ : Pair ι := ⟨(S'.unop, A), hA⟩
      let t₃ : PairCov W ι := ⟨p₃, j, inf_le_left.trans hj⟩
      refine ⟨op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨𝟙 _⟩⟩
      · exact ⟨hS'S.trans hS1, (inf_le_left : A.1 ≤ t₁.unop.1.1.2.1)⟩
      · exact ⟨hS'S.trans hS2, (inf_le_right : A.1 ≤ t₂.unop.1.1.2.1)⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  exact _root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg

end GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_eq {Z Y : Scheme.{0}} (ι : Y ⟶ Z) {A V : Z.Opens} {T B : Y.Opens} (hV : V ≤ A)
    (e : T ≤ ι ⁻¹ᵁ V) (e' : B ≤ ι ⁻¹ᵁ A) (hT : T ≤ B) (x : Γ(Z, A)) :
    (ι.appLE V T e).hom (resG Z hV x) = resG Y hT ((ι.appLE A B e').hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem pullHO1_cmp_eq_zero_of_coboundary : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [Z.IsSeparated]
    (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) →
    ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ Z)
    (w : ι ≫ s = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c →
    (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')
      (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) →
    GlobalTheory.CechDR.pullHO1 w (GlobalTheory.CechCmp.cmp s W hW c) = 0 := by
  intro R _ Z _ s J W hW hWa R' _ σ Y s' ι w c hc ⟨h', hh'⟩
  set y := GlobalTheory.CechDR.pullHO1 w (cmp s W hW c)
  have e1 : (GlobalTheory.CechDR.pairPull w).pull1 (cmp s W hW c) = (pairRes ι s').pull1 y :=
    isPullO_pullHO1 w _
  apply pairCov_restrict_injective W hW hWa ι s'
  rw [map_zero]
  have e2 : (CoefMap.restrict (OAff s') (pairCovIncl W ι ⋙ pairFst ι)).pull1 y =
      (CoefMap.restrict (OPair ι s') (pairCovIncl W ι)).pull1 ((pairRes ι s').pull1 y) := by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b ↦ by rw [NatTrans.id_app, mp_id]) y
  rw [e2, ← e1, pairCov_pull1_eq, restrict_cmp s W hW hc, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  let ix : PairCov W ι → J := fun p ↦ idx (⟨p.1.1.2, p.2⟩ : Bas W)
  have hix : ∀ p : PairCov W ι, p.1.1.1.1 ≤ ι ⁻¹ᵁ W (ix p) := fun p y hy ↦
    le_idx (⟨p.1.1.2, p.2⟩ : Bas W) (p.1.2 hy)
  refine ⟨fun p ↦ -resG Y (hix p.unop) (h' (ix p.unop)), ?_⟩
  funext p q a
  have hqp : q.unop.1.1.1.1 ≤ p.unop.1.1.1.1 := Pair.le_fst (leOfHom a.unop)
  change -resG Y (hix q.unop) (h' (ix q.unop)) - resG Y hqp (-resG Y (hix p.unop) (h' (ix p.unop))) =
    (ι.appLE _ _ _).hom (resG Z _ (c (ix p.unop) (ix q.unop)))
  rw [map_neg, resG_resG']
  have hT : q.unop.1.1.1.1 ≤ ι ⁻¹ᵁ W (ix p.unop) ⊓ ι ⁻¹ᵁ W (ix q.unop) :=
    le_inf (hqp.trans (hix p.unop)) (hix q.unop)
  have hV : q.unop.1.1.2.1 ≤ W (ix p.unop) ⊓ W (ix q.unop) :=
    le_inf ((show q.unop.1.1.2.1 ≤ p.unop.1.1.2.1 from Pair.le_snd (leOfHom a.unop)).trans (le_idx (⟨p.unop.1.1.2, p.unop.2⟩ : Bas W)))
      (le_idx (⟨q.unop.1.1.2, q.unop.2⟩ : Bas W))
  have k := appLE_resG_eq ι (A := W (ix p.unop) ⊓ W (ix q.unop))
    (B := ι ⁻¹ᵁ W (ix p.unop) ⊓ ι ⁻¹ᵁ W (ix q.unop)) hV q.unop.1.2 (fun _ hx => hx) hT
    (c (ix p.unop) (ix q.unop))
  refine Eq.trans ?_ k.symm
  rw [hh', map_sub, resG_resG', resG_resG']
  ring

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassPullHO1EqZeroOfPullbackCoboundaryStatement
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [Z.IsSeparated] (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ Z) (w : ι ≫ s = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (GlobalTheory.CechCmp.cmp s W hW c) = 0 := by
  first | exact @GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary | exact GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary | (intros; apply GlobalTheory.CechCmp.pullHO1_cmp_eq_zero_of_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CechCmp

theorem IsCocycle.res_on {Z : Scheme.{0}} {J : Type} {W : J → Z.Opens}
    {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {U : Z.Opens} {i j k : J}
    (hi : U ≤ W i) (hj : U ≤ W j) (hk : U ≤ W k) :
    resG Z (le_inf hi hj) (c i j) + resG Z (le_inf hj hk) (c j k) =
      resG Z (le_inf hi hk) (c i k) := by
  have e := congrArg (resG Z (le_inf (le_inf hi hj) hk)) (hc i j k)
  simp only [map_add (f := _), resG_resG'] at e
  exact e

theorem exists_coboundary_of_cmp_eq_zero (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R)
    (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i))
    (hWb : ∀ i i', IsAffineOpen (W i ⊓ W i')) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))
    (hc : IsCocycle W c) (h0 : cmp s W hW c = 0) :
    ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i',
      c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  have h1 := restrict_cmp s W hW hc
  rw [h0, map_zero] at h1
  obtain ⟨g, hg⟩ := CatCoh.H1.mk_eq_zero.1 h1.symm
  let g' : ∀ V : Bas W, Γ(Z, V.1.1) := fun V ↦ g (Opposite.op V)
  have key : ∀ (V V' : Bas W) (h : V'.1.1 ≤ V.1.1),
      g' V' - resG Z h (g' V) =
        resG Z (le_inf (h.trans (le_idx V)) (le_idx V')) (c (idx V) (idx V')) := by
    intro V V' h
    exact congrFun (congrFun (congrFun hg (Opposite.op V)) (Opposite.op V'))
      (homOfLE (show V' ≤ V from h)).op
  let Ω : J → Bas W := fun i ↦ ⟨⟨W i, hWa i⟩, i, le_rfl⟩
  have hΩ : ∀ i, W i ≤ W (idx (Ω i)) := fun i ↦ le_idx (Ω i)
  let g₁ : ∀ i, Γ(Z, W i) := fun i ↦ g' (Ω i)
  refine ⟨fun i ↦ resG Z (le_inf le_rfl (hΩ i)) (c i (idx (Ω i))) - g₁ i, fun i i' ↦ ?_⟩
  let Ω₂ : Bas W := ⟨⟨W i ⊓ W i', hWb i i'⟩, i, inf_le_left⟩
  have hd : W i ⊓ W i' ≤ W (idx Ω₂) := le_idx Ω₂
  let g₂ : Γ(Z, W i ⊓ W i') := g' Ω₂
  have k1 : g₂ - resG Z inf_le_left (g₁ i) =
      resG Z (le_inf (inf_le_left.trans (hΩ i)) hd) (c (idx (Ω i)) (idx Ω₂)) :=
    key (Ω i) Ω₂ inf_le_left
  have k2 : g₂ - resG Z inf_le_right (g₁ i') =
      resG Z (le_inf (inf_le_right.trans (hΩ i')) hd) (c (idx (Ω i')) (idx Ω₂)) :=
    key (Ω i') Ω₂ inf_le_right
  have e1 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) (inf_le_left.trans (hΩ i)) hd
  have e2 := hc.res_on (inf_le_right : W i ⊓ W i' ≤ _) (inf_le_right.trans (hΩ i')) hd
  have e3 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right hd
  have e4 : resG Z (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right) (c i i') = c i i' := by
    have : (homOfLE (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right)).op = 𝟙 _ := rfl
    simp only [resG, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e4] at e3
  simp only [map_sub, resG_resG']
  linear_combination e3 - e1 + e2 - k1 + k2

end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZeroStatement
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) → (∀ i i', IsAffineOpen (W i ⊓ W i')) → ∀ (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c → GlobalTheory.CechCmp.cmp s W hW c = 0 → ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i', c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  first | exact @GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | exact GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero | (intros; apply GlobalTheory.CechCmp.exists_coboundary_of_cmp_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEOpensInclusionAppLEEqSecMapIsoSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEOpensInclusionAppLEEqSecMapIsoSpec
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.CechDR

theorem appLE_ι_appLE_eq_secMap : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  intro X T p U O hO V e r
  have hU : IsAffineOpen U.1 := U.2
  have key : (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ ((p ∣_ U.1) ≫ hU.isoSpec.hom).appLE ⊤ V (by simp) =
      p.appLE U.1 O hO ≫ (p ⁻¹ᵁ U.1).ι.appLE O V e := by
    change (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (Scheme.Hom.appTop ((p ∣_ U.1) ≫ hU.isoSpec.hom) ≫
      (p ⁻¹ᵁ U.1).toScheme.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change U.1.topIso.inv ≫ (p ∣_ U.1).appLE ⊤ V (show V ≤ (p ∣_ U.1) ⁻¹ᵁ ⊤ from fun _ _ => trivial) = _
    rw [morphismRestrict_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    exact (p.map_appLE _ _).trans (p.appLE_map _ _).symm
  exact (congrArg (fun f => f.hom r) key).symm

end GlobalTheory.CechDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLEOpensInclusionAppLEEqSecMapIsoSpecStatement
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec : ∀ (X T : Scheme.{0}) (p : T ⟶ X) (U : X.affineOpens) (O : T.Opens) (hO : O ≤ p ⁻¹ᵁ U.1) (V : (p ⁻¹ᵁ U.1).toScheme.Opens) (e : V ≤ (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) (r : Γ(X, U.1)), ((p ⁻¹ᵁ U.1).ι.appLE O V e).hom ((p.appLE U.1 O hO).hom r) = (GlobalTheory.CechDR.secMap ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) V).hom r := by
  first | exact @GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap | exact GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap | (intros; apply GlobalTheory.CechDR.appLE_ι_appLE_eq_secMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1Affine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_tr {A B : Scheme.{0}} (f : A ⟶ B) {O O' : B.Opens} {V V' : A.Opens} (h : O' ≤ O)
    (h' : V' ≤ V) (e : V ≤ f ⁻¹ᵁ O) (e' : V' ≤ f ⁻¹ᵁ O') (x : Γ(B, O)) :
    (f.appLE O' V' e').hom (resG B h x) = resG A h' ((f.appLE O V e).hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem ι_appLE_bijective_of_image {T : Scheme.{0}} (Vo O : T.Opens) (W : Vo.toScheme.Opens)
    (e : W ≤ Vo.ι ⁻¹ᵁ O) (hW : Vo.ι ''ᵁ W = O) : Function.Bijective (Vo.ι.appLE O W e).hom := by
  rw [Scheme.Opens.ι_appLE]
  have k : (homOfLE (Set.image_subset_iff.mpr e) : Vo.ι ''ᵁ W ⟶ O) = eqToHom hW := Subsingleton.elim _ _
  rw [k]
  exact (T.presheaf.mapIso (eqToIso hW).op).commRingCatIsoToRingEquiv.bijective

theorem exists_cech_ho1_cmp : ∀ (X T : Scheme.{0}) (p : T ⟶ X), IsSeparated p → ∀ (U : X.affineOpens) (J : Type) (W : J → T.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = p ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), ∃ Φ : (∀ i i' : J, Γ(T, W i ⊓ W i')) → GlobalTheory.CechDR.HO1 ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)), (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∀ (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ k, (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ((e k) i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ((e k) i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') ((e k) i i''))) → Φ (fun i i' => c i i' - ∑ k, (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i') = Φ c - ∑ k, r k • Φ (e k)) ∧ (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → Φ c = 0 → ∃ h : ∀ i : J, Γ(T, W i), ∀ i i', c i i' = resG T inf_le_left (h i) - resG T inf_le_right (h i')) ∧ (∀ x, ∃ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) ∧ Φ c = x) ∧ ∀ (R' : Type) [CommRing R'] (σ : Γ(X, U.1) →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ T) (ι' : Y ⟶ (p ⁻¹ᵁ U.1).toScheme), ι' ≫ (p ⁻¹ᵁ U.1).ι = ι → ∀ (w : ι' ≫ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (Φ c) = 0 := by
  intro X T p hp U J W hWa hWcov hWU
  have hsepV : (p ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    haveI : IsAffine U.1 := U.2
    constructor
    rw [← Limits.terminal.comp_from (p ∣_ U.1)]
    infer_instance
  have himg : ∀ O : T.Opens, O ≤ p ⁻¹ᵁ U.1 → (p ⁻¹ᵁ U.1).ι ''ᵁ ((p ⁻¹ᵁ U.1).ι ⁻¹ᵁ O) = O := by
    intro O hO
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hO
  let W' : J → (p ⁻¹ᵁ U.1).toScheme.Opens := fun i => (p ⁻¹ᵁ U.1).ι ⁻¹ᵁ W i
  have hW' : ⨆ i, W' i = ⊤ := by
    simp only [W', ← Scheme.Hom.preimage_iSup, hWcov, Scheme.Opens.ι_preimage_self]
  have hWa' : ∀ i, IsAffineOpen (W' i) := fun i => by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (p ⁻¹ᵁ U.1).ι, himg _ (hWU i)]
    exact hWa i
  let τ : ∀ i i', Γ(T, W i ⊓ W i') →+* Γ((p ⁻¹ᵁ U.1).toScheme, W' i ⊓ W' i') := fun i i' =>
    ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom
  have hcoc : ∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) →
      IsCocycle W' (fun i i' => τ i i' (c i i')) := by
    intro c hc i i' i''
    have e := congrArg ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)).hom (hc i i' i'')
    rw [map_add (f := _), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
      appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)] at e
    exact e
  have hb2 : ∀ i i', Function.Bijective (τ i i') := fun i i' =>
    ι_appLE_bijective_of_image _ _ _ _ (himg _ (inf_le_left.trans (hWU i)))
  refine ⟨fun c => cmp ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) W' hW'
    (fun i i' => τ i i' (c i i')), ?_, ?_, ?_, ?_⟩
  · intro c hc N r e he
    have h1 := GlobalTheory.T.cechClassMap_sub_sum_const_linear Γ(X, U.1) _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW'
      (fun i i' => τ i i' (c i i')) (hcoc c hc) N r (fun k i i' => τ i i' (e k i i')) (fun k => hcoc _ (he k))
    refine Eq.trans ?_ h1
    dsimp only
    congr 1
    funext i i'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact GlobalTheory.T.appLE_opensInclusion_appLE_eq_secMap_isoSpec X T p U (W i ⊓ W i') _ (W' i ⊓ W' i') (fun _ hx => hx) (r k)
  · intro c hc h0
    haveI := hsepV
    obtain ⟨h'', hh⟩ := GlobalTheory.T.cechCocycle_isCoboundary_of_class_eq_zero _ _ _ _ W' hW' hWa' (fun i i' => (hWa' i).inf (hWa' i')) _ (hcoc c hc) h0
    choose h hh1 using fun i => (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i) (W' i) le_rfl (himg _ (hWU i))).2 (h'' i)
    refine ⟨h, fun i i' => (hb2 i i').1 ?_⟩
    change ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (c i i') = ((p ⁻¹ᵁ U.1).ι.appLE (W i ⊓ W i') (W' i ⊓ W' i') (fun _ hx => hx)).hom (resG T inf_le_left (h i) - resG T inf_le_right (h i'))
    rw [map_sub, appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i) (O' := W i ⊓ W i') (V := W' i) (V' := W' i ⊓ W' i') inf_le_left inf_le_left le_rfl (fun _ hx => hx), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i') (O' := W i ⊓ W i') (V := W' i') (V' := W' i ⊓ W' i') inf_le_right inf_le_right le_rfl (fun _ hx => hx), hh1, hh1]
    exact hh i i'
  · intro x
    haveI := hsepV
    obtain ⟨c', hc', hx⟩ := GlobalTheory.T.cech_h1_class_eq_of_cocycle_affine_cover _ _ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) _ W' hW' hWa'
      (fun i i' => (hWa' i).inf (hWa' i')) (fun i i' i'' => ((hWa' i).inf (hWa' i')).inf (hWa' i'')) x
    choose c hc using fun i i' => (hb2 i i').2 (c' i i')
    refine ⟨c, ?_, ?_⟩
    · intro i i' i''
      apply (ι_appLE_bijective_of_image (p ⁻¹ᵁ U.1) (W i ⊓ W i' ⊓ W i'') (W' i ⊓ W' i' ⊓ W' i'') (fun _ hx => hx)
        (himg _ (inf_le_left.trans (inf_le_left.trans (hWU i))))).1
      rw [map_add (f := _), appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i') (V' := W' i ⊓ W' i' ⊓ W' i'') inf_le_left inf_le_left (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i' ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i' ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (fun _ hx => hx) (fun _ hx => hx),
        appLE_resG_tr (f := (p ⁻¹ᵁ U.1).ι) (O := W i ⊓ W i'') (O' := W i ⊓ W i' ⊓ W i'') (V := W' i ⊓ W' i'') (V' := W' i ⊓ W' i' ⊓ W' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (fun _ hx => hx) (fun _ hx => hx)]
      have e1 := hc i i'
      have e2 := hc i' i''
      have e3 := hc i i''
      simp only [τ] at e1 e2 e3
      rw [e1, e2, e3]
      exact hc' i i' i''
    · have e : (fun i i' => τ i i' (c i i')) = c' := funext fun i => funext fun i' => hc i i'
      change cmp _ W' hW' (fun i i' => τ i i' (c i i')) = x
      rw [e]
      exact hx
  · intro R' _ σ Y s' ι ι' hι w c hc hcob
    obtain ⟨h', hh'⟩ := hcob
    subst hι
    haveI := hsepV
    refine GlobalTheory.T.cechClass_pullHO1_eq_zero_of_pullback_coboundary _ _ _ _ W' hW' hWa' R' σ Y s' ι' w _ (hcoc c hc) ⟨h', fun i i' => ?_⟩
    refine Eq.trans ?_ (hh' i i')
    rw [← Scheme.Hom.appLE_comp_appLE ι' (p ⁻¹ᵁ U.1).ι _ (W' i ⊓ W' i')]
    all_goals rfl
end GlobalTheory.CechCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechComparisonStructureH1AffineStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_comparison_structure_h1_affine : ∀ (X T : Scheme.{0}) (p : T ⟶ X), IsSeparated p → ∀ (U : X.affineOpens) (J : Type) (W : J → T.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = p ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), ∃ Φ : (∀ i i' : J, Γ(T, W i ⊓ W i')) → GlobalTheory.CechDR.HO1 ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)), (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∀ (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ k, (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') ((e k) i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') ((e k) i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') ((e k) i i''))) → Φ (fun i i' => c i i' - ∑ k, (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i') = Φ c - ∑ k, r k • Φ (e k)) ∧ (∀ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → Φ c = 0 → ∃ h : ∀ i : J, Γ(T, W i), ∀ i i', c i i' = resG T inf_le_left (h i) - resG T inf_le_right (h i')) ∧ (∀ x, ∃ c : ∀ i i' : J, Γ(T, W i ⊓ W i'), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) ∧ Φ c = x) ∧ ∀ (R' : Type) [CommRing R'] (σ : Γ(X, U.1) →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ T) (ι' : Y ⟶ (p ⁻¹ᵁ U.1).toScheme), ι' ≫ (p ⁻¹ᵁ U.1).ι = ι → ∀ (w : ι' ≫ ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(T, W i ⊓ W i')), (∀ i i' i'', resG T (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG T (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG T (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) → GlobalTheory.CechDR.pullHO1 w (Φ c) = 0 := by
  first | exact @GlobalTheory.CechCmp.exists_cech_ho1_cmp | exact GlobalTheory.CechCmp.exists_cech_ho1_cmp | (intros; apply GlobalTheory.CechCmp.exists_cech_ho1_cmp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibre
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.AbCohFibre

theorem mem_smul_top_of_tmul_tmul_eq_zero {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] (m : Ideal R)
    [Algebra S (R ⧸ m)] [IsScalarTower R S (R ⧸ m)] [AddCommGroup M] [Module R M] (x : M)
    (hx : ((1 : R ⧸ m) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x) : (R ⧸ m) ⊗[S] (S ⊗[R] M)) = 0) :
    x ∈ m • (⊤ : Submodule R M) := by
  have h1 := congrArg (AlgebraTensorModule.cancelBaseChange R S (R ⧸ m) (R ⧸ m) M) hx
  rw [AlgebraTensorModule.cancelBaseChange_tmul, one_smul, map_zero] at h1
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M m) h1
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

theorem mem_smul_top_of_pull_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (m : Ideal R), m.IsMaximal → ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp (R ⧸ m)) (φ : Y ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ m)))) (x : GlobalTheory.CechDR.HO1 A.hom), GlobalTheory.CechDR.pullHO1 h.w x = 0 → x ∈ m • (⊤ : Submodule R (GlobalTheory.CechDR.HO1 A.hom)) := by
  intro R _ A _ hA m hm Y s' φ h x hx
  haveI : m.IsMaximal := hm
  haveI : m.IsPrime := hm.isPrime
  let f := spMap (algebraMap R (Localization.AtPrime m))
  letI : GrpObj ((Over.pullback f).obj A) := Functor.grpObjObj
  have hAm : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA f
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (Localization.AtPrime m) ((Over.pullback f).obj A) hAm
  have hsq0 : IsPullback (pullback.fst A.hom f) ((Over.pullback f).obj A).hom A.hom f :=
    IsPullback.of_hasPullback A.hom f
  have := hA.proper
  obtain ⟨⟨e₁, he₁⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (Localization.AtPrime m) A.left _ A.hom _ _ hsq0
    inferInstance inferInstance
  obtain ⟨-, -, hbc, -⟩ := GlobalTheory.AbCoh.oStr (Localization.AtPrime m) ((Over.pullback f).obj A) g hAm hg
  let ψ : Localization.AtPrime m →+* R ⧸ m :=
    IsLocalization.lift (M := m.primeCompl) (g := Ideal.Quotient.mk m) (fun y : m.primeCompl => by
      show IsUnit (Ideal.Quotient.mk m (y : R))
      have hy : Ideal.Quotient.mk m (y : R) ≠ 0 := by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact y.2
      letI := Ideal.Quotient.field m
      exact isUnit_iff_ne_zero.mpr hy)
  letI : Algebra (Localization.AtPrime m) (R ⧸ m) := ψ.toAlgebra
  have hcomp : (algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m)) =
      algebraMap R (R ⧸ m) := IsLocalization.lift_comp _
  haveI : IsScalarTower R (Localization.AtPrime m) (R ⧸ m) := IsScalarTower.of_algebraMap_eq'  hcomp.symm
  have hsp : spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f = spMap (algebraMap R (R ⧸ m)) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let φ' : Y ⟶ ((Over.pullback f).obj A).left :=
    pullback.lift φ (s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) (by
      rw [h.w, Category.assoc, hsp])
  have hφ' : φ' ≫ pullback.fst A.hom f = φ := pullback.lift_fst _ _ _
  have hs' : φ' ≫ ((Over.pullback f).obj A).hom = s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) :=
    pullback.lift_snd _ _ _
  have hbig : IsPullback (φ' ≫ pullback.fst A.hom f) s' A.hom
      (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f) := by
    rw [hφ', hsp]; exact h
  have hsq : IsPullback φ' s' ((Over.pullback f).obj A).hom (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) :=
    IsPullback.of_right hbig hs' hsq0
  obtain ⟨e₂, he₂⟩ := hbc (R ⧸ m) Y s' φ' hsq
  have cong : ∀ (φ₁ : Y ⟶ A.left) (σ₁ : R →+* R ⧸ m) (h₁ : φ₁ ≫ A.hom = s' ≫ spMap σ₁), φ₁ = φ →
      σ₁ = algebraMap R (R ⧸ m) → GlobalTheory.CechDR.pullHO1 h₁ x = GlobalTheory.CechDR.pullHO1 h.w x := by
    rintro _ _ _ rfl rfl; rfl
  have h'' : (φ' ≫ pullback.fst A.hom f) ≫ A.hom =
      s' ≫ spMap ((algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m))) := by
    rw [hφ', hcomp]; exact h.w
  have key : GlobalTheory.CechDR.pullHO1 hsq.w (GlobalTheory.CechDR.pullHO1 hsq0.w x) = 0 := by
    rw [GlobalTheory.CechDR.pullHO1_comp hsq0.w hsq.w h'', cong _ _ h'' hφ' hcomp]
    exact hx
  have k1 : ((1 : R ⧸ m) ⊗ₜ[Localization.AtPrime m] (GlobalTheory.CechDR.pullHO1 hsq0.w x)) = 0 := by
    apply e₂.injective
    rw [he₂, map_zero]; exact key
  have k2 := congrArg (LinearMap.lTensor (R ⧸ m) e₁.symm.toLinearMap) k1
  rw [LinearMap.lTensor_tmul, map_zero, ← he₁, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at k2
  exact mem_smul_top_of_tmul_tmul_eq_zero m x k2

end GlobalTheory.AbCohFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_h1_nakayama_closed_fibre : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (m : Ideal R), m.IsMaximal → ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp (R ⧸ m)) (φ : Y ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ m)))) (x : GlobalTheory.CechDR.HO1 A.hom), GlobalTheory.CechDR.pullHO1 h.w x = 0 → x ∈ m • (⊤ : Submodule R (GlobalTheory.CechDR.HO1 A.hom)) := by
  first | exact @GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero | exact GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero | (intros; apply GlobalTheory.AbCohFibre.mem_smul_top_of_pull_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleMemCoboundaryAddMaximalSmul
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CechBCInj

theorem grp_of_isPullback {X S' P : Scheme.{0}} (G : Over X) [GrpObj G] (hG : IsAbelianScheme G) (f : S' ⟶ X)
    (fst : P ⟶ G.left) (snd : P ⟶ S') (h : IsPullback fst snd G.hom f) :
    ∃ _ : GrpObj (Over.mk snd), IsAbelianScheme (Over.mk snd) := by
  letI : GrpObj ((Over.pullback f).obj G) := Functor.grpObjObj
  have hP := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hG f
  let e : Over.mk snd ≅ (Over.pullback f).obj G := Over.isoMk h.isoPullback (by simp)
  letI gr : GrpObj (Over.mk snd) := GrpObj.ofIso e.symm
  refine ⟨gr, GlobalTheory.Compare.AbelianSchemeTorusCompare.isAbelianScheme_of_iso e ?_ hP⟩
  haveI : IsMonHom e.symm.hom := inferInstance
  exact isMonHom_inv_of_iso e.symm

theorem restrict_isPullback {X T : Scheme.{0}} (p : T ⟶ X) (U : X.affineOpens) :
    IsPullback (p ⁻¹ᵁ U.1).ι ((p ∣_ U.1) ≫ U.2.isoSpec.hom : (p ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) p (chart U) := by
  have h1 := (isPullback_morphismRestrict p U.1).flip
  have h2 : IsPullback U.1.ι U.2.isoSpec.hom (𝟙 X) (U.2.isoSpec.inv ≫ U.1.ι) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have h3 := h1.paste_vert h2
  rw [Category.comp_id] at h3
  have e : chart U = U.2.isoSpec.inv ≫ U.1.ι := (IsAffineOpen.isoSpec_inv_ι U.2).symm
  rw [e]
  exact h3

theorem resG_appLE' {X T : Scheme.{0}} (p : T ⟶ X) (U : X.affineOpens) {O O' : T.Opens} (hO : O ≤ p ⁻¹ᵁ U.1)
    (h : O' ≤ O) (r : Γ(X, U.1)) :
    resG T h ((p.appLE U.1 O hO).hom r) = (p.appLE U.1 O' (h.trans hO)).hom r := by
  show ((p.appLE U.1 O hO) ≫ T.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]

theorem exists_fin_sum {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (x : M)
    (hx : x ∈ I • (⊤ : Submodule R M)) :
    ∃ (N : ℕ) (r : Fin N → R) (y : Fin N → M), (∀ k, r k ∈ I) ∧ x = ∑ k, r k • y k := by
  have key : ∃ l : List (R × M), (∀ p ∈ l, p.1 ∈ I) ∧ x = (l.map fun p => p.1 • p.2).sum := by
    refine Submodule.smul_induction_on hx (fun r hr n _ => ⟨[(r, n)], by simpa using hr, by simp⟩) ?_
    rintro a b ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
    refine ⟨l₁ ++ l₂, fun p hp => ?_, by simp⟩
    rcases List.mem_append.1 hp with h | h
    exacts [h₁ p h, h₂ p h]
  obtain ⟨l, hl, rfl⟩ := key
  refine ⟨l.length, fun k => l[k].1, fun k => l[k].2, fun k => hl _ (List.getElem_mem _), ?_⟩
  exact (Fin.sum_univ_fun_getElem l (fun p => p.1 • p.2)).symm

theorem cocycle_mem_coboundary_add_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) (ι : A.left ⟶ t.G.left), IsPullback ι A.hom t.G.hom (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∃ (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  intro E _ _ _ H X t hP U J W hWa hcov hWU m hm A ι hpb c hc hcob
  have sq := restrict_isPullback t.G.hom U
  obtain ⟨inst, hAb⟩ := grp_of_isPullback t.G
    (GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hP) (chart U) _ _ sq
  have hsq : ι ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hpb.w, Category.assoc]
  let ι' := sq.lift ι (A.hom ≫ spMap (Ideal.Quotient.mk m)) hsq
  have hι' : ι' ≫ (t.G.hom ⁻¹ᵁ U.1).ι = ι := sq.lift_fst _ _ _
  have hw : ι' ≫ ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom : (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1)) =
      A.hom ≫ spMap (Ideal.Quotient.mk m) := sq.lift_snd _ _ _
  have hpb' : IsPullback ι' A.hom (Over.mk ((t.G.hom ∣_ U.1) ≫ U.2.isoSpec.hom :
      (t.G.hom ⁻¹ᵁ U.1).toScheme ⟶ Sp Γ(X, U.1))).hom (spMap (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m))) :=
    IsPullback.of_right (by rw [hι']; exact hpb) hw sq
  obtain ⟨Φ, hlin, hinj, hsurj, hnat⟩ := GlobalTheory.T.cech_comparison_structure_h1_affine X t.G.left t.G.hom t.semi.separated U J W hWa hcov hWU
  have h0 := hnat _ (algebraMap Γ(X, U.1) (Γ(X, U.1) ⧸ m)) A.left A.hom ι ι' hι' hpb'.w c hc hcob
  have hmem := GlobalTheory.T.structure_h1_nakayama_closed_fibre _ _ hAb m hm A.left A.hom ι' hpb' (Φ c) h0
  obtain ⟨N, r, y, hr, hy⟩ := exists_fin_sum m _ hmem
  choose e he hΦe using hsurj
  let ρ : ∀ i i' : J, Γ(X, U.1) →+* Γ(t.G.left, W i ⊓ W i') := fun i i' =>
    (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom
  let c' : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i') := fun i i' => c i i' - ∑ k, ρ i i' (r k) * e (y k) i i'
  have hc' : (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c' i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c' i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c' i i'')) := by
    intro i i' i''
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [c', ρ, map_sub, map_sum, map_mul, resG_appLE']
    rw [← hc i i' i'']
    have := fun k => he (y k) i i' i''
    simp only [← this, mul_add, Finset.sum_add_distrib]
    ring
  have hΦ : Φ c' = 0 := by
    rw [hlin c hc N r (fun k => e (y k)) (fun k => he (y k))]
    simp only [hΦe, ← hy, sub_self]
  obtain ⟨h, hh⟩ := hinj c' hc' hΦ
  refine ⟨h, N, r, fun k => e (y k), hr, fun k => he (y k), fun i i' => ?_⟩
  have := hh i i'
  simp only [c'] at this
  rw [sub_eq_iff_eq_add] at this
  exact this

end GlobalTheory.CechBCInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleMemCoboundaryAddMaximalSmulStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_mem_coboundary_add_maximal_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) (ι : A.left ⟶ t.G.left), IsPullback ι A.hom t.G.hom (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∃ (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  first | exact @GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul | exact GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul | (intros; apply GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesMod
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem GlobalTheory.CechFibre.resG_appLE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) (U : X.affineOpens) {O O' : t.G.left.Opens} (hO : O ≤ t.G.hom ⁻¹ᵁ U.1) (h : O' ≤ O)
    (r : Γ(X, U.1)) :
    resG t.G.left h ((t.G.hom.appLE U.1 O hO).hom r) = (t.G.hom.appLE U.1 O' (h.trans hO)).hom r := by
  show ((t.G.hom.appLE U.1 O hO) ≫ t.G.left.presheaf.map (homOfLE h).op).hom r = _
  rw [Scheme.Hom.appLE_map]


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  classical
  intro E _ _ _ H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj m hm c hc
  let x0 : Sp (Γ(X, U.1) ⧸ m) ⟶ X := spMap (Ideal.Quotient.mk m) ≫ chart U
  letI : GrpObj ((Over.pullback x0).obj t.G) := Functor.grpObjObj
  have hpb := isGrpPullback_pullback t.G x0
  obtain ⟨θ, h', hθ⟩ := GlobalTheory.T.closedFibre_cechCocycle_in_tangentSpan E H X t hP hA hK U n v hv hb δ hδ hδU hδv J W j hWa hcov hWU hj m hm
    ((Over.pullback x0).obj t.G) (pullback.fst t.G.hom x0) hpb c hc
  let κ : Fin n → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i') := fun b i i' =>
    δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) *
      resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val
  have hκ : ∀ b i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (κ b i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (κ b i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (κ b i i'') :=
    fun b i i' i'' => GlobalTheory.T.cech_cocycle_condition_log_derivative_transition t.G.left t.PP.L t.PP.isLB _ (δ b) (hδ b) J W j hWU hj i i' i''
  let c₀ : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i') := fun i i' =>
    c i i' - ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * κ b i i'
  have hc₀ : ∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c₀ i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c₀ i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c₀ i i'') := by
    intro i i' i''
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [c₀, map_sub, map_sum, map_mul, GlobalTheory.CechFibre.resG_appLE]
    rw [← hc i i' i'']
    have e : ∀ b, resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (κ b i i'') = _ := fun b => (hκ b i i' i'').symm
    simp only [e, mul_add, Finset.sum_add_distrib]
    ring
  obtain ⟨h, N, r, e, hr, he, hce⟩ := GlobalTheory.T.cechCocycle_mem_coboundary_add_maximal_smul E H X t hP U J W hWa hcov hWU m hm
    ((Over.pullback x0).obj t.G) (pullback.fst t.G.hom x0) hpb.1 c₀ hc₀ ⟨h', hθ⟩
  refine ⟨θ, h, N, r, e, hr, he, fun i i' => ?_⟩
  have := hce i i'
  simp only [c₀] at this
  linear_combination this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleEqCoboundaryAddLogDerivativesModStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_eq_coboundary_add_logDerivatives_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (θ : Fin n → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (θ b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val) + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  first | exact @GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod | exact GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod | (intros; apply GlobalTheory.CechFibre.exists_dlog_add_coboundary_mod <;> assumption)
end
