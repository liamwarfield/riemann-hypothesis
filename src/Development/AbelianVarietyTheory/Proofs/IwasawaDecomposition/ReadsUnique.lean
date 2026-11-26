module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Lean
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
noncomputable section

namespace GlobalTheory.Mem.SRe.StdUnique

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem pt_of_deco {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q Q' : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q' = ∅)
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} {p' : DecoF E n ST SG Q'} (e : p'.deco = p.deco)
    (h : IsPtOf hc g p) : IsPtOf hc g p' :=
  ⟨h.uni, e ▸ h.lat, e ▸ h.f, e ▸ h.be, fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩

variable {B : Base} {X : PreX B.toPre} (I : TC B X)


set_option maxHeartbeats 2000000 in
theorem reads_mem (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k k' : Unit → GA B (B.R.N i)}
    (hR : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y st' k')
    (x : U) (hx : x.1 ∈ UAd B.sp.cm (B.R.N i)) : ∃ h : x.1 ∈ U', chi' ⟨x.1, h⟩ = chi x := by
  obtain ⟨c, -⟩ := hR.onto ()
  obtain ⟨p0, hp0, -⟩ := hR.k_std ()
  have hk : k () ∈ UAd B.sp.cm (B.R.N i) := hp0.uni
  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  have h1 : PtOf (y c * k ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR.pt c)
  have h2 : PtOf (y c * k' ()) ((I.stp u I.mu0 i).rep c).1.1 := pt_of_deco hQ (extTo_deco _ _).symm (hR'.pt c)
  have hyk : y c * k () ∈ UAd B.sp.cm (B.R.N i) := h1.uni
  have hg : y c * x.1 * k () ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x.1 * k () = (y c * k ()) * ((k ())⁻¹ * x.1 * k ()) := by group
    rw [e]
    exact mul_mem hyk (mul_mem (mul_mem (inv_mem hk) hx) hk)
  obtain ⟨q, hq⟩ := ChiFinTop.exists_isPtOf_of_mem (ST := (B.primes X).vT u) (SG := (B.primes X).vGs)
    (Q := QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) B.sp.cm hQ hg
  have hq' : PtOf (y c * x.1 * k' ()) q := by
    have e : y c * x.1 * k' () = y c * x.1 * k () * ((y c * k ())⁻¹ * (y c * k' ())) := by group
    rw [e]
    exact PtStab.isPtOf_mul_stab _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hq
  obtain ⟨κ, hgam, hκq, hcos⟩ := (hR.lev c x.1 q hq).1 x.2
  have hm : x.1 ∈ U' := (hR'.lev c x.1 q hq').2 ⟨κ, hgam, hκq, hcos⟩
  refine ⟨hm, Units.ext ?_⟩
  exact (hR'.chr c ⟨x.1, hm⟩ κ hgam (by rw [hκq]; exact hq')).trans (hR.chr c x κ hgam (by rw [hκq]; exact hq)).symm


set_option maxHeartbeats 2000000 in
theorem reads_unique (u : B.Word) (i : ℕ) {Lb Lb' : Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U U' : Subgroup (GA B (B.R.N i))} {chi : U →* ℂˣ} {chi' : U' →* ℂˣ} {y y' : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)}
    {st st' : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    (hR : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k)
    (hR' : ∃ k, I.Reads u I.mu0 i (fun _ => ()) (fun _ => Lb') (fun _ => U') (fun _ => chi') y' st' k) (hy : y' = y)
    (hU : U ≤ UAd B.sp.cm (B.R.N i)) (hU' : U' ≤ UAd B.sp.cm (B.R.N i)) : Lb' = Lb ∧ U' = U ∧ HEq chi' chi := by
  obtain ⟨k, hR⟩ := hR
  obtain ⟨k', hR'⟩ := hR'
  subst hy
  have e : U' = U := le_antisymm (fun x hx => (reads_mem I u i hR' hR ⟨x, hx⟩ (hU' hx)).1)
    fun x hx => (reads_mem I u i hR hR' ⟨x, hx⟩ (hU hx)).1
  subst e
  refine ⟨Submodule.ext fun x => (hR'.lb () x).trans (hR.lb () x).symm, rfl, heq_of_eq (MonoidHom.ext fun x => ?_)⟩
  exact (reads_mem I u i hR hR' x (hU x.2)).2

variable (l : I.Laws)


set_option maxHeartbeats 2000000 in
theorem lev_le (hI : I.Ok) (hP : TC.Pins B X) (Z : TC.Later B (I.cols l)) (u : B.Word) (i : ℕ) (hi : i ≤ B.R.m)
    (K : ClsTied (D := I.rec7 l Z) u i hi) : (show Subgroup (GA B (B.R.N i)) from K.lev.U) ≤ UAd B.sp.cm (B.R.N i) := by
  have hg1 : gramN (I.rec7 l Z) i hi = 1 := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have eU : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      UAd B.sp.cm (B.R.N i) := by rw [hg1]; rfl
  exact fun x hx => eU ▸ ((K.lev.U_eq x).1 hx).1


set_option maxHeartbeats 4000000 in
theorem std_pair (hI : I.Ok) (hP : TC.Pins B X) (Z Z' : TC.Later B (I.cols l)) (u : B.Word) {Ch Ch' : ℕ → Type}
    {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} {chOf' : ∀ i, ((I.rec7 l Z').mem u).C.cls i → Ch' i}
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (F' : FormsTiedSym (I.rec7 l Z') u Ch' chOf')
    (hF : I.StdF l Z u F) (hF' : I.StdF l Z' u F') :
    F'.to0.cls0.lev.Lb = F.to0.cls0.lev.Lb ∧ F'.to0.cls0.lev.U = F.to0.cls0.lev.U ∧ HEq F'.to0.cls0.lev.chi F.to0.cls0.lev.chi ∧
      F'.to0.cls0.y = F.to0.cls0.y ∧ F'.to0.val0.eY = F.to0.val0.eY := by
  have hy : ∀ c : (I.stp u I.mu0 0).Cl, (F'.to0.cls0.y c).1 = (F.to0.cls0.y c).1 := fun c =>
    (hF'.yE 0 (Nat.zero_le _) (Or.inl rfl) c).trans (hF.yE 0 (Nat.zero_le _) (Or.inl rfl) c).symm
  have h := reads_unique I u 0 (hF.ends 0 (Nat.zero_le _) (Or.inl rfl)) (hF'.ends 0 (Nat.zero_le _) (Or.inl rfl)) (funext hy)
    (lev_le I l hI hP Z u 0 _ _) (lev_le I l hI hP Z' u 0 _ _)
  refine ⟨h.1, h.2.1, h.2.2, funext fun c => Subtype.ext (hy c), Equiv.ext fun z => Subtype.ext ?_⟩
  exact (hF'.eY 0 (Nat.zero_le _) (Or.inl rfl) z).trans (hF.eY 0 (Nat.zero_le _) (Or.inl rfl) z).symm


set_option maxHeartbeats 4000000 in
theorem car_of_same {D : D7} {u : D.what₂.Word} {F₁ F' : Forms0 D u}
    {lev : StepLevel D.host.F D.host.E (sigD D) (gramN D 0 (Nat.zero_le _)) (D.mem u).A.T D.R.f (badG D)}
    {y : (D.mem u).C.cls 0 → UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {eY : (D.mem u).C.Y 0 ≃ Formalism.L2.Forms.Fr D 0 (Nat.zero_le _)}
    (h : F₁.cls0.lev = lev ∧ F₁.cls0.y = y ∧ F₁.val0.eY = eY)
    (h' : F'.cls0.lev.Lb = lev.Lb ∧ F'.cls0.lev.U = lev.U ∧ HEq F'.cls0.lev.chi lev.chi ∧ F'.cls0.y = y ∧ F'.val0.eY = eY) :
    F'.cls0.lev.Lb = F₁.cls0.lev.Lb ∧ F'.cls0.lev.U = F₁.cls0.lev.U ∧ HEq F'.cls0.lev.chi F₁.cls0.lev.chi ∧
      F'.cls0.y = F₁.cls0.y ∧ F'.val0.eY = F₁.val0.eY := by
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact h'


set_option maxHeartbeats 4000000 in
theorem sameStd : SameStd := by
  intro B f T w Z Zn col col' F₁ h u
  have h1 := std_pair w.I w.l w.ok w.pins Z (reL Z Zn) u (col.C.forms u) (col'.C.forms u) (col.std u) (col'.std u)
  exact car_of_same (F₁ := F₁ u) (F' := (col'.C.forms u).to0) (lev := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.lev :)))
    (y := (by with_unfolding_all exact ((col.C.forms u).to0.cls0.y :))) (eY := (by with_unfolding_all exact ((col.C.forms u).to0.val0.eY :))) ((by with_unfolding_all exact ((h u) :))) ((by with_unfolding_all exact (h1 :)))

end GlobalTheory.Mem.SRe.StdUnique

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.LieMet
  GlobalTheory.LocM
open GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_self)
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.TanPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
  (h' : IsGrpPullback G' t.G x φ)

theorem toUnit_specO_left : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
  rw [Over.toUnit_left]
  exact Spec.map_id _

include h'

theorem exists_lieG {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ p : LieG G', p.1.left ≫ φ = v := by
  let p : specO R (DualNumber R) ⟶ G' :=
    Over.homMk (h'.1.lift v (specO R (DualNumber R)).hom hv.1) (h'.1.lift_snd _ _ _)
  have hp : p.left ≫ φ = v := h'.1.lift_fst _ _ _
  refine ⟨⟨p, Over.OverMorphism.ext (h'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hp⟩
  rw [Over.comp_left, Over.comp_left, toUnit_specO_left, Category.assoc, hp, Category.assoc]
  exact (epsZero_comp_of_isTanAtG t hv).trans ((unitSec_comp h').symm.trans (Category.id_comp _).symm)

theorem isTanAtG_lieG (p : LieG G') : IsTanAtG t x (p.1.left ≫ φ) := by
  constructor
  · rw [Category.assoc, h'.1.w, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w p.1)
  · rw [← Category.assoc, Hom.one_def, Over.comp_left, Over.toUnit_left]
    exact (congrArg (· ≫ φ) (sec_epsZero_comp p)).trans (unitSec_comp h')

theorem tanForm_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v) :
    tanForm t hv = omegaBase h' ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso R).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso R).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ unitSec G' ⁻¹ᵁ φ ⁻¹ᵁ W :=
    (le_preimage_of_comp (unitSec_comp h')).2 le_rfl
  have k₂ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ sec (epsZero R) ⁻¹ᵁ v ⁻¹ᵁ W :=
    (le_preimage_of_comp (epsZero_comp_of_isTanAtG t hv)).2 le_rfl
  have k₃ : v ⁻¹ᵁ W ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W := (le_preimage_of_comp hp).2 le_rfl
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero R)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl k₂
    le_rfl a).trans ?_
  refine Eq.symm ((congrArg ((cotMap p.1 (epsZero_comp p)).app _)
    (omegaBase_dUnit h' le_rfl le_rfl k₁ le_rfl a)).trans ?_)
  exact (cotMap_d p.1 (epsZero_comp p) k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE hp _ _ _ a))

theorem tanEv_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v)
    {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(omega t.G, V)) :
    tanEv t hv h s = (Scheme.ΓSpecIso (.of R)).hom
      (dualApp (tangent p) le_top ((omegaBase h').app ⊤ (pullbackSections x (omega t.G) h s))) := by
  rw [tanEv, tanForm_eq h' p hv hp]
  rfl

theorem exists_equiv_of_isGrpPullback {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} {s : Fin n → Γ(omega t.G, V)}
    (hs : VB.IsFrame s) : ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) := by
  have := t.semi
  have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback h'.1 inferInstance
  let e : Fin n → Γ(omega G', ⊤) := fun b => (omegaBase h').app ⊤ (pullbackSections x (omega t.G) h (s b))
  have he : VB.IsFrame e := by
    have h₁ := ((hs.pullback x).res h).map_iso (omegaBase h')
    have h₂ (b : Fin n) : resM _ h (pullbackSections x (omega t.G) le_rfl (s b)) =
        pullbackSections x (omega t.G) h (s b) := QCoh.res_pullbackSections x _ _ _ _
    simpa only [h₂] using h₁
  have hc := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom
  let Φ : TanM x t.G →ₗ[R] (Fin n → R) :=
    { toFun := fun v b => tanEv t (isTan_tv v) h (s b)
      map_add' := fun v w => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
        have hpq : (p.1 * q.1).left ≫ φ = (tv (v + w)).left :=
          (h'.2 _ p.1 q.1 (tv v) (tv w) hp.symm hq.symm).symm
        rw [Pi.add_apply, tanEv_eq h' p _ hp, tanEv_eq h' q _ hq,
          tanEv_eq h' ⟨_, OmegaGlobal.fst_mul p q⟩ _ hpq, tangent_mul, dualApp_add, LinearMap.add_apply, map_add]
      map_smul' := fun a v => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        have ha : (dualScale a).toRingHom = epsScaleR a := by
          ext y <;> simp [dualScale, epsScaleR]
        have hpq : (ptMap (dualScale a) ≫ p.1).left ≫ φ = (tv (a • v)).left := by
          rw [Over.comp_left, Category.assoc, hp]
          exact congrArg (fun r => spMap r ≫ (tv v).left) ha
        rw [Pi.smul_apply, tanEv_eq h' p _ hp, tanEv_eq h' ⟨_, OmegaGlobal.fst_scale a p⟩ _ hpq, tangent_scale]
        simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LB.resG_self,
          Iso.inv_hom_id_apply, RingHom.id_apply] }
  refine ⟨LinearEquiv.ofBijective Φ ⟨fun v w hvw => ?_, fun c => ?_⟩, fun _ _ => rfl⟩
  · obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
    obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
    obtain rfl : p = q := tangent_injective R G' (he.dual_ext le_rfl fun b => by
      rw [resM_self]
      exact hc.1 ((tanEv_eq h' p _ hp h (s b)).symm.trans
        ((congrFun hvw b).trans (tanEv_eq h' q _ hq h (s b)))))
    exact tan_ext (hp.symm.trans hq)
  · classical
    let coord (i : Fin n) : Γ(VB.dual (omega G'), ⊤) :=
      VB.homMk (fun _ h => (he.basis h).coord i) fun _ _ h h' s => he.repr_resM h h' s i
    have hcoord (i j : Fin n) : dualApp (coord i) le_rfl (e j) = if j = i then 1 else 0 := by
      change (he.basis le_rfl).repr (e j) i = _
      rw [← resM_self (F := omega G') (h := le_rfl) (e j), ← he.basis_apply le_rfl j,
        Module.Basis.repr_self, Finsupp.single_apply]
    let l : Γ(VB.dual (omega G'), ⊤) := ∑ i, cst R (c i) • coord i
    obtain ⟨p, hp⟩ := TangentSurj.tangent_surjective R G' l
    refine ⟨tanOf (isTanAtG_lieG h' p), funext fun b => (tanEv_eq h' p _ rfl h (s b)).trans ?_⟩
    rw [hp]
    have k : dualApp l le_rfl (e b) = cst R (c b) := by
      dsimp [l]
      rw [dualApp_sum, LinearMap.sum_apply]
      simp [dualApp_smul, hcoord]
    rw [k, Iso.inv_hom_id_apply]

omit h'

theorem exists_tanM_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (n : ℕ)
    (s : Fin n → Γ(omega t.G, V)) (hs : VB.IsFrame s) :
    ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) :=
  exists_equiv_of_isGrpPullback (isGrpPullback_pullback t.G x) h hs

end GlobalTheory.LocM.TanPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibre
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.GenFibreComp

theorem exists_fn_hom {F L : Type} [Field F] [Field L] {V : Scheme.{0}} [IsIntegral V] (p : V ⟶ Sp F)
    (g : Sp L ⟶ V) (hg : g (IsLocalRing.closedPoint L) = genericPoint V) (ψ : F →+* L) (hψ : g ≫ p = spMap ψ) :
    ∃ φ : V.functionField →+* L, φ.comp (GlobalTheory.Cartier.constFn p) = ψ := by
  have hs : g (IsLocalRing.closedPoint L) ⤳ genericPoint V := hg ▸ specializes_rfl
  refine ⟨(V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g).hom, ?_⟩
  have h1 : V.presheaf.germ ⊤ (genericPoint V) (TopologicalSpace.Opens.mem_top _) ≫ V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g
      = g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
    exact congrArg (g.app ⊤ ≫ ·) ((congrArg (· ≫ _) ((Spec (CommRingCat.of L)).presheaf.map_id _)).trans
      (Category.id_comp _))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      = CommRingCat.ofHom ψ := by
    rw [← Scheme.Hom.comp_appTop_assoc, hψ, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h1] at h2
  ext a
  have h3 := congrArg (fun t => t.hom a) h2
  refine Eq.trans ?_ h3
  have h4 : p.appLE ⊤ ⊤ le_top = p.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg (p.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)
  rw [← h4]
  rfl

theorem isProjOver_comp_equiv {F K : Type} [Field F] [Field K] (e : F ≃+* K) {X : Scheme.{0}} (p : X ⟶ Sp K)
    (h : IsProjOver p) : IsProjOver (p ≫ spMap e.toRingHom) := by
  have hi : spMap e.symm.toRingHom ≫ spMap e.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have hi' : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have : IsIso (spMap e.symm.toRingHom) := ⟨_, hi, hi'⟩
  have h1 := (GlobalTheory.ProjSpace.points_and_stability K 0).2.2.1 F e.symm.toRingHom X p h
  have h2 := (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ (inv (pullback.fst p (spMap e.symm.toRingHom))) _
    inferInstance h1
  convert h2 using 1
  rw [IsIso.eq_inv_comp, pullback.condition_assoc, hi, Category.comp_id]

theorem exists_vars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed (Xo := Xo) (c := c) → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hF hsm
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have := Z.jQ_open
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  have hgen : ∀ i : Comp Xo c, IsGenericPoint (genPt i) i.1 := fun i => CompSplitPfD.cspD_gen i.2
  have hpre : ∀ i : Comp Xo c, Z.jQ ⁻¹' connectedComponent (Z.jQ (genPt i)) = i.1 := fun i => by
    by_contra hn
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _
      ⟨_, PtComp.preimage_connectedComponent_mem Z hS (Z.jQ (genPt i))⟩ i fun h => hn (congrArg Subtype.val h))
      mem_connectedComponent (hgen i).mem
  let V : Comp Xo c → (gen Z).Opens := fun i => ⟨connectedComponent (Z.jQ (genPt i)), (hcc _).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have key : ∀ i, ∃ (Y : GlobalTheory.ProjVar.Var F) (ε : (V i).toScheme ≅ Y.X), Y.dim = Dw.dim ∧
      ε.hom ≫ Y.str = (V i).ι ≫ genStr Z ≫ spMap e.toRingHom := fun i => by
    have : IrreducibleSpace (V i).toScheme := Subtype.irreducibleSpace (hcc _).1.1
    have : IsIntegral (V i).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have hcl : IsClosedImmersion (V i).ι := IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
    have hp : IsProjOver ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) :=
      (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
    have hsd : SmoothOfRelativeDimension Dw.dim ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
      simpa using h
    have hr : Set.range (genSp i ≫ Z.jQ) ⊆ Set.range (V i).ι := by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, genSp, Scheme.fromSpecResidueField_apply]
      exact mem_connectedComponent
    let g : Sp (kap i) ⟶ (V i).toScheme := IsOpenImmersion.lift (V i).ι (genSp i ≫ Z.jQ) hr
    have hg : g ≫ (V i).ι = genSp i ≫ Z.jQ := IsOpenImmersion.lift_fac _ _ _
    have hgp : (V i).ι (g (IsLocalRing.closedPoint (kap i))) = Z.jQ (genPt i) := by
      exact (Scheme.Hom.comp_apply g (V i).ι _).symm.trans ((congrArg (fun t : Sp (kap i) ⟶ gen Z => t (IsLocalRing.closedPoint (kap i))) hg).trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg Z.jQ (Scheme.fromSpecResidueField_apply _ _))))
    have hgg : g (IsLocalRing.closedPoint (kap i)) = genericPoint (V i).toScheme := by
      have h1 : (V i).ι (genericPoint (V i).toScheme) ⤳ Z.jQ (genPt i) :=
        hgp ▸ (genericPoint_specializes _).map (V i).ι.continuous
      obtain ⟨a, ha⟩ := h1.mem_open Z.jQ.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
      have h2 : a = genPt i := CompSplitPfD.cspD_max i.2 (hgen i) a
        (Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 (ha ▸ h1))
      apply (V i).ι.isOpenEmbedding.injective
      rw [hgp, ← ha, h2]
    obtain ⟨φ, hφ⟩ := exists_fn_hom ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) g hgg
      ((algebraMap c.F (kap i)).comp e.toRingHom) (by
        rw [reassoc_of% hg, reassoc_of% Z.jQ_over, ← Category.assoc]
        exact (congrArg (· ≫ _) (Spec.map_preimage (genSp i ≫ strK)).symm).trans (Spec.map_comp _ _).symm)
    have : GeometricallyConnected ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
      rintro a ⟨P, hP, hPa⟩
      let χ : (V i).toScheme.functionField →+* Om i := (algebraMap (kap i) (Om i)).comp φ
      have hχ : χ.comp (GlobalTheory.Cartier.constFn ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)) =
          (algebraMap c.F (Om i)).comp e.toRingHom := by
        rw [RingHom.comp_assoc, hφ, IsScalarTower.algebraMap_eq c.F (kap i) (Om i), RingHom.comp_assoc]
      obtain ⟨b, hb⟩ := hF i (χ a) ⟨P.map e.toRingHom, (Polynomial.map_ne_zero_iff e.injective).2 hP, by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hχ, ← Polynomial.hom_eval₂, hPa, map_zero]⟩
      refine ⟨e.symm b, χ.injective ?_⟩
      rw [← hb]
      exact (RingHom.congr_fun hχ _).trans (by simp)
    exact GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  choose B ε hd hs using key
  have hrange : ∀ i, Set.range ((ε i).inv ≫ (V i).ι) = connectedComponent (Z.jQ (genPt i)) := fun i => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (ε i).inv.surjective.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
    rfl
  refine ⟨B, fun i => (ε i).inv ≫ (V i).ι, fun i => ⟨inferInstance, hd i, ?_, fun p hp => ?_⟩, fun z => ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [hrange]
    rw [← hpre] at hp
    exact hp
  · refine ⟨⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩, ?_, fun i hi => ?_⟩
    · beta_reduce
      rw [hrange]
      have h := (hgen ⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩).mem
      rw [← connectedComponent_eq (show Z.jQ _ ∈ connectedComponent z from h)]
      exact mem_connectedComponent
    · beta_reduce at hi
      rw [hrange] at hi
      apply Subtype.ext
      rw [← hpre, connectedComponent_eq hi]

end GlobalTheory.GenFibreComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_varieties_components_smooth_genericFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed (Xo := Xo) (c := c) → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  first | exact @GlobalTheory.GenFibreComp.exists_vars | exact GlobalTheory.GenFibreComp.exists_vars | (intros; apply GlobalTheory.GenFibreComp.exists_vars <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.ExpDirs

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc ReciprocityTheory.ChartRestriction.G.PullbackSections Filter
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isDerivAt0_of_comb {X : Scheme.{0}} {t : SAB H X} {x : Sp ℂ ⟶ X} {g m : ℕ}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)} (e0 : e 0 = (1 : Over.mk x ⟶ t.G).left)
    {v : Fin m → (Sp (DualNumber ℂ) ⟶ t.G.left)} {w : Fin m → Fin g → ℂ} (ht : ∀ i, IsTanAtG t x (v i))
    (hv : ∀ i, IsDerivAt0 e (w i) (v i)) {a : Fin m → ℂ} {v' : Sp (DualNumber ℂ) ⟶ t.G.left} (ht' : IsTanAtG t x v')
    (hc : IsCombAtG t x v a v') : IsDerivAt0 e (∑ i, a i • w i) v' := by
  refine ⟨ht'.2.trans e0.symm, fun U h f => ?_⟩
  have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => DerLin.le_of_fst_eq ((ht i).2.trans ht'.2.symm) h
  let b : Fin m → TanMod.TanSp x t.G := fun i =>
    TanMod.TanSp.mk (Over.homMk (v i) (ht i).1) (TanMod.smT_zero_of x _ (ht i).2)
  have key : (TanDeriv.evAt v' U h f).snd = ∑ i, a i * (TanDeriv.evAt (v i) U (hU i) f).snd := by
    refine TanDeriv.derivAt_sum b a v' ?_ U h hU f
    obtain ⟨u, hu, rfl⟩ := hc
    have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst hub
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  refine key.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact congrArg (a i * ·) ((hv i).2 U (hU i) f)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {σ : c.F →+* ℂ}

theorem frame_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := ℂ) (ReciprocityTheory.ChartRestriction.G.Chart.JetR ℂ (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}
    (hx : IsUnivChart _ n xc) (cc : Letter Dw → Fin n → ℂ) (hcc : ∀ z, f.v z.1 z.2 = vec Z.t x xc (cc z)) :
    LinearIndependent ℂ cc ∧ ⊤ ≤ Submodule.span ℂ (Set.range cc) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨p, hp, hps⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hE : ∀ τ m, IsEigV (rho hx) (embK c τ) m ↔ ∀ a : 𝓞 E, vec Z.t x xc m ≫ (Z.t.act.act a).left =
      spMap (epsMul (σ (embK c τ a))) ≫ vec Z.t x xc m := fun τ m => by
    rw [vec_eig_iff hx (fun a => σ (embK c τ a)), ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
    rfl
  have hv : ∀ τ, f.v τ = fun i => vec Z.t x xc (cc ⟨τ, i⟩) := fun τ => funext fun i => hcc ⟨τ, i⟩
  have hb : ∀ τ m, IsEigV (rho hx) (embK c τ) m → ∃! a : Fin (Dw.mult τ) → ℂ, m = ∑ i, a i • cc ⟨τ, i⟩ :=
    fun τ m hm => by
      have := f.basis τ _ (vec_tan hx m) ((hE τ m).1 hm)
      rw [hv] at this
      simpa only [LieLocBasis.comb_iff hx] using this
  have he : ∀ τ (a : Fin (Dw.mult τ) → ℂ), IsEigV (rho hx) (embK c τ) (∑ i, a i • cc ⟨τ, i⟩) := fun τ a r => by
    have h1 : ∀ i, IsEigV (rho hx) (embK c τ) (cc ⟨τ, i⟩) := fun i => (hE _ _).2 (hcc ⟨τ, i⟩ ▸ f.eig τ i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, h1 i r, smul_comm]
  refine ⟨Fintype.linearIndependent_iff.2 fun a ha z => ?_, fun m _ => ?_⟩
  · rw [Fintype.sum_sigma] at ha
    have h1 := proj_sum_eig (rho hx) (embK c) α hinj _ (fun τ => he τ fun i => a ⟨τ, i⟩) z.1
    rw [ha, map_zero] at h1
    exact congrFun ((hb z.1 0 fun r => by simp).unique h1 (y₂ := 0) (by simp)) z.2
  · have h1 := LinearMap.congr_fun (sum_proj (rho hx) (embK c) α hinj) m
    rw [LinearMap.sum_apply, Module.End.one_apply] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := hb τ _ (eig_of_alpha _ _ α hN τ (proj_eig_alpha (rho hx) _ α hinj p hp hps τ m))
    rw [ha]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem dirs_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)}
    (e0 : e 0 = (1 : Over.mk x ⟶ Z.t.G).left) (h1 : ∀ w, ∃! v, IsTanAtG Z.t x v ∧ IsDerivAt0 e w v)
    (h2 : ∀ v, IsTanAtG Z.t x v → ∃! w, IsDerivAt0 e w v) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, IsDerivAt0 e (W z) (f.v z.1 z.2)) : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W := by
  classical
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose cc hcc using fun z : Letter Dw => vec_exists hx _ (f.tan z.1 z.2)
  obtain ⟨hli, hsp⟩ := frame_basis f hx cc hcc
  choose u hu using fun j : Fin n => (h2 _ (vec_tan hx (Pi.single j 1))).exists
  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ u
  have hT : ∀ m, IsDerivAt0 e (T m) (vec Z.t x xc m) := fun m =>
    isDerivAt0_of_comb e0 (fun j => vec_tan hx _) hu (vec_tan hx m) ((LieLocBasis.comb_iff hx _ m m).2 (by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]))
  have hbij : Function.Bijective T := by
    refine ⟨fun m m' h => vec_inj hx ((h1 (T m)).unique ⟨vec_tan hx m, hT m⟩ ⟨vec_tan hx m', h ▸ hT m'⟩), fun w => ?_⟩
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h1 w
    obtain ⟨m, rfl⟩ := vec_exists hx v hv
    exact ⟨m, (h2 _ hv).unique (hT m) hd⟩
  refine ⟨(Module.Basis.mk hli hsp).map (LinearEquiv.ofBijective T hbij), funext fun z => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  exact (h2 _ (f.tan z.1 z.2)).unique (hcc z ▸ hT (cc z)) (hW z)

theorem differentiableAt_dir {n g : ℕ} {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (he : IsExpChart e ex) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {B : Set V} (hB : IsOpen B) {x : V → CxPts (genStr Z) σ}
    (hx : IsHolTo B fun b => (x b).1) (hs : ∀ b ∈ B, x b ∈ e.source) {v : V → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)}
    (hv : HolTan B v) {W : V → Fin g → ℂ} (hW : ∀ b ∈ B, IsDerivAt0 (fun w => (ex (x b) w).left) (W b) (v b))
    {b₀ : V} (hb₀ : b₀ ∈ B) : DifferentiableAt ℂ W b₀ := by
  obtain ⟨-, h1, -, h3, h4, h5⟩ := he
  let ε : CxPts (genStr Z) σ → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun y w => (ex y w).left
  have hz : DifferentiableAt ℂ (fun b => e (x b)) b₀ :=
    differentiableAt_pi.2 fun k => (h1 k V B x hB hx hs).differentiableAt (hB.mem_nhds hb₀)
  have ht := e.map_source (hs b₀ hb₀)
  have hl : ∀ b ∈ B, ε (e.symm (e (x b))) = ε (x b) := fun b hb => by rw [e.left_inv (hs b hb)]
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (U : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, U)), ⊤ ≤ ε (x b₀) 0 ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (ε (x b₀) z) U f) 0 w = 0 := by
    intro U f hU
    have hU' : ⊤ ≤ ε (e.symm (e (x b₀))) 0 ⁻¹ᵁ U := by rwa [hl b₀ hb₀]
    have d := (HolLieFrame.differentiableAt_fderiv (e := fun z => ε (e.symm z)) h4 ht U f hU').comp b₀ hz
    have hn : ∀ᶠ b in 𝓝 b₀, b ∈ B ∧ ⊤ ≤ v b ⁻¹ᵁ U := by
      have hc : ContinuousAt (fun b => (e (x b), (0 : Fin g → ℂ))) b₀ := hz.continuousAt.prodMk continuousAt_const
      filter_upwards [hB.mem_nhds hb₀, hc.preimage_mem_nhds ((h4 U f).1.mem_nhds ⟨⟨ht, trivial⟩, hU'⟩)] with b hb hb'
      have h' : ⊤ ≤ ε (e.symm (e (x b))) 0 ⁻¹ᵁ U := hb'.2
      rw [hl b hb] at h'
      exact ⟨hb, (TangentOrigin.top_le_preimage_iff _ U).2 (by rw [(hW b hb).1]; exact h')⟩
    refine hw (fun b => fderiv ℂ (fun z => valAt' (ε (x b) z) U f) 0) (d.congr_of_eventuallyEq ?_)
      (((hv U f).differentiableAt hn).congr_of_eventuallyEq ?_)
    · filter_upwards [hB.mem_nhds hb₀] with b hb
      simp only [Function.comp_apply, hl b hb]
    · filter_upwards [hn] with b ⟨hb, h⟩
      refine ((hW b hb).2 U h f).symm.trans ?_
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR, dite_eq_left h]
  have d₁ := LocalLift.isDerivAt0_const (ε (x b₀)) w hw'
  have d₀ := LocalLift.isDerivAt0_const (ε (x b₀)) 0 fun _ _ _ => map_zero _
  have e0 : ex (x b₀) 0 = 1 := by simpa using h3 _ (hs b₀ hb₀) 0 0
  exact ((h5 _ (hs b₀ hb₀)).2 _ ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (ex (x b₀) 0))),
    d₁.1.trans (congrArg (·.left) e0)⟩).unique d₁ d₀

theorem exists_inverse {J : Type} [Fintype J] [DecidableEq J] {g : ℕ} (b : Module.Basis J ℂ (Fin g → ℂ)) :
    ∃ Wi : Matrix (Fin g) J ℂ, Matrix.of b * Wi = 1 ∧ Wi * Matrix.of b = 1 := by
  refine ⟨Matrix.of fun j z => b.repr (Pi.single j 1) z, ?_, ?_⟩
  · ext z z'
    have h : b z = ∑ j, b z j • (Pi.single j 1 : Fin g → ℂ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 := congrArg (fun w => b.repr w z') h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_apply, Matrix.one_apply, h2]
    rfl
  · ext j k
    have h := congrFun (b.sum_repr (Pi.single j 1)) k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Finset.sum_apply, Pi.single_apply, eq_comm] using h

theorem exists_dirs_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ e.source) → ∃ (W : V → Matrix (Letter Dw) (Fin g) ℂ) (Wi : V → Matrix (Fin g) (Letter Dw) ℂ), ContinuousOn W B ∧ ContinuousOn Wi B ∧ ∀ b ∈ B, Dirs (a b) (fun w => (ex (a b).1 w).left) (W b) ∧ W b * Wi b = 1 ∧ Wi b * W b = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex he V _ _ _ B a hB ha hs
  have h5 := fun b hb => he.2.2.2.2.2 _ (hs b hb)
  choose! W hW using fun b hb (z : Letter Dw) => ((h5 b hb).2 _ ((a b).2.tan z.1 z.2)).exists
  have hbas : ∀ b ∈ B, ∃ bs : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑bs = W b := fun b hb => by
    have e0 : ex (a b).1 0 = 1 := by simpa using he.2.2.2.1 _ (hs b hb) 0 0
    exact dirs_basis (a b).2 (e := fun w => (ex (a b).1 w).left) (congrArg (·.left) e0) (h5 b hb).1 (h5 b hb).2 (hW b hb)
  have hinv : ∀ b ∈ B, ∃ Wi : Matrix (Fin g) (Letter Dw) ℂ, Matrix.of (W b) * Wi = 1 ∧ Wi * Matrix.of (W b) = 1 :=
    fun b hb => by
      obtain ⟨bs, h⟩ := hbas b hb
      rw [← h]
      exact exists_inverse bs
  choose! Wi hWi using hinv
  have hd : ∀ b ∈ B, ∀ z, DifferentiableAt ℂ (fun b => W b z) b := fun b hb z =>
    differentiableAt_dir he hB ha.1 hs (ha.2 z.1 z.2) (fun b hb => hW b hb z) hb
  refine ⟨fun b => Matrix.of (W b), Wi, fun b hb => ContinuousAt.continuousWithinAt ?_,
    fun b hb => ContinuousAt.continuousWithinAt ?_, fun b hb => ⟨hW b hb, hWi b hb⟩⟩
  · exact continuousAt_pi.2 fun z => (hd b hb z).continuousAt
  · obtain ⟨bs, -⟩ := hbas b hb
    let q : Fin g ≃ Letter Dw := (Pi.basisFun ℂ (Fin g)).indexEquiv bs
    refine continuousAt_pi.2 fun j => continuousAt_pi.2 fun z => ?_
    have := HolFrameMatrix.differentiableAt_of_mul_eq_one (fun b => (Wi b).submatrix id q)
      (fun b => (Matrix.of (W b)).submatrix q id) b (fun i k => differentiableAt_pi.1 (hd b hb (q i)) k) (by
        filter_upwards [hB.mem_nhds hb] with b' hb'
        rw [Matrix.submatrix_mul_equiv, (hWi b' hb').2]
        rfl) j (q.symm z)
    simpa using this.continuousAt

end GlobalTheory.ShFam.Hor.ExpDirs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousOn_frameDirections_inverse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ e.source) → ∃ (W : V → Matrix (Letter Dw) (Fin g) ℂ) (Wi : V → Matrix (Fin g) (Letter Dw) ℂ), ContinuousOn W B ∧ ContinuousOn Wi B ∧ ∀ b ∈ B, Dirs (a b) (fun w => (ex (a b).1 w).left) (W b) ∧ W b * Wi b = 1 ∧ Wi b * W b = 1 := by
  first | exact @GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn | exact GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn | (intros; apply GlobalTheory.ShFam.Hor.ExpDirs.exists_dirs_continuousOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSections
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSections
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

theorem exists_blowup_graph {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (hσ : Generates J σ) :
    ∃ (G : Scheme.{0}) (b : G ⟶ X) (c : G ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      FinalTheorems.Blowup b J ∧ Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  have : IsProper (PSpace.str R m) := isProper_str R m
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let U : X.Opens := J.support.compl
  have hU : ∀ x : U.toScheme, U.ι x ∉ J.support := fun x => x.2
  have htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤ := fun g hg =>
    eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)
  obtain ⟨φ, hφ, hφσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ)
    (by rw [htop _ hU]; exact effCartier_top _)
  let b := graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm
  let c := graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm
  let j := graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm
  have hjb : j ≫ b = U.ι := graphClosure.incl_fst ..
  have hjc : j ≫ c = φ := graphClosure.incl_snd ..
  have hbc : Proportional σ b c := .of_comp j (by rwa [hjb, hjc])
  have hc : b ≫ s = c ≫ PSpace.str R m := graphClosure.condition ..
  have hι : pullback.lift b c hc = graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]; rfl
    · rw [pullback.lift_snd]; rfl
  refine ⟨_, b, c, hc, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance
    inferInstance fun t => ?_, fun W g hg => ?_⟩, hbc, ?_⟩
  · rw [mem_support_comap, ← Scheme.Hom.comp_apply, hjb]; exact hU t
  · obtain ⟨ψ, hψ, hψσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg
    have hd := GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg
    let d := Scheme.Opens.ι (X := W) (J.comap g).support.compl
    have hdU : ∀ t, (d ≫ g) t ∉ J.support := fun t ht => t.2 ((mem_support_comap J g _).2 ht)
    let w := IsOpenImmersion.lift U.ι (d ≫ g) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨_, hdU t⟩, rfl⟩)
    have hw : w ≫ U.ι = d ≫ g := IsOpenImmersion.lift_fac ..
    have hw' : d ≫ ψ = w ≫ φ := GlobalTheory.T.eq_of_proportional_to_generating_sections R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ)
      (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)
    have key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j := fun h hh => by
      have H := graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm
      have e : w ≫ U.ι = (d ≫ h) ≫ b := by rw [hw, Category.assoc, hh]
      have h1 := H.lift_fst w (d ≫ h) e
      rw [Category.comp_id] at h1
      rw [← H.lift_snd w (d ≫ h) e, h1]
    have hl := graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'
    exact ⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm)
      (hh.trans hl.symm)⟩
  · rw [hι]; infer_instance

theorem exists_iso_of_blowup {X X' G : Scheme.{0}} (J : X.IdealSheafData) (b : X' ⟶ X) (b₀ : G ⟶ X)
    (hb : FinalTheorems.Blowup b J) (hb₀ : FinalTheorems.Blowup b₀ J) : ∃ e : X' ⟶ G, IsIso e ∧ e ≫ b₀ = b := by
  obtain ⟨e, he, -⟩ := hb₀.2 X' b hb.1
  obtain ⟨e', he', -⟩ := hb.2 G b₀ hb₀.1
  have h1 : e ≫ e' = 𝟙 X' := by
    obtain ⟨_, -, hu⟩ := hb.2 X' b hb.1
    rw [hu (e ≫ e') (by show (e ≫ e') ≫ b = b; rw [Category.assoc, he', he]), hu (𝟙 X') (Category.id_comp _)]
  have h2 : e' ≫ e = 𝟙 G := by
    obtain ⟨_, -, hu⟩ := hb₀.2 G b₀ hb₀.1
    rw [hu (e' ≫ e) (by show (e' ≫ e) ≫ b₀ = b₀; rw [Category.assoc, he, he']), hu (𝟙 G) (Category.id_comp _)]
  exact ⟨e, ⟨e', h1, h2⟩, he⟩

theorem exists_closedImmersion_of_generates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (J : X.IdealSheafData)
    (b : X' ⟶ X) (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), IsProjOver s → FinalTheorems.Blowup b J →
    GlobalTheory.ProjBlowup.Generates J σ → ∃ (c : X' ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      GlobalTheory.ProjBlowup.Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  intro R _ _ X X' s J b L₀ m σ hs hb hσ
  obtain ⟨G, b₀, c₀, hc₀, hb₀, hp₀, hi₀⟩ := exists_blowup_graph s hs J L₀ m σ hσ
  obtain ⟨e, he, heb⟩ := exists_iso_of_blowup J b b₀ hb hb₀
  have hc : b ≫ s = (e ≫ c₀) ≫ PSpace.str R m := by rw [← heb, Category.assoc, Category.assoc, hc₀]
  have hp : Proportional σ b (e ≫ c₀) := heb ▸ hp₀.comp e
  have hl : pullback.lift b (e ≫ c₀) hc = e ≫ pullback.lift b₀ c₀ hc₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, heb]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  refine ⟨e ≫ c₀, hc, hp, ?_⟩
  rw [hl]
  infer_instance

end GlobalTheory.ProjBlowup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClosedImmersionBlowupGeneratingSectionsStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedImmersion_blowup_generatingSections : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData)
    (b : X' ⟶ X) (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), IsProjOver s → FinalTheorems.Blowup b J →
    GlobalTheory.ProjBlowup.Generates J σ → ∃ (c : X' ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      GlobalTheory.ProjBlowup.Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  first | exact @GlobalTheory.ProjBlowup.exists_closedImmersion_of_generates | exact GlobalTheory.ProjBlowup.exists_closedImmersion_of_generates | (intros; apply GlobalTheory.ProjBlowup.exists_closedImmersion_of_generates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFree
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFree
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRep

theorem exists_finite_free_rep (O : Type) [CommRing O] [HenselianLocalRing O] {Y : Scheme.{0}} (f : Y ⟶ Sp O)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] [Flat f] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (j : Sp A ⟶ Y), Module.Finite O A ∧ Module.Free O A ∧
      j ≫ f = spMap (algebraMap O A) ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B]
        (h : Sp B ⟶ Y), h ≫ f = spMap (algebraMap O B) → ∃! φ : A →ₐ[O] B, spMap (φ : A →+* B) ≫ j = h := by
  have : HenselianLocalRing (CommRingCat.of O) := ‹_›
  have hfin : IsFinite ((finitePart f).ι ≫ f) := isFinite_finitePart f
  have : IsAffine (finitePart f).toScheme := isAffine_of_isAffineHom ((finitePart f).ι ≫ f)
  let A : CommRingCat.{0} := Γ((finitePart f).toScheme, ⊤)
  let i : Spec A ≅ (finitePart f).toScheme := (finitePart f).toScheme.isoSpec.symm
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i.hom ≫ (finitePart f).ι ≫ f)
  have h₁ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    infer_instance
  have h₂ : ψ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hψ]
    infer_instance
  let _ : Algebra O A := ψ.hom.toAlgebra
  have h₃ : Module.Finite O A := h₁
  have h₄ : Module.Flat O A := h₂
  have hj : (i.hom ≫ (finitePart f).ι) ≫ f = spMap (algebraMap O A) := by
    rw [Category.assoc, ← hψ]; rfl
  refine ⟨A, inferInstance, inferInstance, i.hom ≫ (finitePart f).ι, h₃,
    Module.free_of_flat_of_isLocalRing, hj, fun B _ _ _ h hh => ?_⟩
  have : IsFinite (spMap (algebraMap O B)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 ‹_›)
  obtain ⟨l, hl, -⟩ := existsUnique_lift_finitePart f _ h hh
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (R := A) (S := .of B) (l ≫ i.inv)
  have hχ' : Spec.map χ ≫ i.hom ≫ (finitePart f).ι = h := by
    rw [hχ, Category.assoc, i.inv_hom_id_assoc, hl]
  have hc : CommRingCat.ofHom (algebraMap O A) ≫ χ = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    refine Eq.trans ?_ hh
    rw [← hχ', Category.assoc, hj]
  refine ⟨⟨χ.hom, fun r => congr(($hc).hom r)⟩, hχ', fun φ hφ => ?_⟩
  have h₅ : spMap (φ : A →+* B) = Spec.map χ := by
    rw [← cancel_mono (i.hom ≫ (finitePart f).ι)]
    exact hφ.trans hχ'.symm
  have h₆ := Spec.map_injective h₅
  exact AlgHom.ext fun a => congr(($h₆).hom a)

theorem exists_finite_free_torsion_rep : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  intro X G _ _ hG O _ _ x q hq
  obtain ⟨hf, hqf⟩ := GlobalTheory.T.pow_flat_locallyQuasiFinite X G hG q hq
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  let m : G ⟶ G := (𝟙 G) ^ q
  have hm : ∀ {T : Over X} (g : T ⟶ G), g ≫ m = g ^ q := fun g => by
    rw [MonObj.comp_pow, Category.comp_id]
  have : Flat m.left := hf
  have : LocallyQuasiFinite m.left := hqf
  have : LocallyOfFiniteType (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp _ G.hom
  have : QuasiCompact (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact m.left := QuasiCompact.of_comp _ G.hom
  have : IsSeparated (m.left ≫ G.hom) := by rw [Over.w]; infer_instance
  have : IsSeparated m.left := IsSeparated.of_comp _ G.hom
  let e : Sp O ⟶ G.left := (1 : Over.mk x ⟶ G).left
  have he : e ≫ G.hom = x := Over.w (1 : Over.mk x ⟶ G)
  have h1 : ∀ (B : Type) [CommRing B] [Algebra O B],
      (1 : overAt x B ⟶ G).left = spMap (algebraMap O B) ≫ e := fun B _ _ => by
    let t : overAt x B ⟶ Over.mk x := Over.homMk (spMap (algebraMap O B)) rfl
    rw [← MonObj.comp_one t]
    rfl
  have : LocallyQuasiFinite (pullback.snd m.left e) :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (IsPullback.of_hasPullback m.left e) hqf
  obtain ⟨A, _, _, j, hA₁, hA₂, hj, H⟩ := exists_finite_free_rep O (pullback.snd m.left e)
  have hu : (j ≫ pullback.fst m.left e) ≫ m.left = spMap (algebraMap O A) ≫ e := by
    rw [Category.assoc, pullback.condition, reassoc_of% hj]
  let u : overAt x A ⟶ G := Over.homMk (j ≫ pullback.fst m.left e) (by
    rw [← Over.w m, ← Category.assoc]
    exact (congrArg (· ≫ G.hom) hu).trans (by rw [Category.assoc, he]; rfl))
  refine ⟨A, inferInstance, inferInstance, u, hA₁, hA₂, ?_, fun B _ _ _ g hg => ?_⟩
  · rw [← hm]
    exact Over.OverMorphism.ext (hu.trans (h1 A).symm)
  have hg' : g.left ≫ m.left = spMap (algebraMap O B) ≫ e := by
    rw [← Over.comp_left, hm, hg, h1]
  obtain ⟨φ, hφ, hφ'⟩ := H B (pullback.lift g.left (spMap (algebraMap O B)) hg') (pullback.lift_snd _ _ _)
  refine ⟨φ, Over.OverMorphism.ext ?_, fun φ' h' => hφ' φ' ?_⟩
  · change spMap (φ : A →+* B) ≫ j ≫ pullback.fst m.left e = g.left
    rw [← Category.assoc, hφ]
    exact pullback.lift_fst _ _ _
  · apply pullback.hom_ext
    · rw [Category.assoc]
      exact (congrArg CommaMorphism.left h').trans (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, hj]
      refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, φ'.comp_algebraMap]

end GlobalTheory.TorsionRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionRepresentableFiniteFreeStatement
open AlgebraicGeometry CategoryTheory Limits MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_representable_finite_free : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (O : Type) [CommRing O] [HenselianLocalRing O] (x : Sp O ⟶ X) (q : ℕ), q ≠ 0 → ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (u : overAt x A ⟶ G), Module.Finite O A ∧ Module.Free O A ∧ u ^ q = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] [Module.Finite O B] (g : overAt x B ⟶ G), g ^ q = 1 → ∃! φ : A →ₐ[O] B, homAt x φ ≫ u = g := by
  first | exact @GlobalTheory.TorsionRep.exists_finite_free_torsion_rep | exact GlobalTheory.TorsionRep.exists_finite_free_torsion_rep | (intros; apply GlobalTheory.TorsionRep.exists_finite_free_torsion_rep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChange
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.ShFam.Pad.isFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) :=
  GlobalTheory.LocM.isFrame_bc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrame_compose_ringHom_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  first | exact @GlobalTheory.ShFam.Pad.isFrame_baseChange | exact GlobalTheory.ShFam.Pad.isFrame_baseChange | (intros; apply GlobalTheory.ShFam.Pad.isFrame_baseChange <;> assumption)
end
end
