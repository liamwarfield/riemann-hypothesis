module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCommutatorPairingConstHolomorphicFamilyAn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
noncomputable section

namespace GlobalTheory.ThKConst

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  obtain ⟨c₁, t₁⟩ := h₁
  obtain ⟨c₂, t₂⟩ := h₂
  have e : ⇑(χ₁ / χ₂) = fun x => χ₁ x / χ₂ x := funext fun x => MonoidHom.div_apply χ₁ χ₂ x
  exact And.intro (by rw [e]; exact c₁.div' c₂) fun x => by rw [MonoidHom.div_apply, t₁ x, t₂ x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {n₁ n₂ n : ℕ} (h₁ : ResEtaPow K χ₁ n₁)
    (h₂ : ResEtaPow K χ₂ n₂) (he : Even (n₁ + n₂)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e₁ := h₁ x
  have e₂ := h₂ x
  rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂]
  split_ifs
  · norm_num
  · rcases Nat.even_or_odd n₁ with h | h
    · rw [h.neg_one_pow, ((Nat.even_add.mp he).mp h).neg_one_pow, hn.neg_one_pow]
      norm_num
    · have h' : Odd n₂ := Nat.not_even_iff_odd.mp fun h'' => (Nat.not_even_iff_odd.mpr h) ((Nat.even_add.mp he).mpr h'')
      rw [h.neg_one_pow, h'.neg_one_pow, hn.neg_one_pow]
      norm_num

variable {a a' : ℕ}

theorem isPair_small {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV'
    skew := h.geo.hW
    good := h.geo.hM'
    hX := h.chars.heckeα
    hW := isHecke_div h.chars.heckeα h.chars.heckeβ
    resX := h.chars.resα
    resW := resEtaPow_div h.chars.resα h.chars.resβ (Nat.even_add.mpr (Nat.even_add.mp h.geo.even).symm) h.geo.even
    weil := h.weil' }

theorem thetaSum_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (f : ι → (κ → AF F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => ?_) ?_
  · simp [thetaSum]
  · intro k s hk ih hf
    have hs : ∀ j ∈ s, f j ∈ schA F κ := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      thetaSum_add F (hf k (Finset.mem_insert_self k s)) (Submodule.sum_mem _ hs), ih hs]

end GlobalTheory.ThKConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Rigid

open GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem pull_cls_diag {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R}
    {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S} (m : ObjMap o' o f) :
    pull m.φ (cls _ (pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left)) =
      cls _ (pull_isLB o'.isLB (lift (𝟙 o'.A) (𝟙 o'.A)).left) := by
  have hs := m.sq
  have e : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = (_ ≫ _) ≫ (fst o.A o.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd o.A o.A).left = (_ ≫ _) ≫ (snd o.A o.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull m.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB :=
    ((cls_eq_iff o'.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol).symm
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem eq_on_torsion {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {S S' : Scheme.{0}}
    {s : S ⟶ Sp R} (o : Obj b N s) {A' : Over S'} [GrpObj A'] {f : S' ⟶ S}
    {φ φ' : A'.left ⟶ o.A.left} (hφ : IsGrpPullback A' o.A f φ)
    (lv : D.La → (𝟙_ (Over S') ⟶ A'))
    (h₁ : ∀ a, (lv a).left ≫ φ = f ≫ (o.eta a).left) (h₂ : ∀ a, (lv a).left ≫ φ' = f ≫ (o.eta a).left)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S') (y : Over.mk x ⟶ A') (hy : y ^ N = 1) :
    y.left ≫ φ = y.left ≫ φ' := by
  let β : R →+* k := (Spec.preimage ((x ≫ f) ≫ s)).hom
  obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (Spec.map_preimage _).symm
  have hy₁ : pushHom hφ (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
  obtain ⟨a, ha⟩ := (I.onto N hN hNp _).1 hy₁
  have hu : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := (Category.comp_id _).symm.trans (Over.w (toUnit _))
  have e : (x ≫ f) ≫ (o.eta a).left = y.left ≫ φ := by
    rw [← hu]
    exact congrArg (fun q => q.left) ((hI a).trans ha)
  have e₁ : y.left = x ≫ (lv a).left := by
    apply hφ.1.hom_ext
    · rw [Category.assoc]
      exact e.symm.trans ((Category.assoc _ _ _).trans (congrArg (x ≫ ·) (h₁ a).symm))
    · rw [Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁, Category.assoc, Category.assoc]
  exact congrArg (x ≫ ·) ((h₁ a).trans (h₂ a).symm)

theorem eq_id : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (m : ObjMap o o (𝟙 S)), m.φ = 𝟙 _ := by
  intro p _ D R _ b N hN hNp S s o m
  have hψ := m.cart
  have e₂ : m.φ ≫ o.A.hom = o.A.hom := hψ.1.w.trans (Category.comp_id _)
  haveI : IsIso m.φ := hψ.1.isIso_fst_of_isIso
  let σ : o.A ≅ o.A := Over.isoMk (asIso m.φ) e₂
  have hσ : IsMonHom σ.hom := isMonHom_of_mul_comp σ.hom fun T x y => mul_comp_of_grpPullback_id σ.hom hψ x y
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 o.A o.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S.residueField t)
    let j : Sp K ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField t) K)) ≫ S.fromSpecResidueField t
    have hp := isGrpPullback_pullback o.A j
    have := o.ab.smooth
    have := o.ab.proper
    have := o.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj o.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd o.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd o.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd o.A.hom j); infer_instance }
    have hNK : (N : K) ≠ 0 := by
      have hu := (b.unit N hNp).map (Spec.preimage (j ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have g := hp.comp m.cart
    rw [Category.comp_id] at g
    have e' := eq_of_field (pull_isLB o.isLB _) o.ample hab g hp
      (by rw [pull_comp, pull_cls_diag m]) hN hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ N = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion (φ' := 𝟙 _) (by omega) hNp o m.cart o.eta m.eta (fun a => by simp) Ω (x ≫ j) _ hy₁
        rw [← Category.assoc]
        exact e₁.trans (Category.comp_id _)
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · exact e'
  have := congrArg (fun q => q.left) key
  exact this

end GlobalTheory.UPel.HT.Rigid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumMult

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

abbrev multW (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (e : ℕ)
    (i i' : Fin 1 → U.LG.L.ι) : (thickObj R (maximalIdeal R) e G).left.Opens :=
  ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
    (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i'

def MultAct (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (N : ℕ)
    (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, multW U b e i i')) :
    Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ (f : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), (∀ e, U.ExpandsAt e k s f.f) →
    ∃ F : IntFam (maximalIdeal R) D.toPre (N * k), ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι),
      ChartExpOn U.toUnifPre e (N * k) i' (multW U b e i i')
        (m e i i' ^ k * ((thickObj R (maximalIdeal R) e G).left.presheaf.map
          (homOfLE (inf_le_left : multW U b e i i' ≤
            ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom
          ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) F.f

def LeadPt (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G)
    (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, multW U b e i i')) :
    Prop :=
  ∃ x : D.toPre.P.A.left, D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧
    ∀ y : (thickObj R (maximalIdeal R) 0 G).left, (U.gt 0).pG.left y = x →
      ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ multW U b 0 i i' →
        y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i')

def PosN (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) :
    Prop :=
  RelAmple D.toPre.P.A (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) ∧
    ∀ (κ : D.toPre.X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 →
      (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) →
      (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) →
      (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
        algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) →
      ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y)

def NonzeroAt (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (N : ℕ)
    (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]))
    (x : D.toPre.P.A.left) : Prop :=
  ∀ j : Fin 2 → D.toPre.P.L.ι,
    x ∈ LB.wchart D.toPre.P.L (![𝟙 D.toPre.P.A.left, a.left] : Fin 2 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) j →
      x ∈ D.toPre.P.A.left.basicOpen (σ₀.f j)

end GlobalTheory.MumMult
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.DvrDom

theorem exists_cdvr_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ IsLocalHom φ := by
  intro R _ _ _ _ _
  by_cases hR : IsField R
  · letI : Field R := hR.toField
    have hC : Function.Injective (PowerSeries.C (R := R)) := PowerSeries.C_injective
    have : CharZero (PowerSeries R) := charZero_of_injective_ringHom hC
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries R)) (PowerSeries R) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    have hl : IsLocalHom (PowerSeries.C (R := R)) := by
      constructor
      intro a ha
      by_cases h0 : a = 0
      · subst h0; simp at ha
      · exact isUnit_iff_ne_zero.mpr h0
    exact ⟨PowerSeries R, inferInstance, inferInstance, inferInstance, PowerSeries.C (R := R),
      (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, this⟩, hC, hl⟩
  · obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating (R := R) hR
    have : CharZero O := charZero_of_injective_ringHom h1
    exact ⟨O, inferInstance, hO, inferInstance, φ, (GlobalTheory.LN.cDvr_iff _).2 ⟨hO', hO'', this⟩, h1, h2⟩

end GlobalTheory.DvrDom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem isGenSec_of_univBasis {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {K K' : Type} [CommRing K]
    [CommRing K'] {x : Sp K ⟶ S} {e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))} (he : UnivBasis G L x e)
    (i : K →+* K') {x' : Sp K' ⟶ S} (h : spMap i ≫ x = x') :
    IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e) :=
  (isGenSec_iff _).2 fun s => by
    obtain ⟨c, hc, -⟩ := he K' i x' h s
    exact ⟨c, hc⟩

theorem spMap_id (K : Type) [CommRing K] : spMap (RingHom.id K) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem gen_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (K : Type)
    [Field K] (x : Sp K ⟶ S), PolFib G L g x → (∃ θ : SecAt G L x, IsGenSec G L _ θ) ∧
    ∀ θ : SecAt G L x, IsGenSec G L _ θ → ∀ (K' : Type) [Field K'] (i : K →+* K'),
      IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g K _ x hP
  obtain ⟨P, α, -, hp, hw⟩ := hP
  obtain ⟨e, he⟩ := exists_univBasis_of_fibre abelianSchemeLaws_all.2 S (Sp K) G L hL P x α hp hw K (𝟙 _) x
    (Category.id_comp x)
  have h0 : spMap (RingHom.id K) ≫ x = x := by rw [spMap_id, Category.id_comp]
  refine ⟨⟨_, isGenSec_of_univBasis he (RingHom.id K) h0⟩, fun θ hθ K' _ i => ?_⟩
  set e₀ := VVRank.pullS G _ (Over.homMk (spMap (RingHom.id K)) h0 : Over.mk x ⟶ Over.mk x) e with he₀
  obtain ⟨c, hc, -⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G θ)
  obtain ⟨r, hr⟩ := (isGenSec_iff θ).1 hθ (SecM.ofSec G e₀)
  obtain ⟨c₀, -, hu⟩ := he K (RingHom.id K) x h0 (SecM.ofSec G e₀)
  have hrc : r * c = 1 := by
    have e1 : SecM.ofSec G e₀ = (r * c) • SecM.ofSec G e₀ := by
      conv_lhs => rw [hr, hc]
      rw [smul_smul]
    exact (hu _ e1).trans (hu 1 (one_smul _ _).symm).symm
  have hcu : IsUnit c := ⟨⟨c, r, by rw [mul_comm]; exact hrc, hrc⟩, rfl⟩
  have ha : IsUnit ((fnR x).symm c) := hcu.map (fnR x).symm
  have hb := he.smul_pull hL (RingHom.id K) h0 ha
  have eq : SecM.toSec G (fnR x ((fnR x).symm c) • pl (RingHom.id K) h0 (SecM.ofSec G e)) = θ := by
    rw [RingEquiv.apply_symm_apply, pl_ofSec, ← hc]
    rfl
  rw [eq] at hb
  exact isGenSec_of_univBasis hb i rfl

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principallyPolarisedFibre_exists_generator_stable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (K : Type) [Field K] (x : Sp K ⟶ S), PolFib G L g x → (∃ θ : SecAt G L x, IsGenSec G L _ θ) ∧ ∀ θ : SecAt G L x, IsGenSec G L _ θ → ∀ (K' : Type) [Field K'] (i : K →+* K'), IsGenSec G L _ (SecAt.pull G L θ i) := by
  first | exact @GlobalTheory.UMin.gen_of_polFib | exact GlobalTheory.UMin.gen_of_polFib | (intros; apply GlobalTheory.UMin.gen_of_polFib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdUniq

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ c : A →+* B, spMap c = f :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem pCrd_iff {o R : Type} [CommRing o] [CommRing R] {n : ℕ} (x : Sp R ⟶ PSpace o n) (c : o →+* R)
    (hx : x ≫ PSpace.str o n = spMap c) (v : Fin (n + 1) → R) :
    PCrd x v ↔ ∃ hv : Ideal.span (Set.range v) = ⊤, x = ProjSpace.pt c v hv := by
  have h := ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c x (by rw [Category.comp_id]; exact hx) v
  have h2 := RepBC.secCoord_pull (ProjSpace.O1 o n) (ProjSpace.coord o n) (𝟙 _) x v
  rw [Category.comp_id] at h2
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Category.comp_id] at h
  exact h2.symm.trans h

theorem eq_of_pCrd {o R : Type} [CommRing o] [CommRing R] {n : ℕ} {x x' : Sp R ⟶ PSpace o n} {v : Fin (n + 1) → R}
    (hs : x ≫ PSpace.str o n = x' ≫ PSpace.str o n) (h : PCrd x v) (h' : PCrd x' v) : x = x' := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, e⟩ := (pCrd_iff x c hc.symm v).1 h
  obtain ⟨hv', e'⟩ := (pCrd_iff x' c (hs ▸ hc.symm) v).1 h'
  rw [e, e']

theorem exists_ne_zero_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (h : PCrd x v) : ∃ k, v k ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, -⟩ := (pCrd_iff x c hc.symm v).1 h
  by_contra hn
  push_neg at hn
  have : Set.range v ⊆ {0} := by rintro _ ⟨k, rfl⟩; exact hn k
  have h0 : Ideal.span (Set.range v) = ⊥ := by
    rw [Ideal.span_eq_bot]; intro y hy; exact this hy
  rw [h0] at hv
  exact bot_ne_top hv

theorem scalar_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v w : Fin (n + 1) → K} (hv : PCrd x v) (hw : PCrd x w) : ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j := by
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hv).2.2 w hw
  exact ⟨u, u.ne_zero, hu⟩

theorem pCrd_of_map {o K K' : Type} [CommRing o] [Field K] [Field K'] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (i : K →+* K') (h : PCrd (spMap i ≫ x) (fun j => i (v j))) : PCrd x v := by
  obtain ⟨w, hw⟩ := FieldPoint.exists_secCoord o n K x
  have hw' := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).1 K' i
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw').2.2 _ h
  obtain ⟨k, hk⟩ := exists_ne_zero_of_pCrd h
  have hvk : v k ≠ 0 := fun e => hk (by simp only [e, map_zero])
  have hwk : w k ≠ 0 := fun e => hk (by rw [hu k]; simp only [e, map_zero, mul_zero])
  have hua : (u : K') = i (v k / w k) := by
    rw [map_div₀, eq_div_iff ((map_ne_zero i).2 hwk), hu k]
  have hvj : ∀ j, v j = (v k / w k) * w j := fun j => by
    apply i.injective
    rw [hu j, hua, map_mul]
  have hs := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).2.1
    (Units.mk0 (v k / w k) (div_ne_zero hvk hwk))
  have e : (fun j => ((Units.mk0 (v k / w k) (div_ne_zero hvk hwk) : Kˣ) : K) * w j) = v :=
    funext fun j => (hvj j).symm
  rw [e] at hs
  exact hs

theorem main : (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x x' : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K), x ≫ PSpace.str o n = x' ≫ PSpace.str o n → PCrd x v → PCrd x' v → x = x') ∧ (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v w : Fin (n + 1) → K), PCrd x v → PCrd x w → ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j) ∧ ∀ (o K K' : Type) [CommRing o] [Field K] [Field K'] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (i : K →+* K'), PCrd (spMap i ≫ x) (fun j => i (v j)) → PCrd x v :=
  ⟨fun _ _ _ _ _ _ _ _ hs h h' => eq_of_pCrd hs h h',
   fun _ _ _ _ _ _ _ _ hv hw => scalar_of_pCrd hv hw,
   fun _ _ _ _ _ _ _ _ _ i h => pCrd_of_map i h⟩

end GlobalTheory.UMin.CrdUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescendStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveHomogeneousCoords_field_determine_descend : (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x x' : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K), x ≫ PSpace.str o n = x' ≫ PSpace.str o n → PCrd x v → PCrd x' v → x = x') ∧ (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v w : Fin (n + 1) → K), PCrd x v → PCrd x w → ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j) ∧ ∀ (o K K' : Type) [CommRing o] [Field K] [Field K'] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (i : K →+* K'), PCrd (spMap i ≫ x) (fun j => i (v j)) → PCrd x v := by
  first | exact @GlobalTheory.UMin.CrdUniq.main | exact GlobalTheory.UMin.CrdUniq.main | (intros; apply GlobalTheory.UMin.CrdUniq.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumCmp

section Maps

variable {X Y X' : Scheme.{0}} (L : LB X) (L' : LB X') {J : Type} [Fintype J]

lemma mapsAtExp_le_b (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L (fun i => p ≫ pr i) jN := by
  intro y hy
  refine Set.mem_iInter.2 fun i => ?_
  have h1 : p.base y ∈ LB.wchart L pr jN := hy.1
  exact Set.mem_iInter.1 h1 i

lemma mapsAtExp_le_a (pr : J → (X' ⟶ X)) (ε : J → ℤ) (p : Y ⟶ X') (jN : J → L.ι) (jL : L'.ι) :
    p ⁻¹ᵁ (LB.div (LB.LinComb L pr ε) L').U (jN, jL) ≤ LB.wchart L' (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

def MapsAtExp (pr : J → (X' ⟶ X)) (ε : J → ℤ) (w : LB.Iso L' (LB.LinComb L pr ε)) (p : Y ⟶ X') (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := J) (fun i => p ≫ pr i) (fun i => n * ε i))) : Prop :=
  ∀ (jN : J → L.ι) (jL : L'.ι),
    res (mapsAtExp_le_b L L' pr ε p jN jL) (b.s jN) =
      (pullU p _ (w.s (jN, jL))) ^ n * res (mapsAtExp_le_a L L' pr ε p jN jL) (a.s (fun _ => jL))

end Maps

variable {R : Type} [CommRing R] [IsDomain R]

def twφ (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A) : Fin 3 → (D₀.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A β (toUnit D₀.P.A ≫ b)).left, (toUnit D₀.P.A ≫ b).left, (toUnit D₀.P.A ≫ η[D.P.A]).left]

def twε : Fin 3 → ℤ := ![1, -1, 1]

def IsTwist (D₀ D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) : Prop :=
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ w : LB.Iso D₀.P.L (LB.LinComb D.P.L (twφ D₀ D β.hom g.b) twε), w.IsGen ∧
      ∀ χ : D₀.X, ∃ t : LB.Gen (LB.LinComb D.P.L (fun i => D₀.xK χ ≫ twφ D₀ D β.hom g.b i) (fun i => -1 * twε i)),
        MapsAtExp D.P.L D₀.P.L (twφ D₀ D β.hom g.b) twε w (D₀.xK χ) (-1) (D₀.psi χ) t ∧
        LB.Gen.Corr D.P.L _ _ _ _ t
          (LB.mulGen D.P.L _ _ _ _ (D.psi (xe χ)) (LB.pullGen D.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left))

end GlobalTheory.MumCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic

namespace GlobalTheory.Mum.PowData

def AdjCls {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] [GrpObj G₀] (c : Pic G.left) (c₀ : Pic G₀.left) (q : G ⟶ G₀)
    (j : G₀ ⟶ G) : Prop :=
  ∀ (T : Over S) (x : T ⟶ G) (z : T ⟶ G₀), lam c x (z ≫ j) = lam c₀ (x ≫ q) z

variable {R : Type} [CommRing R] [IsDomain R]

def PrimVal (D : DegPre R) (f : D.P.A ⟶ D.P.A) (m : D.X → D.X) : Prop :=
  ∃ u : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(padd D.P.A (𝟙 _) f).left, 𝟙 D.P.A.left, f.left, (toUnit D.P.A ≫ η[D.P.A]).left] ![1, -2, -1, 2]),
    u.IsGen ∧ ∀ y, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau y (m y)) (LB.pullGen D.P.L _ _ u (D.xK y))) (LB.mulGen D.P.L _ _ _ _ (D.psi y) D.rigK)

theorem isPrimitiveValue_of_ringElement_psiRelation {O : Type} [CommRing O] [StarRing O] {D : DegPre R} [Module O D.X] {o : D.OAct O} {w : O}
    (h : TraceFormTwistIso D o w) : PrimVal D (o.onB.act w) (fun y => w • y) :=
  h.imp fun _ h => ⟨h.1, h.2.2⟩

def Expand (D : DegPre R) {K : Type} [Fintype K] (n : K → ℤ) {T : Over (Sp R)} (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)) : Prop :=
  ∃ κ : LB.Gen (LB.LinComb D.P.L (Sum.elim (lamPts x (∏ i, y i ^ n i)) (fun k : K × Fin 4 => lamPts x (y k.1) k.2))
      (Sum.elim Oε (fun k : K × Fin 4 => -(n k.1 * Oε k.2)))),
    κ.IsGen ∧ ∀ (p : TK R ⟶ T) (a : D.X) (b : K → D.X), p ≫ x = toUnit _ ≫ D.c a → (∀ i, p ≫ y i = toUnit _ ≫ D.c (b i)) →
      ∀ z J, Good D.P.L z J →
        val (D.tau a (∑ i, n i • b i)) (𝟙 _) z J * val κ p.left z J = ∏ i, val (D.tau a (b i)) (𝟙 _) z J ^ n i

def CmpTwo (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A) : Prop :=
  ∃ Γ : LB.Gen (LB.LinComb (JN D D₀)
      (Sum.elim (fun k => lamPts (fst D.P.A D₀.P.A) (snd D.P.A D₀.P.A ≫ j) k ≫ coprod.inl)
        (fun k => lamPts (fst D.P.A D₀.P.A ≫ q) (snd D.P.A D₀.P.A) k ≫ coprod.inr)) (Sum.elim Oε Oinvε)),
    Γ.IsGen ∧ ∀ (χ' : D.X) (χ : D₀.X), D.c χ' = D₀.c χ ≫ j → ∀ u : LB.Gen (CmpLB D D₀ q χ' χ), Nrm u →
      ∀ (T : Over (Sp R)) (x : T ⟶ D.P.A) (z : T.left) (J), Good (JN D D₀) z J →
        val u x.left z J = val Γ (lift x (toUnit T ≫ D₀.c χ)).left z J

def PeriodRel (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (h : D₀.X → D.X) (k : D.X → D₀.X) : Prop :=
  ∀ χ, ∃ u : LB.Gen (CmpLB D D₀ q (h χ) χ), Nrm u ∧ ∀ y z J, Good (JN D D₀) z J →
    val (D₀.tau (k y) χ) (𝟙 _) z (rr J) = val (D.tau y (h χ)) (𝟙 _) z (rl J) * val u (ptK (D.c y)) z J

section Points

variable {S : Scheme.{0}} {T T' G G' : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K]

theorem comp_prod_zpow (p : T' ⟶ T) (y : K → (T ⟶ G)) (n : K → ℤ) : p ≫ ∏ i, y i ^ n i = ∏ i, (p ≫ y i) ^ n i := by
  let f : (T ⟶ G) →* (T' ⟶ G) := MonoidHom.mk' (fun a => p ≫ a) fun a b => MonObj.comp_mul p a b
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

theorem prod_zpow_comp [GrpObj G'] [IsCommMonObj G'] (y : K → (T ⟶ G)) (n : K → ℤ) (g : G ⟶ G') [IsMonHom g] :
    (∏ i, y i ^ n i) ≫ g = ∏ i, (y i ≫ g) ^ n i := by
  let f : (T ⟶ G) →* (T ⟶ G') := MonoidHom.mk' (fun a => a ≫ g) fun a b => MonObj.mul_comp a b g
  exact (map_prod f _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow f _ _)

end Points

end GlobalTheory.Mum.PowData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.ThPull
open GlobalTheory.ThetaPtMove

theorem thG_pull {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left}
    {ρ : LB.Gen (L.pull (eSec G))} (hL : L.IsLB) (hρ : ρ.IsGen) {m : ℕ}
    {B T : Over S} (β : B ⟶ T) {θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)} {y : T ⟶ G} {c : Γ(T.left, ⊤)}
    (H : ThG G L ρ m θ y c) : ThG G L ρ m (VVRank.pullS G _ β θ) (β ≫ y) (β.left.appTop.hom c) := by
  have hp : IsGrpPullback G G (𝟙 _) (𝟙 G.left) :=
    @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G) (inferInstanceAs (IsMonHom (𝟙 G)))
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 _)) :=
    (GlobalTheory.PolBaseChange.lbIso_refl hL).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)
  obtain ⟨ρ', -, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL hρ
  have hτ : β.left ≫ T.hom = B.hom ≫ 𝟙 S := by rw [Over.w, Category.comp_id]
  have hσ : 𝟙 B.left ≫ B.hom = B.hom ≫ 𝟙 S := by simp
  obtain ⟨t, ht⟩ := exists_secRel hp β.left hτ hw hL hL θ
  have hu : (β ≫ y) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, H.1, MonObj.comp_one]
  have hrel := secRel_smul hp β.left hτ (𝟙 B.left) hσ β (Category.id_comp _) ht
    (th' := VVRank.pullS G _ β θ) (c := 1) (one_smul _ _).symm
  have q := ThG.smul (th' := SecM.toSec G ((𝟙 B.left : B.left ⟶ B.left).appTop.hom 1 • SecM.ofSec G t)) hL rfl
    (ThG.move hp β.left hτ hw hL hL hr (x := β ≫ y) (by simp) hu ht H)
  have q' := ThG.up hp (𝟙 B.left) hσ hw hL hL hr (x₀ := β ≫ y) (by simp) hu hrel q
  simpa using q'

theorem thList_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (m N : ℕ) (K K' : Type) [Field K] [Field K'] (i : K →+* K') (x : Sp K ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c → ∃ pt' : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), (∀ a, (pt' a).left = spMap i ≫ (pt a).left) ∧ ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt' (fun a => i (c a)) := by
  intro S G _ _ L ρ hL hρ m N K K' _ _ i x θ pt c H
  let β : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hβ : β.left = spMap i := Over.homMk_left _ _
  refine ⟨fun a => β ≫ pt a, fun a => by simp only [Over.comp_left, hβ], fun a b h => H.1 (TorsionFieldExt.comp_injective β _ h), fun a => ?_,
    fun F _ _ k => ?_⟩
  · have q := thG_pull hL hρ β (H.2.1 a)
    have e : β.left.appTop.hom (GlobalTheory.ZH.fn (c a)) = GlobalTheory.ZH.fn (i (c a)) :=
      (congrArg (fun q => q.hom (c a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
    rw [e] at q
    exact q
  · have e : spMap k ≫ spMap i ≫ x = spMap (k.comp i) ≫ x := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc]
    rw [e]
    intro p hp
    obtain ⟨a, ha⟩ := H.2.2 F (k.comp i) p hp
    refine ⟨a, ?_⟩
    rw [ha, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc, Over.comp_left, hβ, Category.assoc]

end GlobalTheory.UMin.ThPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaConstantListOfFibrePullbackFieldExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (m N : ℕ) (K K' : Type) [Field K] [Field K'] (i : K →+* K') (x : Sp K ⟶ S) (θ : SecAt G L x) (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c → ∃ pt' : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), (∀ a, (pt' a).left = spMap i ≫ (pt a).left) ∧ ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt' (fun a => i (c a)) := by
  first | exact @GlobalTheory.UMin.ThPull.thList_pull | exact GlobalTheory.UMin.ThPull.thList_pull | (intros; apply GlobalTheory.UMin.ThPull.thList_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Cmp

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

def LatTo {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (𝔪 : UMem X₁ z₁ act V ev X t δ) : Prop :=
  ∃ K : (Fin 8 → X₀) ≃+ (Fin 8 → X), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀),
      K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) ∧ ∀ a mu, 𝔪₀.YY a mu → 𝔪.YY a (K mu)


open Classical in
def ZHAbove (X₁ : Setup F W i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) : Prop :=
  ∃ (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J), Nonempty (ZHOut X₁.ρ Y U₀ EE) ∧ X₁.S.Over₀ Y U₀ ∧ X₁.S.IsEE Y U₀ EE ∧
    X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY

theorem LatTo.refl {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ) : LatTo 𝔪 𝔪 :=
  ⟨AddEquiv.refl _, fun _ _ => rfl, fun _ _ h => h⟩

theorem LatTo.trans {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁}
    {X₂ : Type} [AddCommGroup X₂] {m₁ : ℕ} {t₁ : Fin m₁ → V₁} {δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₂}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    {𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪₁ : UMem X₁ z₁ act V₁ ev₁ X₂ t₁ δ₁} {𝔪 : UMem X₁ z₁ act V ev X t δ}
    (h₀ : LatTo 𝔪₀ 𝔪₁) (h₁ : LatTo 𝔪₁ 𝔪) : LatTo 𝔪₀ 𝔪 := by
  obtain ⟨K₀, e₀, l₀⟩ := h₀
  obtain ⟨K₁, e₁, l₁⟩ := h₁
  refine ⟨K₀.trans K₁, fun a mu => ?_, fun a mu h => l₁ _ _ (l₀ _ _ h)⟩
  simp only [AddEquiv.trans_apply]
  rw [e₀, e₁]

end GlobalTheory.Poinc.Sep.Cmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEqOfRankAtStalk
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.ConjSeq

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymmPoincare

universe u

section Linear

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  {ψ : Module.Dual K V →ₗ[K] Module.Dual K V →ₗ[K] K} {β : V →ₗ[K] Module.Dual K V}

end Linear

section Swap

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A B : Over S} [GrpObj A] [GrpObj B]

theorem isCorrForm_swap {P : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) : IsCorrForm κ t B A (swap P) (-φ.flip) := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  have m : IsMor κ ((A ⊗ B).hom ≫ t) κ ((B ⊗ A).hom ≫ t) (RingHom.id R) (lift (snd B A) (fst B A)).left :=
    (homMor κ t (lift (snd B A) (fst B A))).isMor
  have k := isChern_pull m hc
  rw [crystallinePull2_sum_cup] at k
  refine ⟨n, fun i ↦ -b i, a, ?_, fun x y ↦ ?_⟩
  · convert k using 2 with i
    rw [pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, Submodule.coe_neg, map_neg, map_neg,
      LinearMap.neg_apply, neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)]
  · simp only [LinearMap.neg_apply, LinearMap.flip_apply, hφ, map_neg, ← Finset.sum_neg_distrib, neg_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

theorem isCorrForm_of_iso {P Q : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) : IsCorrForm κ t A B Q φ := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  exact ⟨n, a, b, (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ hP hQ e _ hc, hφ⟩

theorem skew_of_symm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB) (hs : LBIso (swap P) P)
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x :=
  LinearMap.congr_fun₂ (H.unique C hP (isCorrForm_of_iso (isCorrForm_swap H) (pull_isLB hP _) hP hs)) x y

end Swap

end GlobalTheory.SymmPoincare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentX
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentX
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_ext_of_isNilpotent :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ ψ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        (∀ i, φ (X i) = ψ (X i)) → φ = ψ := by
  intro k _ σ _ A _ _ φ ψ hφ h
  classical
  obtain ⟨N₁, h₁⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ A φ hφ
  obtain ⟨N₂, h₂⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ A ψ (fun i => h i ▸ hφ i)
  have hp : φ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) =
      ψ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [h i]
  have hm : ∀ (α : σ →₀ ℕ) (c : k), φ (monomial α c) = ψ (monomial α c) := by
    intro α c
    have := DFunLike.congr_fun hp (MvPolynomial.monomial α c)
    simpa [MvPolynomial.coe_monomial] using this
  have hfin : {α : σ →₀ ℕ | α.degree ≤ N₁ + N₂}.Finite := Finsupp.finite_of_degree_le _
  apply AlgHom.ext
  intro f
  set p : MvPowerSeries σ k := ∑ α ∈ hfin.toFinset, monomial α (coeff α f) with hpdef
  have hc : ∀ α : σ →₀ ℕ, α.degree ≤ N₁ + N₂ → coeff α (f - p) = 0 := by
    intro α hα
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, hpdef, map_sum, Finset.sum_eq_single α]
    · simp
    · intro β _ hβ
      rw [coeff_monomial_ne hβ.symm]
    · intro hn
      exact absurd (by simpa using hα) hn
  have e₁ : φ (f - p) = 0 := h₁ _ (fun α hα => hc α (by omega))
  have e₂ : ψ (f - p) = 0 := h₂ _ (fun α hα => hc α (by omega))
  have e₃ : φ p = ψ p := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hpdef, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun α _ => hm _ _)
  rw [map_sub, sub_eq_zero] at e₁ e₂
  rw [e₁, e₂, e₃]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentXStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ φ ψ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) → (∀ i, φ (X i) = ψ (X i)) → φ = ψ := by
  first | exact @GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent | exact GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent | (intros; apply GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.Two

theorem over₀_onTorus_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), (∀ b b' : D₁.toPre.P.A ⟶ D₂.toPre.P.A, Over₀ U₁ U₂ a b → Over₀ U₁ U₂ a b' → b = b') ∧ ∀ h h' : D₂.toPre.X → D₁.toPre.X, OnTorus U₁ U₂ a h → OnTorus U₁ U₂ a h' → h = h' := by
  intro R _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a
  refine ⟨fun b b' hb hb' => ?_, fun h h' hh hh' => ?_⟩
  · obtain ⟨_, -, -, _⟩ := hR
    have := D₁.toPre.P.isAb.smooth
    have := D₁.toPre.P.isAb.geomConnected
    have := D₁.toPre.P.isAb.proper
    have := D₂.toPre.P.isAb.proper
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I) D₁.toPre.P.A).2 _ b b'
      fun e => ?_
    have := (U₁.gt e).q_flat
    have := (U₁.gt e).q_surj
    have := (U₁.gt e).q_affine
    have := FlatQuotient.epi_of_flat_surjective (U₁.gt e).q
    have k := congrArg (fun q => q.left ≫ pullback.fst D₂.toPre.P.A.hom (thick R I e))
      ((cancel_epi _).1 ((hb e).symm.trans (hb' e)))
    exact (pullback.lift_fst _ _ _).symm.trans (k.trans (pullback.lift_fst _ _ _))
  · have := hR.2.2.2
    have := EndTorus.connectedSpace_thickening I 0
    have : Mono (U₂.gt 0).i := by
      have : Mono (η[thickObj R I 0 D₂.toPre.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
      exact (MorphismProperty.monomorphisms _).of_isPullback (U₂.gt 0).isKernel.flip (.infer_property _)
    obtain ⟨t, ht, e⟩ := hh 0
    obtain ⟨t', ht', e'⟩ := hh' 0
    obtain rfl : t = t' := (cancel_mono _).1 (e.symm.trans e')
    funext χ
    exact SplitTorusHom.charUnit_injective (S := Sp (R ⧸ I ^ (0 + 1)))
      (congrArg Units.val ((ht χ).symm.trans (ht' χ)))

end GlobalTheory.Mum.Two
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroupHom_induced_maps_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), (∀ b b' : D₁.toPre.P.A ⟶ D₂.toPre.P.A, Over₀ U₁ U₂ a b → Over₀ U₁ U₂ a b' → b = b') ∧ ∀ h h' : D₂.toPre.X → D₁.toPre.X, OnTorus U₁ U₂ a h → OnTorus U₁ U₂ a h' → h = h' := by
  first | exact @GlobalTheory.Mum.Two.over₀_onTorus_unique | exact GlobalTheory.Mum.Two.over₀_onTorus_unique | (intros; apply GlobalTheory.Mum.Two.over₀_onTorus_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubset
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.GenericChart

theorem exists_isClosed_chart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∃ T : Set X, IsClosed T ∧ genericPoint X ∉ T ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), y.1 (IsLocalRing.closedPoint ℂ) ∉ T → ∃ c : AlgChart p σ D, y ∈ c.e.source := by
  intro k _ X _ p D h
  obtain ⟨U, hU, hη, t, ht⟩ := GlobalTheory.GenericCoords.exists_affine_etale_coords h
  refine ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl, fun h' => h' hη, fun σ y hy => ?_⟩
  obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale (σ := σ) hU t ht (y := y)
    (mem_ptsIn.2 (not_not.1 hy))
  exact ⟨c, hc⟩

end GlobalTheory.GenericChart
end
