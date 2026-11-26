module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleTwist
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Stab

open GlobalTheory.AdelicLatMove (mt_mul mt_one gram_mul_inv)

theorem isInt_mulVec {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hM : IntM O M) (hx : ∀ i, IsInt O (x i)) (i : Fin n) :
    IsInt O ((M *ᵥ x) i) :=
  isInt_iff.2 (show ∑ k, M i k * x k ∈ _ from
    sum_mem fun k _ => mul_mem (isInt_iff.1 (hM i k)) (isInt_iff.1 (hx k)))

theorem isInt_vecMul {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {x : Fin n → K} (hM : IntM O M) (hx : ∀ i, IsInt O (x i)) (i : Fin n) :
    IsInt O ((x ᵥ* M) i) :=
  isInt_iff.2 (show ∑ k, x k * M k i ∈ _ from
    sum_mem fun k _ => mul_mem (isInt_iff.1 (hx k)) (isInt_iff.1 (hM k i)))

theorem map_mulVec' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (y : Fin n → R) : (fun i => f ((M *ᵥ y) i)) = M.map f *ᵥ fun i => f (y i) :=
  funext fun i => RingHom.map_mulVec f M y i

theorem dual_move {R K : Type} [CommRing R] [Field K] (c : R →+* R) (π : R →+* K) {n : ℕ}
    (G M N : Matrix (Fin n) (Fin n) R) (β : GL (Fin n) K) (h : G * N = (M.map c)ᵀ * G) (y : Fin n → R) :
    (fun i => π (c ((M *ᵥ y) i))) ᵥ* (G.map π * β.1) =
      ((fun i => π (c (y i))) ᵥ* (G.map π * β.1)) ᵥ* ((β⁻¹).1 * N.map π * β.1) := by
  have hG : G.map π * N.map π = (M.map (π.comp c))ᵀ * G.map π := by
    rw [← Matrix.map_mul, h, Matrix.map_mul]
    rfl
  have hc := map_mulVec' (π.comp c) M y
  simp only [RingHom.comp_apply] at hc
  rw [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ β.1,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, hG, Matrix.mul_assoc,
    ← Matrix.vecMul_mulVec, hc]

theorem split_move {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (a b : R)
    (M : Matrix (Fin n) (Fin n) R) (h : ∀ i j, (a + b) * (M - 1) i j = (M - 1) i j) (y : Fin n → R) :
    (M.map f *ᵥ fun i => f (y i)) = ((fun i => f (a * (M *ᵥ y) i)) + fun i => f (b * (M *ᵥ y) i)) +
      (((fun i => f (y i)) - fun i => f (a * y i)) - fun i => f (b * y i)) := by
  have h1 : (a + b) • (M - 1) = M - 1 := Matrix.ext fun i j => h i j
  have h3 : (a + b) • (M *ᵥ y - y) = M *ᵥ y - y := by
    have := congrArg (· *ᵥ y) h1
    simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
  rw [← map_mulVec']
  funext i
  have h4 : (a + b) * ((M *ᵥ y) i - y i) = (M *ᵥ y) i - y i := congrFun h3 i
  simp only [Pi.add_apply, Pi.sub_apply, ← map_add (f := _), ← map_sub]
  congr 1
  linear_combination -h4

variable {D : D7}

theorem finPart_surj (z : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ a : AE D, finPart D a = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul α x => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

theorem idem_mul_mem (V : HSp D) {a : AE D} (ha : a * a = a) {y : Fin V.rank → AE D}
    (hy : (fun i => finPart D (y i)) ∈ LamHat V) : (fun i => finPart D (a * y i)) ∈ LamHat V := by
  let Λ := GlobalTheory.PlaceModel.latFrame V
  have hs : ∀ b ∈ intAE D, ∀ z ∈ latHat D.host.F D.host.E
      (Λ : Set (Fin V.rank → D.host.E)),
      (fun i => b * z i) ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) := by
    intro b hb z hz
    change z ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) at hz
    change _ ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E))
    induction hb using AddSubgroup.closure_induction with
    | mem b hb =>
      obtain ⟨s, hs, o, rfl⟩ := hb
      induction hz using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨t, ht, x, hx, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨s * t, fun v => mul_mem (hs v) (ht v), o • x,
          Λ.smul_mem o hx, ?_⟩
        funext i
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rfl
      | zero =>
        simp only [Pi.zero_apply, mul_zero]
        exact zero_mem _
      | add u w _ _ hu hw =>
        simp only [Pi.add_apply, mul_add]
        exact add_mem hu hw
      | neg u _ hu =>
        simp only [Pi.neg_apply, mul_neg]
        exact neg_mem hu
    | zero =>
      simp only [zero_mul]
      exact zero_mem _
    | add u w _ _ hu hw =>
      simp only [add_mul]
      exact add_mem hu hw
    | neg u _ hu =>
      simp only [neg_mul]
      exact neg_mem hu
  have h := hs (finPart D a)
    (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
    (fun i => finPart D (y i)) (by rw [GlobalTheory.PlaceModel.coe_latFrame]; exact hy)
  rw [GlobalTheory.PlaceModel.coe_latFrame] at h
  simpa only [RingHom.map_mul] using h

theorem finMat_eq (V : HSp D) (g : GA D V) : finMat D.sp.cm.sig V.gram g = (mt V g).map (finPart D) := rfl

theorem suppAt_inv {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  have h : (e + cA D e) • (mt V g - 1) = mt V g - 1 := Matrix.ext fun i j => hg i j
  have h1 : mt V g⁻¹ - 1 = -((mt V g - 1) * mt V g⁻¹) := by
    rw [Matrix.sub_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, neg_sub]
  have h2 : (e + cA D e) • (mt V g⁻¹ - 1) = mt V g⁻¹ - 1 := by
    rw [h1, smul_neg, ← Matrix.smul_mul, h]
  exact fun i j => congrFun (congrFun h2 i) j

theorem mem_GfC {e : AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt V g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

variable {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} {V : HSp D}
  {β : GL (Fin V.rank) (Fv D.host.F v)}

theorem intM_of_stable (hπ : Chart e v π) (hβ : Frame V e π β) {g : GA D V}
    (h : ∀ y ∈ LamHat V, finMat D.sp.cm.sig V.gram g *ᵥ y ∈ LamHat V) : IntM (Ov D v) (rho V π β g).1 := by
  intro i j
  choose y hy using fun k => hπ.1 (β.1 k j)
  have hcol : (fun k => π (y k)) = β.1 *ᵥ Pi.single j 1 := by
    funext k
    rw [hy, Matrix.mulVec_single_one]
    rfl
  have h1 := (hβ y).2 fun k => by
    rw [hcol, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mulVec_single_one]
    exact intM_one k j
  have h2 := h _ h1
  rw [finMat_eq, ← map_mulVec'] at h2
  have h3 : mt V g *ᵥ (fun k => e * y k) = fun k => e * (mt V g *ᵥ y) k := Matrix.mulVec_smul _ e y
  rw [h3] at h2
  have h4 := (hβ _).1 h2 i
  rw [map_mulVec', hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h4
  rw [rho_val]
  exact h4

theorem stable_of_intM (he : IsSplitIdem D e) (hβ : Frame V e π β)
    (hd : ∀ y : Fin V.rank → AE D, (fun i => finPart D (cA D e * y i)) ∈ LamHat V ↔ ∀ j, IsInt (Ov D v)
      (((fun i => π (cA D (y i))) ᵥ* ((V.gram.map fun a => π (incA D a)) * β.1)) j))
    {g : GA D V} (hg : SuppAt e V g) (h1 : IntM (Ov D v) (rho V π β g).1) (h2 : IntM (Ov D v) (rho V π β g⁻¹).1)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ LamHat V) :
    finMat D.sp.cm.sig V.gram g *ᵥ z ∈ LamHat V := by
  choose y hy using fun k => finPart_surj (z k)
  obtain rfl : z = fun k => finPart D (y k) := funext fun k => (hy k).symm
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have a1 := idem_mul_mem V he.1 hz
  have a2 := idem_mul_mem V he'.1 hz
  have b1 : (fun i => finPart D (e * (mt V g *ᵥ y) i)) ∈ LamHat V := by
    refine (hβ _).2 fun i => ?_
    have := isInt_mulVec h1 ((hβ y).1 a1) i
    rwa [rho_val, Matrix.mulVec_mulVec, Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← map_mulVec'] at this
  have b2 : (fun i => finPart D (cA D e * (mt V g *ᵥ y) i)) ∈ LamHat V := by
    refine (hd _).2 fun i => ?_
    have := isInt_vecMul h2 ((hd y).1 a2) i
    rw [rho_val] at this
    exact (congrFun (dual_move (cA D) π (V.gram.map (incA D)) _ _ β (gram_mul_inv V g) y) i).symm ▸ this
  rw [finMat_eq, split_move (finPart D) e (cA D e) (mt V g) hg y]
  exact add_mem (add_mem b1 b2) (sub_mem (sub_mem hz a1) a2)

theorem finMat_mul_inv (g : GA D V) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    finMat D.sp.cm.sig V.gram g *ᵥ (finMat D.sp.cm.sig V.gram g⁻¹ *ᵥ y) = y := by
  rw [finMat_eq, finMat_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.one_mulVec]

theorem mem_KsphC_iff_gInt : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ g : GA D V, SuppAt e V g → (g ∈ KsphC V ∅ ↔ GInt (Ov D v) (rho V π β g)) := by
  intro D e v π he hπ V β hβ g hg
  have hd := GlobalTheory.T.conj_mem_completedLattice_iff_dual_splitPlace e v π he hπ V β hβ
  unfold GInt
  rw [← map_inv]
  constructor
  · rintro ⟨-, h, -⟩
    exact ⟨intM_of_stable hπ hβ fun y hy => (h y).1 hy,
      intM_of_stable hπ hβ fun y hy => (h _).2 (by rw [finMat_mul_inv]; exact hy)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨mem_GfC he hg, fun y => ⟨stable_of_intM he hβ hd hg h1 h2 y, fun hy => ?_⟩,
      fun w hw => absurd hw (Finset.notMem_empty w)⟩
    have h3 := stable_of_intM he hβ hd (suppAt_inv hg) h2 (by rw [inv_inv]; exact h1) _ hy
    have h4 := finMat_mul_inv g⁻¹ y
    rw [inv_inv] at h4
    rwa [h4] at h3

end GlobalTheory.SplitHecke.Stab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (V : HSp D) (β : GL (Fin V.rank) (Fv D.host.F v)), Frame V e π β → ∀ g : GA D V, SuppAt e V g → (g ∈ KsphC V ∅ ↔ GInt (Ov D v) (rho V π β g)) := by
  first | exact @GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt | exact GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt | (intros; apply GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueEqOfGenerators
namespace GlobalTheory.ClassResidueGenerators

theorem residue_eq_of_generators {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A]
    (S : Set A) (ψ ψ' : ↥(Algebra.adjoin O S) →ₐ[O] O)
    (h : ∀ (a : A) (ha : a ∈ S),
      IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin ha⟩) =
        IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin ha⟩))
    (x : A) (hx : x ∈ Algebra.adjoin O S) :
    IsLocalRing.residue O (ψ ⟨x, hx⟩) = IsLocalRing.residue O (ψ' ⟨x, hx⟩) := by
  induction hx using Algebra.adjoin_induction with
  | mem a ha => exact h a ha
  | algebraMap r =>
    have e : (⟨algebraMap O A r, Subalgebra.algebraMap_mem _ r⟩ : ↥(Algebra.adjoin O S)) =
        algebraMap O _ r := rfl
    rw [e, ψ.commutes, ψ'.commutes]
  | add a b ha hb iha ihb =>
    have e : (⟨a + b, add_mem ha hb⟩ : ↥(Algebra.adjoin O S)) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), iha, ihb]
  | mul a b ha hb iha ihb =>
    have e : (⟨a * b, mul_mem ha hb⟩ : ↥(Algebra.adjoin O S)) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_mul, iha, ihb]

theorem cls_eq_of_generators : ∀ {O K V : Type} [inst : CommRing O] [inst_1 : Field K] [inst_2 : Algebra O K] [inst_3 : AddCommGroup V] [inst_4 : Module K V] [inst_5 : Module O V] [inst_6 : IsScalarTower O K V] [inst_7 : IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : ↥(Algebra.adjoin O S) →ₐ[O] O), (∀ (a : Module.End K V) (h : a ∈ S), (IsLocalRing.residue O : O → IsLocalRing.ResidueField O) ((ψ : ↥(Algebra.adjoin O S) → O) (⟨a, Algebra.subset_adjoin h⟩ : ↥(Algebra.adjoin O S))) = (IsLocalRing.residue O : O → IsLocalRing.ResidueField O) ((ψ' : ↥(Algebra.adjoin O S) → O) (⟨a, Algebra.subset_adjoin h⟩ : ↥(Algebra.adjoin O S)))) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  intro O K V _ _ _ _ _ _ _ _ S ψ ψ' h
  unfold Formalism.L2.NCov.cls
  congr 1
  ext ⟨x, hx⟩
  exact residue_eq_of_generators S ψ ψ' h x hx

end GlobalTheory.ClassResidueGenerators
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem residue_map_equiv {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R ≃+* R') {a b : R} (h : IsLocalRing.residue R a = IsLocalRing.residue R b) :
    IsLocalRing.residue R' (φ a) = IsLocalRing.residue R' (φ b) := by
  have h' : IsLocalRing.residue R (a - b) = 0 := by rw [map_sub, h, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at h'
  rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  refine (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_)
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 h') ((isUnit_map_iff φ _).1 hu)

theorem heckeD_add (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W]
    [Module ℂ W] (J : Subgroup (Formalism.AUTREP.GAf L n)) (Dset : Set (Formalism.AUTREP.GAf L n))
    (hfin : ((fun x : Formalism.AUTREP.GAf L n => (x : Formalism.AUTREP.GAf L n ⧸ J)) '' Dset).Finite)
    (c : ℂ) (f f' : Formalism.AUTREP.GAf L n → W) :
    Formalism.L2.NG.heckeD J Dset (c • f + f') = c • Formalism.L2.NG.heckeD J Dset f + Formalism.L2.NG.heckeD J Dset f' := by
  classical
  funext g
  have hsub : ∀ F : Formalism.AUTREP.GAf L n → W,
      Function.support (fun cc : Formalism.AUTREP.GAf L n ⧸ J =>
        if hc : ∃ x ∈ Dset, (x : Formalism.AUTREP.GAf L n ⧸ J) = cc then F (g * hc.choose) else 0) ⊆
        (hfin.toFinset : Set (Formalism.AUTREP.GAf L n ⧸ J)) := by
    intro F cc hcc
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    apply hcc
    dsimp only
    rw [dite_eq_right]
    rintro ⟨x, hx, rfl⟩
    exact hn ⟨x, hx, rfl⟩
  rw [Pi.add_apply, Pi.smul_apply]
  simp only [Formalism.L2.NG.heckeD]
  rw [finsum_eq_sum_of_support_subset _ (hsub _), finsum_eq_sum_of_support_subset _ (hsub _),
    finsum_eq_sum_of_support_subset _ (hsub _), Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun cc _ => ?_
  split_ifs <;> simp

theorem cls_eq_of_residue : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] (S : Set (Module.End K V)) (ψ ψ' : Algebra.adjoin O S →ₐ[O] O), (∀ a (h : a ∈ S), IsLocalRing.residue O (ψ ⟨a, Algebra.subset_adjoin h⟩) = IsLocalRing.residue O (ψ' ⟨a, Algebra.subset_adjoin h⟩)) → Formalism.L2.NCov.cls ψ = Formalism.L2.NCov.cls ψ' := by
  first
  | exact @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators
  | (apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClassResidueGenerators.cls_eq_of_generators ..)

theorem pt_of_eigvec : ∀ {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (S : Set (Module.End K V)) (e : V), e ≠ 0 → Function.Injective (algebraMap O K) → (∀ a ∈ S, ∃ c : O, a e = algebraMap O K c • e) → ∃ ψ : Algebra.adjoin O S →ₐ[O] O, (∀ t : Algebra.adjoin O S, (t : Module.End K V) e = algebraMap O K (ψ t) • e) ∧ e ∈ Formalism.L2.NCov.W (Algebra.adjoin O S) (Formalism.L2.NCov.pt ψ) := by
  intro O K V _ _ _ _ _ _ _ S e he hinj hS
  have key : ∀ t ∈ Algebra.adjoin O S, ∃ c : O, t e = algebraMap O K c • e := by
    intro t ht
    induction ht using Algebra.adjoin_induction with
    | mem a ha => exact hS a ha
    | algebraMap r => exact ⟨r, by rw [Formalism.L2.NCov.algebraMap_end_eq]; simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 + c2, by rw [LinearMap.add_apply, h1, h2, map_add (f := _), add_smul]⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨c1, h1⟩ := iha
      obtain ⟨c2, h2⟩ := ihb
      exact ⟨c1 * c2, by rw [Module.End.mul_apply, h2, map_smul, h1, smul_smul, map_mul, mul_comm]⟩
  choose f hf using fun t : Algebra.adjoin O S => key t t.2
  have uniq : ∀ c c' : O, algebraMap O K c • e = algebraMap O K c' • e → c = c' :=
    fun c c' hcc => hinj (smul_left_injective K he hcc)
  have f1 : f 1 = 1 := uniq _ _ (by rw [← hf 1, map_one, one_smul]; rfl)
  have fm : ∀ s t, f (s * t) = f s * f t := fun s t => uniq _ _ (by
    rw [← hf (s * t), map_mul, mul_comm, mul_smul, ← hf s, ← map_smul, ← hf t]; rfl)
  have f0 : f 0 = 0 := uniq _ _ (by rw [← hf 0, map_zero, zero_smul]; rfl)
  have fa : ∀ s t, f (s + t) = f s + f t := fun s t => uniq _ _ (by
    rw [← hf (s + t), map_add (f := _), add_smul, ← hf s, ← hf t]; rfl)
  have fc : ∀ r, f (algebraMap O (Algebra.adjoin O S) r) = r := fun r => uniq _ _ (by
    rw [← hf]
    show (algebraMap O (Module.End K V) r) e = _
    rw [Formalism.L2.NCov.algebraMap_end_eq]; simp)
  let ψ : Algebra.adjoin O S →ₐ[O] O :=
    { toFun := f, map_one' := f1, map_mul' := fm, map_zero' := f0, map_add' := fa, commutes' := fc }
  refine ⟨ψ, fun t => hf t, ?_⟩
  refine (Submodule.mem_iInf _).2 fun t => ?_
  rw [Module.End.mem_maxGenEigenspace]
  refine ⟨1, ?_⟩
  simp only [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Formalism.L2.NCov.pt]
  rw [hf t]
  exact sub_self _

theorem descent : ∀ {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type} (Mg : G → Matrix ι ι K) (d : ι → C), d ≠ 0 → (∀ g, Matrix.mulVec ((Mg g).map φ) d = 0) → ∃ c : ι → K, c ≠ 0 ∧ ∀ g, Matrix.mulVec (Mg g) c = 0 := by
  intro K C _ _ φ ι _ G Mg d hd hdg
  classical
  by_contra hne
  push_neg at hne
  let kerS : Finset G → Submodule K (ι → K) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))
  have hex : ∃ m, ∃ s : Finset G, Module.finrank K (kerS s) = m := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin : ∀ s' : Finset G, Module.finrank K (kerS s) ≤ Module.finrank K (kerS s') := fun s' =>
    hs ▸ Nat.find_min' hex ⟨s', rfl⟩
  have hbot : kerS s = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [Submodule.mem_bot]
    by_contra hc0
    obtain ⟨g, hg⟩ := hne c hc0
    have hins : kerS (insert g s) = LinearMap.ker (Matrix.mulVecLin (Mg g)) ⊓ kerS s := by
      simp only [kerS, Finset.iInf_insert]
    have hle : kerS (insert g s) ≤ kerS s := by rw [hins]; exact inf_le_right
    have heq := Submodule.eq_of_le_of_finrank_le hle (hmin _)
    have hc' : c ∈ kerS (insert g s) := heq ▸ hc
    rw [hins] at hc'
    exact hg (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hc').1)
  let R : Matrix (↥s × ι) ι K := fun p b => Mg p.1.1 p.2 b
  have hinjR : Function.Injective (Matrix.toLin' R) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [← hbot]
    simp only [kerS, Submodule.mem_iInf, LinearMap.mem_ker]
    intro g hg
    funext a
    have hc' : Matrix.mulVec R c = 0 := by rw [← Matrix.toLin'_apply]; exact LinearMap.mem_ker.1 hc
    have := congrFun hc' (⟨g, hg⟩, a)
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, R] using this
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' R) (LinearMap.ker_eq_bot.2 hinjR)
  have hLR : LinearMap.toMatrix' Ψ * R = 1 := by
    have := congrArg LinearMap.toMatrix' hΨ
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at this
  have hLRC : (LinearMap.toMatrix' Ψ).map φ * R.map φ = 1 := by
    rw [← Matrix.map_mul, hLR, Matrix.map_one φ φ.map_zero φ.map_one]
  have hRd : Matrix.mulVec (R.map φ) d = 0 := by
    funext p
    have := congrFun (hdg p.1.1) p.2
    simp only [Matrix.mulVec, dotProduct] at this
    exact this
  apply hd
  calc d = Matrix.mulVec ((LinearMap.toMatrix' Ψ).map φ * R.map φ) d := by rw [hLRC, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hRd, Matrix.mulVec_zero]

theorem coeff_monic_poly_sum {R : Type} [Semiring R] (n k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n) (c : ℕ → R) :
    (X ^ n + ∑ k' ∈ Finset.Icc 1 n, C (c k') * X ^ (n - k')).coeff (n - k) = c k := by
  rw [coeff_add, coeff_X_pow, if_neg (by omega), zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [coeff_C_mul_X_pow, if_pos rfl]
  · intro b hb hbk
    rw [coeff_C_mul_X_pow, if_neg]
    rw [Finset.mem_Icc] at hb
    omega
  · intro hk
    exact absurd (Finset.mem_Icc.2 ⟨hk1, hk2⟩) hk

theorem coeff_extract : ∀ {O : Type} [CommRing O] [IsLocalRing O] (ι : O →+* ℂ), Function.Injective ι → ∀ (n q : ℕ), IsUnit (q : O) → ∀ (p : O[X]) (lam : ℕ → ℂ) (t : ℕ → O), p.map ι = X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * lam k) * X ^ (n - k) → p.map (IsLocalRing.residue O) = (X ^ n + ∑ k ∈ Finset.Icc 1 n, C ((-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) * t k) * X ^ (n - k)).map (IsLocalRing.residue O) → ∀ k, 1 ≤ k → k ≤ n → ∃ a : O, ι a = lam k ∧ IsLocalRing.residue O a = IsLocalRing.residue O (t k) := by
  intro O _ _ ι hι n q hq p lam t h1 h2 k hk1 hk2
  set u : O := (-1 : O) ^ k * (q : O) ^ (k * (k - 1) / 2) with hu_def
  have hu : IsUnit u := ((isUnit_one.neg).pow k).mul (hq.pow _)
  have e1 : ι (p.coeff (n - k)) = ι u * lam k := by
    have := congrArg (fun P : ℂ[X] => P.coeff (n - k)) h1
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1) ^ k' * (q : ℂ) ^ (k' * (k' - 1) / 2) * lam k')]
    simp [u]
  have e2 : IsLocalRing.residue O (p.coeff (n - k)) = IsLocalRing.residue O (u * t k) := by
    have := congrArg (fun P : (IsLocalRing.ResidueField O)[X] => P.coeff (n - k)) h2
    simp only [coeff_map] at this
    rw [this, coeff_monic_poly_sum n k hk1 hk2 (fun k' => (-1 : O) ^ k' * (q : O) ^ (k' * (k' - 1) / 2) * t k')]
  refine ⟨↑hu.unit⁻¹ * p.coeff (n - k), ?_, ?_⟩
  · rw [map_mul, e1, ← mul_assoc, ← map_mul, hu.val_inv_mul, map_one, one_mul]
  · rw [map_mul, e2, ← map_mul, ← mul_assoc, hu.val_inv_mul, one_mul]

theorem normV_unit : ∀ (D : D7) (i : D.nd.Loc) (w : PlE D.host), w ∉ placesOver D.host.E (D.nd.l i) → IsUnit (((normV w : ℕ) : D.nd.O i)) := by
  intro D i w hw
  classical
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hN : ¬ (D.nd.l i) ∣ normV w := by
    intro hdvd
    letI := Ideal.Quotient.field w.asIdeal
    haveI : Finite (𝓞 D.host.E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    letI := Fintype.ofFinite (𝓞 D.host.E ⧸ w.asIdeal)
    obtain ⟨p, hchar⟩ := CharP.exists (𝓞 D.host.E ⧸ w.asIdeal)
    have hp : p.Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ w.asIdeal) p
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 D.host.E ⧸ w.asIdeal) p
    have hcard : normV w = p ^ (n : ℕ) := by rw [normV, Nat.card_eq_fintype_card, hn]
    rw [hcard] at hdvd
    have hlp : D.nd.l i = p := (Nat.prime_dvd_prime_iff_eq hl hp).1 (hl.dvd_of_dvd_pow hdvd)
    apply hw
    show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, hlp]
    exact CharP.cast_eq_zero _ p
  have hu : IsUnit ((normV w : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).2 hN
  have := hu.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  rwa [map_natCast] at this

end GlobalTheory.PtLocalEig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReprMemOfBasisRational
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCmComplexOfPow
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresRat

def conjAlg : algebraicClosure ℚ ℂ →+* algebraicClosure ℚ ℂ :=
  ((starRingEnd ℂ).comp (algebraicClosure ℚ ℂ).val.toRingHom).codRestrict (algebraicClosure ℚ ℂ) fun x => by
    have hx : IsAlgebraic ℚ (x : ℂ) := mem_algebraicClosure_iff.1 x.2
    exact mem_algebraicClosure_iff.2 (hx.algHom (starRingEnd ℂ).toRatAlgHom)

def cmComplex : Subfield ℂ :=
  (⨅ τ : algebraicClosure ℚ ℂ →+* ℂ, RingHom.eqLocusField (τ.comp conjAlg) ((starRingEnd ℂ).comp τ)).map
    (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_cmComplex {z : ℂ} : z ∈ cmComplex ↔ ∃ x : algebraicClosure ℚ ℂ, (x : ℂ) = z ∧
    ∀ τ : algebraicClosure ℚ ℂ →+* ℂ, τ (conjAlg x) = starRingEnd ℂ (τ x) := by
  unfold cmComplex
  rw [Subfield.mem_map]
  refine exists_congr fun x => ?_
  rw [Subfield.mem_iInf, and_comm]
  rfl

theorem conj_eq_inv_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : starRingEnd ℂ z = z⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz hn.ne')).symm

theorem mem_cmComplex_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ cmComplex := by
  have ha : IsAlgebraic ℚ z := IsAlgebraic.of_pow hn (by rw [hz]; exact isAlgebraic_one)
  refine mem_cmComplex.2 ⟨⟨z, mem_algebraicClosure_iff.2 ha⟩, rfl, fun τ => ?_⟩
  set x : algebraicClosure ℚ ℂ := ⟨z, mem_algebraicClosure_iff.2 ha⟩
  have hx : x ^ n = 1 := Subtype.ext hz
  have h1 : conjAlg x = x⁻¹ := Subtype.ext (conj_eq_inv_of_pow hn hz)
  rw [h1, map_inv₀, conj_eq_inv_of_pow hn (by rw [← map_pow, hx, map_one])]

theorem mem_cmComplex_iff {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (a : K) : σ a ∈ cmComplex ↔ a ∈ cmMax K := by
  let s : K →+* algebraicClosure ℚ ℂ := σ.codRestrict (algebraicClosure ℚ ℂ) fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  have hs : conjAlg (s a) = s (star a) := Subtype.ext (hσ a).symm
  rw [mem_cmComplex]
  constructor
  · rintro ⟨x, hx, h⟩ φ
    have hx' : x = s a := Subtype.ext hx
    let _ : Algebra K (algebraicClosure ℚ ℂ) := s.toAlgebra
    have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := by
      convert algebraicClosure.isAlgebraic ℚ ℂ
    have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) K
    have h1 := h (ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ)
    rw [hx', hs] at h1
    have e : ∀ b, ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ (s b) = φ b := fun b =>
      ComplexEmbedding.lift_algebraMap_apply _ φ b
    rw [e, e] at h1
    exact h1
  · intro h
    exact ⟨s a, rfl, fun τ => by rw [hs]; exact h (τ.comp s)⟩

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem act_mem (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1)
    (hρ : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i))
    (k : J) (γ : Γ) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    (PresBasic.bW P).repr ((χ k : ℂ) • ρ γ (P.coef x)) i ∈ cmComplex := by
  obtain ⟨n, hn, hk⟩ := hχ k
  have h1 : (χ k : ℂ) ∈ cmComplex :=
    mem_cmComplex_of_pow hn (by rw [← Units.val_pow_eq_pow_val, hk, Units.val_one])
  have h2 : P.coef x = ∑ j, σ (S.bV.repr x j) • P.coef (S.bV j) := by
    conv_lhs => rw [← S.bV.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smulₛₗ]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h2]
  refine cmComplex.mul_mem h1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine cmComplex.sum_mem fun j _ => cmComplex.mul_mem ((mem_cmComplex_iff σ hσ _).2 (hx j)) ?_
  obtain ⟨c, hc, e⟩ := hρ γ j
  rw [e]
  simp only [← PresBasic.bW_apply]
  rw [Module.Basis.repr_sum_self]
  exact (mem_cmComplex_iff σ hσ _).2 (hc i)

end GlobalTheory.PresRat

namespace GlobalTheory

theorem classPres_dcOp_rat : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (A : Finset G) (T : Module.End K S.Forms), (∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) → (∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1) → (∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i)) → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ P A T hσ hχ hρ hT
  have hb : S.HasRatBasis := by
    refine (forms_rat S).1 fun c γ i j => ?_
    rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, P.coef_act]
    refine PresRat.act_mem P hσ hχ hρ _ _ _ (fun l => ?_) i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hb, (forms_rat S).2 T hb fun f hf c i => ?_⟩
  rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, ← PresBasic.ext_y P, hT]
  unfold dcOp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact PresRat.cmComplex.sum_mem fun a _ => PresRat.act_mem P hσ hχ hρ _ _ _ (hf _) i

end GlobalTheory
end
end

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeRational

open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open scoped TensorProduct

theorem repr_mem_of_basis_rational {K V ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ]
    (F : Subfield K) (b : Module.Basis ι K V) (b' : Module.Basis κ K V) (h : ∀ i j, b'.repr (b i) j ∈ F)
    (v : V) (hv : ∀ j, b'.repr v j ∈ F) (i : ι) : b.repr v i ∈ F := by
  obtain ⟨φ, h1, h2⟩ := FormsDescent.exists_retraction F
  have e2 : FormsDescent.coordMap F b' φ v = v := by
    apply b'.repr.injective
    ext j
    rw [FormsDescent.repr_coordMap, h2 _ (hv j)]
  have key : v = ∑ a, φ (b.repr v a) • b a := by
    rw [← FormsDescent.coordMap_sum F b' φ _ _ h, b.sum_repr, e2]
  have : b.repr v i = φ (b.repr v i) := by
    conv_lhs => rw [key]
    rw [b.repr_sum_self]
  rw [this]
  exact h1 _

theorem repr_map_mem {K V κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype κ]
    (F : Subfield K) (b : Module.Basis κ K V) (g : V →ₗ[K] V) (hg : ∀ i j, b.repr (g (b j)) i ∈ F)
    (v : V) (hv : ∀ j, b.repr v j ∈ F) (i : κ) : b.repr (g v) i ∈ F := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact F.sum_mem fun j _ => F.mul_mem (hv j) (hg i j)

theorem levFn_isOfFinOrder {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    IsOfFinOrder (levFn β L x) := by
  have hfin : ∀ PP : Pl E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hone : IsOfFinOrder (1 : ℂˣ) := IsOfFinOrder.one
  unfold levFn
  refine IsOfFinOrder.mul (IsOfFinOrder.mul ?_ ?_) ?_
  · unfold ext1
    split_ifs
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact hone
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun c _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

variable {D : D7}

theorem levEnv_chi_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).χ k ^ n = 1 :=
  isOfFinOrder_iff_pow_eq_one.1 (levFn_isOfFinOrder β (Lev.flag1L L) _)

theorem embE_mem_cmMax (x : D.host.E) : D.embE x ∈ cmMax D.what₂.LL := by
  intro σ
  rw [← D.embE_conj]
  exact D.host.conjE_apply (σ.comp D.embE) x

theorem labLL_mem_cmMax (τ : D.what₂.Tau) (x : D.host.E) : labLL D τ x ∈ cmMax D.what₂.LL := embE_mem_cmMax _

theorem action_rational (V : TH.HSp D) (C : CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Gf V)} {χ : J →* ℂˣ}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL) (γ : GQ V) (j : S.ιV) :
    ∃ c : S.ιV → D.what₂.LL, (∀ i, c i ∈ cmMax D.what₂.LL) ∧
      C.ρ γ (P.coef (S.bV j)) = ∑ i, D.what₂.embLL (c i) • P.coef (S.bV i) := by
  obtain ⟨e, hr, he, -⟩ := hP
  obtain ⟨γE, hγ⟩ : ∃ γE, IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  refine ⟨fun i => (S.bV.map e).repr (rho γE (e (S.bV j))) i, fun i => ?_, ?_⟩
  · exact repr_mem_of_basis_rational _ (S.bV.map e) (bVV D.what₂.LL lam) hr _
      (repr_map_mem _ _ _ (hrho γE) _ (hr j)) i
  · rw [he, ← hM.1 γ γE hγ]
    conv_lhs => rw [← (S.bV.map e).sum_repr (rho γE (e (S.bV j)))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he, LinearMap.map_smulₛₗ, Module.Basis.map_apply]

theorem dcOp_matrix_mem_cmMax (V : TH.HSp D) (C : CoefDat D V) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {S : CSD D.what₂.LL}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ (levEnv V β L).J (levEnv V β L).χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL)
    (B : Finset (Gf V)) (T : Module.End D.what₂.LL S.Forms)
    (hT : ∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) :
    S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax D.what₂.LL :=
  GlobalTheory.classPres_dcOp_rat (ratF V) S D.what₂.embLL C.ρ _ _ P B T D.starLL_cx (levEnv_chi_pow V β L)
    (action_rational V C P hP hM hrho) hT

theorem toMatrix_one_mem {K M ι : Type} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι] (F : Subfield K)
    (b : Module.Basis ι K M) (i j : ι) : LinearMap.toMatrix b b (1 : Module.End K M) i j ∈ F := by
  rw [LinearMap.toMatrix_one, Matrix.one_apply]
  split_ifs
  · exact F.one_mem
  · exact F.zero_mem

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (t : T) (B : Finset (Gf D.sp.X'))
    (U : Module.End D.what₂.LL (A.MtildeCSD t).Forms)
    (hU : ∀ f : (A.MtildeCSD t).Forms, (R.B.R t).pres.ext (U f).1 = dcOp B ((R.B.R t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax D.sp.X' R.cX.coef R.βX (R.datXt t) (R.B.R t).pres (hT.coefR t) hT.mapR
    (fun g i j => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i j).1) B U hU).2 a b

theorem lifts_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (j : Fin D.R.m) (t : T) (B : Finset (Gf (Vc D j)))
    (U : Module.End D.what₂.LL (A.MtCSD j t).Forms)
    (hU : ∀ f : (A.MtCSD j t).Forms, (R.B.L j t).pres.ext (U f).1 = dcOp B ((R.B.L j t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax (Vc D j) (R.cV j).coef (R.βV j) (R.datVt j t) (R.B.L j t).pres (hT.coefL j t) (hT.mapL j)
    (fun g i k => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i k).2) B U hU).2 a b

end GlobalTheory.HeckeRational

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceDiv

section Abstract

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem single_mem (j i : n) : (Pi.single j (1 : R) : n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simpa using O.one_mem
  · simpa [Pi.single_eq_of_ne h] using O.zero_mem

theorem exists_factor (P Q : Matrix n n R)
    (H : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ P.mulVec y = Q.mulVec z) :
    ∃ M : Matrix n n O, P = Q * M.map O.subtype := by
  choose z hz1 hz2 using fun j => H (Pi.single j 1) (single_mem O j)
  refine ⟨Matrix.of fun i j => ⟨z j i, hz1 j i⟩, ?_⟩
  ext i j
  have := congrFun (hz2 j) i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this]
  rfl

theorem mem_range_of_mul_eq_one (M N : Matrix n n O) (h : M.map O.subtype * N.map O.subtype = 1) :
    ∃ k ∈ (Formalism.UG.bc (n := n) O.subtype).range, k.1 = M.map O.subtype := by
  have h1 : M * N = 1 := by
    apply Matrix.map_injective O.subtype_injective
    simp only [Matrix.map_mul]
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  exact ⟨_, ⟨⟨M, N, h1, mul_eq_one_comm.1 h1⟩, rfl⟩, rfl⟩

theorem double_coset (B m T T' : Matrix n n R) (hT : T' * T = 1)
    (h1 : ∀ z : n → R, (∀ i, z i ∈ O) → ∀ i, B.mulVec z i ∈ O)
    (h2 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ y = B.mulVec z)
    (h3 : ∀ y : n → R, (∀ i, y i ∈ O) → ∃ z : n → R, (∀ i, z i ∈ O) ∧ m.mulVec y = (B * T).mulVec z)
    (h4 : ∀ z : n → R, (∀ i, z i ∈ O) → ∃ y : n → R, (∀ i, y i ∈ O) ∧ m.mulVec y = (B * T).mulVec z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := n) O.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := n) O.subtype).range,
      m = k₁.1 * T * k₂.1 := by
  obtain ⟨B0, hB0⟩ := exists_factor O B 1 fun y hy => ⟨_, h1 y hy, by rw [Matrix.one_mulVec]⟩
  rw [Matrix.one_mul] at hB0
  obtain ⟨C, hC⟩ := exists_factor O 1 B fun y hy => by rw [Matrix.one_mulVec]; exact h2 y hy
  obtain ⟨M, hM⟩ := exists_factor O m (B * T) h3
  obtain ⟨N, hN⟩ := exists_factor O (B * T) m fun z hz => (h4 z hz).imp fun y hy => ⟨hy.1, hy.2.symm⟩
  have hCB : C.map O.subtype * B = 1 := mul_eq_one_comm.1 hC.symm
  have hinv : T' * C.map O.subtype * (B * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ B, hCB, Matrix.one_mul, hT]
  have hMN : M.map O.subtype * N.map O.subtype = 1 := by
    have e : B * T * (M.map O.subtype * N.map O.subtype) = B * T := by
      rw [← Matrix.mul_assoc, ← hM, ← hN]
    calc _ = T' * C.map O.subtype * (B * T) * (M.map O.subtype * N.map O.subtype) := by
          rw [hinv, Matrix.one_mul]
      _ = 1 := by rw [Matrix.mul_assoc, e, hinv]
  obtain ⟨k₁, hk₁, e₁⟩ := mem_range_of_mul_eq_one O B0 C (by rw [← hB0, ← hC])
  obtain ⟨k₂, hk₂, e₂⟩ := mem_range_of_mul_eq_one O M N hMN
  exact ⟨k₁, hk₁, k₂, hk₂, by rw [e₁, e₂, ← hB0, hM]⟩

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sgT_mem_intA (v : HeightOneSpectrum (𝓞 F)) {y : Fv F v ⊗[F] E} (hy : y ∈ ordAt E v) :
    sgT E v y ∈ intA F E := by
  refine (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).2 fun w => ?_
  by_cases h : w = v
  · subst h; rwa [evF_sgT_self]
  · rw [evF_sgT_ne h]; exact zero_mem _

theorem sgT_mem_lamHat [StarRing E] (V : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    {y : Fin V.rank → Fv F v ⊗[F] E} (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v) :
    (fun i => sgT E v (y i)) ∈ lamHat F V := by
  refine (mem_lamHat_iff V _).2 fun w => ?_
  by_cases h : w = v
  · subst h; simpa only [evF_sgT_self] using hy
  · simp only [evF_sgT_ne h]; exact zero_mem _

omit [NumberField E] in
theorem evF_mulVec {n : Type} [Fintype n] (v : HeightOneSpectrum (𝓞 F)) {f : Af F ⊗[F] E} (hf : evF E v f = 1)
    (A : Matrix n n (Af F ⊗[F] E)) (z : n → Af F ⊗[F] E) :
    (fun a => evF E v (f * A.mulVec z a)) = (A.map (evF E v)).mulVec fun i => evF E v (z i) := by
  funext a
  rw [map_mul, hf, one_mul, RingHom.map_mulVec]
  rfl

theorem double_coset_of_divG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram), IsIdemOf E v e → IsFrameAt V v h → ϖ ≠ 0 → DivG hc V e ϖ d g → ∃ k₁ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, (h⁻¹ * locMat hc V v g * h).1 = k₁.1 * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i)) * k₂.1 := by
  intro F E _ _ _ _ _ _ hc V v e h ϖ d g he hh hϖ ⟨B, h1, h2, h3, h4⟩
  have he1 := he.2.1
  have hfr : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y i ∈ ordAt E v) →
      h.1.mulVec y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := fun y hy => by
    refine (hh _).2 ?_
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]; exact hy
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1.mulVec ((h⁻¹).1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1.mulVec (h.1.mulVec y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have key : ∀ y z : Fin V.rank → Af F ⊗[F] E,
      ((fun a => finP F E e * (finMat hc.sig V.gram g).mulVec y a) =
        fun a => finP F E e * B.mulVec (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) a) →
      (locMat hc V v g).1.mulVec (fun i => evF E v (y i)) =
        (B.map (evF E v) * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec fun i => evF E v (z i) := by
    intro y z hyz
    rw [locMat_val, ← evF_mulVec v he1, ← Matrix.mulVec_mulVec]
    have e2 : (Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i))).mulVec (fun i => evF E v (z i)) =
        fun i => evF E v (finP F E (inclR (AF F) (ϖ ^ d i)) * z i) := by
      funext i
      rw [Matrix.mulVec_diagonal, map_mul, evF_finP_incl]
    rw [e2, ← evF_mulVec v he1]
    funext a
    rw [congrFun hyz a]
  refine double_coset (ordAt E v) ((h⁻¹).1 * B.map (evF E v)) _ _
    (Matrix.diagonal fun i => inclR (Fv F v) (ϖ ^ d i)⁻¹) ?_ ?_ ?_ ?_ ?_
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i
    rw [← map_mul, inv_mul_cancel₀ (zpow_ne_zero _ hϖ), map_one]
  · intro z hz
    have := (mem_lamHat_iff V _).1 (h1 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)) v
    rw [evF_mulVec v he1] at this
    simp only [evF_sgT_self] at this
    rw [← Matrix.mulVec_mulVec]
    exact (hh _).1 this
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h2 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    rw [← Matrix.mulVec_mulVec, ← evF_mulVec v he1, ← hback' y]
    congr 1; funext a
    rw [← congrFun e2 a, map_mul, he1, one_mul, evF_sgT_self]
  · intro y hy
    obtain ⟨z, hz, e2⟩ := h3 _ (sgT_mem_lamHat V v (hfr y hy))
    refine ⟨fun i => evF E v (z i), fun i => (GlobalTheory.PlaceComp.IntLocal.mem_intA_iff F E _).1 (hz i) v, ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  · intro z hz
    obtain ⟨y, hy, e2⟩ := h4 (fun i => sgT E v (z i)) fun i => sgT_mem_intA v (hz i)
    refine ⟨(h⁻¹).1.mulVec fun i => evF E v (y i), (hh _).1 ((mem_lamHat_iff V _).1 hy v), ?_⟩
    have := key _ _ e2
    simp only [evF_sgT_self] at this
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec _ (h⁻¹).1, ← this, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hback]

end GlobalTheory.PlaceDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisorsStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localMatrix_doubleCoset_of_elementaryDivisors : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)) (ϖ : E) (d : Fin V.rank → ℤ) (g : HA (AF F) hc.sig V.gram), IsIdemOf E v e → IsFrameAt V v h → ϖ ≠ 0 → DivG hc V e ϖ d g → ∃ k₁ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range, (h⁻¹ * locMat hc V v g * h).1 = k₁.1 * Matrix.diagonal (fun i => inclR (Fv F v) (ϖ ^ d i)) * k₂.1 := by
  first | exact @GlobalTheory.PlaceDiv.double_coset_of_divG | exact GlobalTheory.PlaceDiv.double_coset_of_divG | (intros; apply GlobalTheory.PlaceDiv.double_coset_of_divG <;> assumption)
end
end
