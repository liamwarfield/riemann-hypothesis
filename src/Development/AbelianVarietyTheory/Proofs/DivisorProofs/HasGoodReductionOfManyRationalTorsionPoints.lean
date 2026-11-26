module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperOfInfinitelyManyLargeTorsionCounts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianReductionAlongIsogenyStrictHenselian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEqSumAevalBoundedIntCoeffAmpleStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GoodRedTorsion

def secHom {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] :
    (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback f).obj G) :=
  (GlobalTheory.RedPts.precomp _ (Functor.LaxMonoidal.ε (Over.pullback f))).comp (Over.pullback f).homMonoidHom

theorem secHom_apply {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (s : 𝟙_ (Over S) ⟶ G) :
    secHom f G s = GlobalTheory.IsogRed.sec f s := rfl

theorem card_le_of_fibres {M N : Type} [CommGroup M] [DecidableEq N] (TF : Finset M) (m c B : ℕ)
    (hT : ∀ a ∈ TF, a ^ m = 1) (F : M → N)
    (hF : ∀ a ∈ TF, ∀ b ∈ TF, F a = F b → a ^ c = b ^ c)
    (hfin : {x : M | x ^ Nat.gcd m c = 1}.Finite) (hB : {x : M | x ^ Nat.gcd m c = 1}.ncard ≤ B) :
    TF.card ≤ B * (TF.image F).card := by
  classical
  refine Finset.card_le_mul_card_image TF B fun y hy => ?_
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.1 hy
  calc (TF.filter fun x => F x = F a0).card ≤ hfin.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun a => a * a0⁻¹) ?_ ?_
        · intro a ha
          have ha' : a ∈ TF.filter fun x => F x = F a0 := by simpa using ha
          obtain ⟨haT, haF⟩ := Finset.mem_filter.1 ha'
          have h1 : (a * a0⁻¹) ^ m = 1 := by rw [mul_pow, inv_pow, hT a haT, hT a0 ha0]; simp
          have h2 : (a * a0⁻¹) ^ c = 1 := by rw [mul_pow, inv_pow, hF a haT a0 ha0 haF, mul_inv_cancel]
          simpa using pow_gcd_eq_one.2 ⟨h1, h2⟩
        · intro a _ b _ h
          simpa using h
    _ = {x : M | x ^ Nat.gcd m c = 1}.ncard := (Set.ncard_eq_toFinset_card _ hfin).symm
    _ ≤ B := hB

theorem torsion_finite_ncard_le (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) (d : ℕ) (hd : (d : K) ≠ 0) :
    {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}.Finite ∧
      {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1}.ncard ≤ d ^ (2 * g) := by
  have hc := GlobalTheory.T.card_abelianVariety_torsion_sepClosed K (AlgebraicClosure K) A hA g hg d hd
  let u : ptOver K (AlgebraicClosure K) ⟶ 𝟙_ (Over (Sp K)) := toUnit _
  have hu : u.left = spMap (algebraMap K (AlgebraicClosure K)) := by simpa using Over.w u
  have hdom : IsDominant (spMap (algebraMap K (AlgebraicClosure K))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap K (AlgebraicClosure K)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap K (AlgebraicClosure K)).injective]; exact bot_le)⟩
  have : IsProper A.hom := hA.proper
  have hinj : Function.Injective (fun x : 𝟙_ (Over (Sp K)) ⟶ A => u ≫ x) := by
    intro x y h
    have h' : spMap (algebraMap K (AlgebraicClosure K)) ≫ x.left = spMap (algebraMap K (AlgebraicClosure K)) ≫ y.left := by
      rw [← hu]; exact congrArg Over.Hom.left h
    exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp K) A.hom
      ((Over.w x).trans (Over.w y).symm) (spMap (algebraMap K (AlgebraicClosure K))) h')
  have hd0 : d ≠ 0 := by rintro rfl; exact hd Nat.cast_zero
  have hfinB : Finite {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hd0)
  let φ : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} → {x : ptOver K (AlgebraicClosure K) ⟶ A // x ^ d = 1} :=
    fun x => ⟨u ≫ x.1, by rw [← MonObj.comp_pow, x.2, MonObj.comp_one]⟩
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  have : Finite {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ d = 1} := Finite.of_injective φ hφ
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, ← hc]
  exact Nat.card_le_card_of_injective φ hφ

end GlobalTheory.GoodRedTorsion

namespace GlobalTheory.GoodRedTorsion

theorem hasGoodReduction_of_torsion : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], GlobalTheory.SS.SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} = m ^ (2 * g)}.Infinite → HasGoodReduction R K A := by
  intro R K _ _ _ _ _ hS A _ _ hA g hg hinf
  obtain ⟨G, inst, hG, he, c, hc, hs⟩ :=
    GlobalTheory.SS.exists_neutral_group_model R K hS A hA (GlobalTheory.T.abelianVariety_isProjectiveOverRingByCharts K A hA)
  obtain ⟨hDVR, hHen, hAC, hFR⟩ := hS
  have := hG.1
  have := hG.2.1
  have := hG.2.2.1
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R K
  have heL : IsIso G.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map G.e.hom))
  have hgenP : IsProper ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom := by
    rw [← Over.w G.e.hom]; have := hA.proper; infer_instance
  have hGg : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K))).obj G.Y).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (g := 𝟙 _) ⟨(Over.w G.e.hom).trans (Category.comp_id _).symm⟩) hg
  let ψ : (𝟙_ (Over (Sp R)) ⟶ G.Y) →* (𝟙_ (Over (Sp K)) ⟶ A) :=
    { toFun := fun t => secHom (spMap (algebraMap R K)) G.Y t ≫ G.e.hom
      map_one' := by rw [map_one]; exact MonObj.one_comp _
      map_mul' := fun t t' => by rw [map_mul]; exact MonObj.mul_comp _ _ _ }
  have hψinj : Function.Injective ψ := fun t t' h =>
    GlobalTheory.IsogRed.sec_injective (spMap (algebraMap R K)) ((cancel_mono G.e.hom).1 h)
  have hψ : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, ∃ t, ψ t = a ^ c := fun a => by
    obtain ⟨s, hs'⟩ := hs a
    refine ⟨s, ?_⟩
    change GlobalTheory.IsogRed.sec _ s ≫ G.e.hom = _
    rw [GlobalTheory.IsogRed.sec_eq_comp _ G.e s (a ^ c) hs', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose sA hsA using hψ
  have hred : ∀ t : 𝟙_ (Over (Sp R)) ⟶ G.Y, ∀ n : ℕ, IsUnit (n : R) → t ^ n = 1 →
      secHom (spMap (residue R)) G.Y t = 1 → t = 1 := by
    intro t n hn htn ht
    refine GlobalTheory.RedPts.eq_one_of_pow_of_closedPoint G.Y (𝟙 (Sp R)) hn t htn (Z := Over.mk (spMap (residue R)))
      (Over.homMk (spMap (residue R)) (Category.comp_id _))
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ ?_
    rw [← MonObj.comp_one (Over.homMk (spMap (residue R)) (Category.comp_id _) :
      Over.mk (spMap (residue R)) ⟶ Over.mk (𝟙 (Sp R)))]
    apply Over.OverMorphism.ext
    have e1 := GlobalTheory.IsogRed.sec_left (spMap (residue R)) t
    have e2 := GlobalTheory.IsogRed.sec_left (spMap (residue R)) (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y)
    have e3 : GlobalTheory.IsogRed.sec (spMap (residue R)) t = GlobalTheory.IsogRed.sec (spMap (residue R)) 1 := by
      rw [← secHom_apply, ← secHom_apply, map_one]; exact ht
    change spMap (residue R) ≫ t.left = spMap (residue R) ≫ (1 : 𝟙_ (Over (Sp R)) ⟶ G.Y).left
    rw [← e1, ← e2, e3]
  have hunit : ∀ m : ℕ, (m : ResidueField R) ≠ 0 → IsUnit (m : R) := fun m hm => by
    by_contra h
    exact hm (by rw [← map_natCast (residue R)]; exact (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 h))
  have hsp : IsProper (GlobalTheory.SS.spFibre G.Y).hom := by
    refine GlobalTheory.T.isProper_of_infinitely_many_large_torsion (ResidueField R) (GlobalTheory.SS.spFibre G.Y) (GlobalTheory.IsogRed.smConn_baseChange _ _ hG) g
      (GlobalTheory.IsogRed.relDim_spFibre (K := K) G.Y hG g hGg) (c ^ (2 * g)) (hinf.mono ?_)
    rintro m ⟨hm, hcard⟩
    refine ⟨hm, ?_⟩
    have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero
    have hmK : (m : K) ≠ 0 := by
      have := ((hunit m hm).map (algebraMap R K)).ne_zero
      rwa [map_natCast] at this
    have hfinT : {x : 𝟙_ (Over (Sp K)) ⟶ A | x ^ m = 1}.Finite := by
      have : Finite {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hm0)
      exact Set.finite_coe_iff.mp this
    have hTcard : hfinT.toFinset.card = m ^ (2 * g) := by
      rw [← hcard, ← Set.ncard_eq_toFinset_card _ hfinT, ← Nat.card_coe_set_eq]; rfl
    have hT : ∀ a ∈ hfinT.toFinset, a ^ m = 1 := fun a ha => by simpa using ha
    have hsAm : ∀ a : 𝟙_ (Over (Sp K)) ⟶ A, a ^ m = 1 → sA a ^ m = 1 := fun a ha =>
      hψinj (by rw [map_pow, hsA, map_one, ← pow_mul, mul_comm, pow_mul, ha, one_pow])
    classical
    refine ⟨hfinT.toFinset.image fun a => secHom (spMap (residue R)) G.Y (sA a), ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      rw [← map_pow, hsAm a (hT a ha), map_one]
    · have hd : ((Nat.gcd m c : ℕ) : K) ≠ 0 := by
        obtain ⟨k, hk⟩ := Nat.gcd_dvd_left m c
        intro h0
        apply hmK
        rw [hk, Nat.cast_mul, h0, zero_mul]
      obtain ⟨hfin, hB⟩ := torsion_finite_ncard_le K A hA g hg _ hd
      rw [← hTcard]
      refine card_le_of_fibres _ m c (c ^ (2 * g)) hT _ ?_ hfin
        (hB.trans (Nat.pow_le_pow_left (Nat.le_of_dvd hc (Nat.gcd_dvd_right m c)) _))
      intro a ha b hb hab
      have ht : (sA a * (sA b)⁻¹) ^ m = 1 := by
        rw [mul_pow, inv_pow, hsAm a (hT a ha), hsAm b (hT b hb)]; simp
      have h1 := hred _ m (hunit m hm) ht (by rw [map_mul, map_inv, hab, mul_inv_cancel])
      rw [← hsA a, ← hsA b, mul_inv_eq_one.1 h1]
  have hprop : IsProper G.Y.hom := GlobalTheory.T.isProper_smoothConnGroupScheme_dvr_of_proper_fibres R K G.Y hG hgenP hsp
  exact ⟨G.Y, inst, GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' _ G.Y hG hprop, G.e, he⟩

end GlobalTheory.GoodRedTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGoodReductionOfManyRationalTorsionPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGoodReduction_of_many_rational_torsion_points : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], GlobalTheory.SS.SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ Nat.card {x : 𝟙_ (Over (Sp K)) ⟶ A // x ^ m = 1} = m ^ (2 * g)}.Infinite → HasGoodReduction R K A := by
  first | exact @GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion | exact GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion | (intros; apply GlobalTheory.GoodRedTorsion.hasGoodReduction_of_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizes
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.NormRatio.StdLevel

variable {D : D7}

def intSub (D : D7) : Subring (Af D.host.F ⊗[D.host.F] D.host.E) where
  carrier := intAE D
  mul_mem' := GlobalTheory.HostAdeleIso.intAE_mul_mem D
  one_mem' := AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩
  add_mem' := (intAE D).add_mem
  zero_mem' := (intAE D).zero_mem
  neg_mem' := (intAE D).neg_mem

theorem mem_intAE_iff_swap (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ intAE D ↔ Lev.swapAE D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      have e : Lev.swapAE D (a ⊗ₜ[D.host.F] (x : D.host.E)) =
          ((x : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)) * ((1 : D.host.E) ⊗ₜ[D.host.F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]; rfl
      rw [e]
      exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, fun v => ha v⟩, rfl⟩))
    | zero => rw [RingHom.map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [RingHom.map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy
  · intro hz
    let c := (Algebra.TensorProduct.comm D.host.F D.host.E (Af D.host.F)).toRingEquiv.toRingHom
    have key : Formalism.L2.Herm.intAf D.host.F D.host.E ≤ (intSub D).comap c := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · exact AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, rfl⟩
      · exact AddSubgroup.subset_closure ⟨a, fun v => ha v, 1, rfl⟩
    have e : ∀ w, c (Lev.swapAE D w) = w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [RingHom.map_zero, RingHom.map_zero]
      | tmul a b => rfl
      | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
    have h : c (Lev.swapAE D z) ∈ intSub D := key hz
    rw [e] at h
    exact h

theorem preserves_iff {R : Type} [CommRing R] (S : Subring R) {n : ℕ} (M M' : Matrix (Fin n) (Fin n) R)
    (h1 : M * M' = 1) (h2 : M' * M = 1) :
    (∀ y : Fin n → R, (∀ i, y i ∈ S) ↔ ∀ i, (M *ᵥ y) i ∈ S) ↔ (∀ i j, M i j ∈ S) ∧ ∀ i j, M' i j ∈ S := by
  have hmv : ∀ (A : Matrix (Fin n) (Fin n) R) (y : Fin n → R), (∀ i j, A i j ∈ S) → (∀ i, y i ∈ S) →
      ∀ i, (A *ᵥ y) i ∈ S :=
    fun A y hA hy i => show (∑ j, A i j * y j) ∈ S from Subring.sum_mem _ fun j _ => mul_mem (hA i j) (hy j)
  have hs : ∀ j k : Fin n, (Pi.single j (1 : R) : Fin n → R) k ∈ S := fun j k => by
    rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have := (h (Pi.single j 1)).1 (hs j) i
      simpa [Matrix.mulVec_single_one] using this
    · have hy := (h (M' *ᵥ Pi.single j 1)).2 (by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]; exact hs j) i
      simpa [Matrix.mulVec_single_one] using hy
  · rintro ⟨hM, hM'⟩ y
    refine ⟨hmv M y hM, fun hy => ?_⟩
    have := hmv M' _ hM' hy
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at this

theorem mem_latHat_stdLat (V : HSp D) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E ((stdLat V : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
      Set (Fin V.rank → D.host.E)) ↔ ∀ i, z i ∈ intAE D := by
  classical
  constructor
  · intro hz i
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, o, congrArg (fun w => a ⊗ₜ[D.host.F] w) ho.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro hz
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have := hz i
    generalize z i = w at this
    induction this using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨x, rfl⟩
        · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
      · by_cases hj : j = i
        · subst hj; rw [Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, TensorProduct.tmul_zero]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

theorem stdLat_eq (V : HSp D) : stdLat V = GlobalTheory.SW.stdL D.host.E V.rank := by
  ext x
  rw [GlobalTheory.SW.Base.mem_stdL]
  simp only [stdLat, Formalism.MainNotions.StandardLatticesGL3.stdL, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun i => ?_
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

end GlobalTheory.NormRatio.StdLevel


open GlobalTheory.NormRatio.StdLevel in
theorem GlobalTheory.NormRatio.selfDual_and_mem_intG_iff : ∀ {D : D7} (V : HSp D) (n : ℕ) (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n),
    V.gram = 1 → V.rank = n → GlobalTheory.BotFormula.IsFinPt V g x →
    IsSelfDualC V (stdLat V) ∧ (x ∈ intG D n ↔ g ∈ openOff V (stdLat V) ∅) := by
  intro D V n g x hG hn hx
  subst hn
  have hSD : IsSelfDualC V (stdLat V) := by rw [stdLat_eq]; exact GlobalTheory.Ker.Base.selfDualC_stdL hG
  refine ⟨hSD, ?_⟩
  have hfx := GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hx
  subst hfx
  have e1 : ∀ (k : GA D V) (i j : Fin V.rank),
      (((GlobalTheory.BotClassDict.finStd V hG k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔
        (finHom V k).1 i j ∈ intAE D := fun k i j => by
    rw [← GlobalTheory.BotClassDict.toAfE_int_iff, GlobalTheory.BotClassDict.toAfE_finStd, mem_intAE_iff_swap]
  have hL : GlobalTheory.BotClassDict.finStd V hG g ∈ intG D V.rank ↔
      (∀ i j, (finHom V g).1 i j ∈ intAE D) ∧ ∀ i j, (finHom V g⁻¹).1 i j ∈ intAE D := by
    rw [GlobalTheory.NormSum.mem_intG]
    unfold Formalism.MainNotions.StandardLatticesGL3.IntG
    have e2 : ((↑(GlobalTheory.BotClassDict.finStd V hG g) : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) =
        ↑(GlobalTheory.BotClassDict.finStd V hG g⁻¹) := by rw [map_inv, Subgroup.coe_inv]
    rw [e2]
    simp only [e1]
    exact ⟨fun h => ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩, fun h i j => ⟨h.1 i j, h.2 i j⟩⟩
  have hR : g ∈ openOff V (stdLat V) ∅ ↔
      ∀ y, (∀ i, y i ∈ intAE D) ↔ ∀ i, ((finHom V g).1 *ᵥ y) i ∈ intAE D := by
    have e : g ∈ openOff V (stdLat V) ∅ ↔ g ∈ GlobalTheory.AdelicU.levelOpen _ (HSpace.gram V) (stdLat V) := by
      rw [GlobalTheory.AdelicU.mem_levelOpen]; simp [openOff]
    haveI := hSD.1
    rw [e, GlobalTheory.AdelicU.mem_levelOpen_iff_latHat _ _ (Submodule.IsLattice.fg D.host.E (stdLat V))]
    refine forall_congr' fun y => ?_
    rw [mem_latHat_stdLat, mem_latHat_stdLat]
    rfl
  have h1 : (finHom V g).1 * (finHom V g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h2 : (finHom V g⁻¹).1 * (finHom V g).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  rw [hL, hR]
  exact (preserves_iff (intSub D) _ _ h1 h2).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizesStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes : ∀ {D : D7} (V : HSp D) (n : ℕ) (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n), V.gram = 1 → V.rank = n → GlobalTheory.BotFormula.IsFinPt V g x →
  IsSelfDualC V (stdLat V) ∧ (x ∈ intG D n ↔ g ∈ openOff V (stdLat V) ∅) := by
  first | exact @GlobalTheory.NormRatio.selfDual_and_mem_intG_iff | exact GlobalTheory.NormRatio.selfDual_and_mem_intG_iff | (intros; apply GlobalTheory.NormRatio.selfDual_and_mem_intG_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFiberMeasuresChangeOfForm
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open GlobalTheory.UPel.HT.TateCompare
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKGeo.GammaUniq

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem exists_simSys_all {N : ℕ} (hN : 0 < N) (hK : N.Coprime p) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (he : ∀ n q q' z z', e n q q' z → e n q q' z' → z = z') (I₁ I₂ : TateIsoO D k Q act e)
    (hI : ∀ y, I₁.ev N y = I₂.ev N y) :
    ∃ t : SimSys D N N, ∀ n, 0 < n → n.Coprime p → ∀ y, I₂.ev n y = I₁.ev n (t.g n y) := by
  choose g hg using exists_lift I₁ I₂
  choose u hu using exists_mult I₁ I₂
  have hdiv : ∀ {n m : ℕ}, (n * m).Coprime p → n.Coprime p := fun {n m} h =>
    Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) h
  have utow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → u (n * m) ≡ u n [MOD n] := by
    intro n m hn hm hc
    have h : I₁.ζ n ^ u (n * m) = I₁.ζ n ^ u n := by
      rw [hu n hn (hdiv hc), ← I₂.ζ_pow n m hn hm hc, ← hu _ (Nat.mul_pos hn hm) hc, ← pow_mul, mul_comm (u _) m,
        pow_mul, I₁.ζ_pow n m hn hm hc]
    rwa [pow_eq_pow_iff_modEq, ← (I₁.ζ_prim n hn (hdiv hc)).eq_orderOf] at h
  have gtow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z := by
    intro n m hn hm hc x
    rw [← ev_eq_iff I₁ hn (hdiv hc), hg n hn (hdiv hc), ← I₁.tower n m hn hm hc, hg _ (Nat.mul_pos hn hm) hc,
      I₂.tower n m hn hm hc]
  have sim2 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y,
      (n : ℤ) ∣ 2 * (D.EF (g n x) (g n y) - u n * D.EF x y) := by
    intro n hn hc x y
    have h₁ := I₁.isom n hn hc (g n x) (g n y)
    rw [hg n hn hc, hg n hn hc] at h₁
    have h := he _ _ _ _ _ h₁ (I₂.isom n hn hc x y)
    rw [← hu n hn hc, ← zpow_natCast, ← _root_.zpow_mul] at h
    rw [← (I₁.ζ_prim n hn hc).zpow_eq_one_iff_dvd, mul_sub, _root_.zpow_sub, h,
      show (u n : ℤ) * (2 * D.EF x y) = 2 * (u n * D.EF x y) by ring, mul_inv_cancel]
  refine ⟨{
    g := g
    u := u
    lin := fun n hn hc c x => ?_
    u_cop := fun n hn hc => ?_
    u_tower := utow
    surj := fun n hn hc x => ?_
    inj := fun n hn hc x z h => ?_
    sim := fun n hn hc x y => ?_
    tower := gtow
    one := fun x => ?_ }, fun n hn hc y => (hg n hn hc y).symm⟩
  · rw [← ev_eq_iff I₁ hn hc, hg n hn hc, I₁.lin, I₂.lin, hg n hn hc]
  · rw [← (I₁.ζ_prim n hn hc).pow_iff_coprime hn, hu n hn hc]
    exact I₂.ζ_prim n hn hc
  · obtain ⟨y, hy⟩ := (I₂.onto n hn hc _).1 ((I₁.onto n hn hc _).2 ⟨x, rfl⟩)
    refine ⟨y, ?_⟩
    rw [← ev_eq_iff I₁ hn hc, hg n hn hc, hy]
  · rw [← I₂.ker n hn hc, ← hg n hn hc, h]
    exact I₁.ev_nsmul_self hn hc z
  · by_cases hp : p = 2
    · subst hp
      have hco : IsCoprime (n : ℤ) 2 := by exact_mod_cast Nat.isCoprime_iff_coprime.2 hc
      exact hco.dvd_of_dvd_mul_left (sim2 n hn hc x y)
    · have hc2 : (n * 2).Coprime p :=
        Nat.Coprime.mul_left hc ((Nat.coprime_primes Nat.prime_two Fact.out).2 (Ne.symm hp))
      have h := sim2 (n * 2) (by omega) hc2 x y
      obtain ⟨z, hz⟩ := gtow n 2 hn two_pos hc2 x
      obtain ⟨w, hw⟩ := gtow n 2 hn two_pos hc2 y
      obtain ⟨a, ha⟩ := (utow n 2 hn two_pos hc2).dvd
      obtain ⟨c, hcc⟩ := h
      rw [hz, hw] at hcc
      simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at hcc
      push_cast at hcc
      refine ⟨c - D.EF (g n x) w - D.EF z (g n y) - n * D.EF z w - a * D.EF x y, ?_⟩
      have h2 : (2 : ℤ) ≠ 0 := two_ne_zero
      apply mul_left_cancel₀ h2
      linear_combination hcc - 2 * D.EF x y * ha
  · rw [← ev_eq_iff I₁ hN hK, hg N hN hK, hI]

theorem isIntAf_mul {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a * c) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hc v)

theorem isIntAf_intCast (c : ℤ) : IsIntAf (c : AfP p) := fun v => by
  rw [map_intCast]; exact intCast_mem _ c

theorem inAf_mem (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem smul_mem {a : AfP p} (ha : IsIntAf a) {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) : a • z ∈ LaHat D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨a * c, x, isIntAf_mul ha hc, by rw [TensorProduct.smul_tmul', smul_eq_mul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_mem (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)) (hA : ∀ x, A (inAf D x) ∈ LaHat D)
    {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) : A z ∈ LaHat D := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = c • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul]
    exact smul_mem hc (hA x)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := A)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem eq_zero_of_dvd (a : AfP p) (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ c, IsIntAf c ∧ a = n • c) : a = 0 := by
  have key : ∀ v : AwayP p, AfP.eval v a = 0 := by
    intro v
    by_contra hne
    obtain ⟨l, hl0, hlp, hlv⟩ : ∃ l : ℕ, 0 < l ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
      have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
      have hmax : v.1.asIdeal.IsMaximal := v.1.isMaximal
      have hmp : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
      have hnle : ¬ v.1.asIdeal ≤ Ideal.span {(p : ℤ)} := fun hle => v.2 (hmax.eq_of_le hmp.ne_top hle)
      obtain ⟨x, hx, hxp⟩ := Set.not_subset.1 hnle
      have hxp' : ¬ (p : ℤ) ∣ x := fun hd => hxp (Ideal.mem_span_singleton.2 hd)
      refine ⟨x.natAbs, Int.natAbs_pos.2 (fun h0 => hxp' (h0 ▸ dvd_zero _)), ?_, ?_⟩
      · exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 (fun hd => hxp' (Int.natCast_dvd.2 hd))).symm
      · rcases Int.natAbs_eq x with h1 | h1
        · rw [← h1]; exact hx
        · rw [← neg_eq_iff_eq_neg.2 h1]; exact neg_mem hx
    have hlt : Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) < 1 := by
      have e : ((l : ℕ) : v.1.adicCompletion ℚ) = algebraMap ℤ (v.1.adicCompletion ℚ) (l : ℤ) := by simp
      have e2 : Valued.v (algebraMap ℤ (v.1.adicCompletion ℚ) (l : ℤ)) = v.1.valuation ℚ (algebraMap ℤ ℚ (l : ℤ)) := by
        rw [IsScalarTower.algebraMap_apply ℤ ℚ (v.1.adicCompletion ℚ)]
        exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
      rw [e, e2, HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact hlv
    have hv0 : Valued.v (AfP.eval v a) ≠ 0 := (Valuation.ne_zero_iff _).2 hne
    obtain ⟨j, hj⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hv0)
    obtain ⟨c, hc, e⟩ := h (l ^ j) (pow_pos hl0 j) (Nat.Coprime.pow_left j hlp)
    have hc1 : Valued.v (AfP.eval v c) ≤ 1 := hc v
    have : Valued.v (AfP.eval v a) ≤ Valued.v ((l : ℕ) : v.1.adicCompletion ℚ) ^ j := by
      rw [e, map_nsmul, nsmul_eq_mul, map_mul, Nat.cast_pow, map_pow]
      exact mul_le_of_le_one_right' hc1
    exact absurd hj (not_lt.2 this)
  exact Subtype.ext (funext key)

def basAf {J : Type} (b : Module.Basis J ℤ D.La) : Module.Basis J (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  (b.baseChange ℚ).baseChange (AfP p)

theorem basAf_apply {J : Type} (b : Module.Basis J ℤ D.La) (i : J) : basAf b i = inAf D (b i) := by
  simp [basAf, inAf]

theorem isIntAf_repr {J : Type} (b : Module.Basis J ℤ D.La) (i : J) {z : AfP p ⊗[ℚ] VQ D} (hz : z ∈ LaHat D) :
    IsIntAf ((basAf b).repr z i) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    have e : (basAf b).repr (c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D)) i = ((b.repr x i : ℤ) : AfP p) * c := by
      simp [basAf, Algebra.smul_def]
    rw [e]
    exact isIntAf_mul (isIntAf_intCast _) hc
  | zero => simpa using isIntAf_intCast (p := p) 0
  | add x y _ _ hx hy =>
    intro v
    rw [map_add (f := _), Finsupp.add_apply, map_add (f := _)]
    exact add_mem (hx v) (hy v)
  | neg x _ hx =>
    intro v
    rw [map_neg, Finsupp.neg_apply, map_neg]
    exact neg_mem (hx v)

theorem eq_zero_of_dvd_laHat (z : AfP p ⊗[ℚ] VQ D)
    (h : ∀ n : ℕ, 0 < n → n.Coprime p → ∃ w ∈ LaHat D, z = n • w) : z = 0 := by
  have := D.freeLa
  let b := Module.Free.chooseBasis ℤ D.La
  refine (basAf b).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine eq_zero_of_dvd _ fun n hn hc => ?_
  obtain ⟨w, hw, rfl⟩ := h n hn hc
  exact ⟨_, isIntAf_repr b i hw, by rw [map_nsmul, Finsupp.smul_apply]⟩

theorem end_ext {A B : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)} (h : ∀ x, A (inAf D x) = B (inAf D x)) : A = B := by
  have := D.freeLa
  exact (basAf (Module.Free.chooseBasis ℤ D.La)).ext fun i => by rw [basAf_apply, h]

theorem actOn_injective {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (rep : C →ₐ[ℚ] Module.End ℚ V) (hr : Function.Injective rep) (R : Type) [CommRing R] [Algebra ℚ R] :
    Function.Injective (actOn rep R) := by
  have h₁ : Function.Injective (rep.toLinearMap.lTensor R) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hr
  have j := (TensorProduct.isBaseChange ℚ V R).end
  have e : ∀ x, actOn rep R x = j.equiv (rep.toLinearMap.lTensor R x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r c =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul]
      ext v
      have := (TensorProduct.isBaseChange ℚ V R).endHom_comp_apply (rep c) v
      have e₁ : actOn rep R (r ⊗ₜ c) = r • (rep c).baseChange R := by
        rw [Algebra.smul_def]; rfl
      rw [e₁]
      simp at this ⊢
      simp [this, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  intro x y h
  rw [e, e] at h
  exact h₁ (j.equiv.injective h)

variable {G : HTGroup p} (L : Link D G)

theorem actG_injective : Function.Injective L.actG := by
  intro g h e
  have := D.finLa
  have h₁ : (g.1.1 : AfP p ⊗[ℚ] G.C) = h.1.1 := actOn_injective L.rep L.rep_inj (AfP p) e
  have h₁' : g.1.1 = h.1.1 := Units.ext h₁
  refine Subtype.ext (Prod.ext h₁' (Units.ext ?_))
  have hg := mem_uGroup.1 g.2
  have hh := mem_uGroup.1 h.2
  rw [h₁, hh] at hg
  have hinj : Function.Injective (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C)) :=
    Algebra.TensorProduct.includeLeft_injective (S := ℚ) (algebraMap ℚ G.C).injective
  exact (hinj hg).symm

theorem inAf_add (x y : D.La) : inAf D (x + y) = inAf D x + inAf D y := by
  simp only [inAf, TensorProduct.tmul_add]

end GlobalTheory.LKGeo.GammaUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepKeepsSphericalOfLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepKeepsSphericalOfLatticeStabilizer
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

namespace GlobalTheory.SphMove

theorem isSphOff_om : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GlobalTheory.Core.Rk.IP.WRep A B),
  IsWeilDatumO ψ A B χA χB om → ∀ (LA : Lat A) (LB : Lat B), IsSelfDualC A LA → IsSelfDualC B LB →
  ∀ (Sf : Finset (FinPl D)) (g : GA D A), g ∈ openOff A LA Sf → ∀ f, IsThetaFunO ψ A B f → IsSphOff ψ A B LA LB Sf f →
    IsSphOff ψ A B LA LB Sf (om (g, 1) f) := by
  intro D ψ A B χA χB om hW LA LB hA hB Sf g hg f hf hsph
  have hmv : GlobalTheory.FinPl.Moves A g LA LA (fun v => v ∉ Sf) :=
    (GlobalTheory.QLawPf.moves_iff_forall hA _ g).2 fun v hv =>
      (GlobalTheory.StMoves.moves_iff_stabLoc A LA hA.1.fg v g).2 (hg v hv)
  have hmi : GlobalTheory.FinPl.Moves A g⁻¹ LA LA (fun v => v ∉ Sf) := GlobalTheory.StMoves.moves_inv hmv
  have hm1 : GlobalTheory.FinPl.Moves B (1 : GA D B)⁻¹ LB LB (fun v => v ∉ Sf) := by
    intro y _
    rw [inv_one, show mt B (1 : GA D B) = 1 from rfl, Matrix.one_mulVec]
  have key : ∀ u ∈ latO A B (LA : Set _) (LB : Set _) (fun v => v ∉ Sf),
      actO A B g⁻¹ (1 : GA D B)⁻¹ u ∈ latO A B (LA : Set _) (LB : Set _) (fun v => v ∉ Sf) :=
    fun u hu => GlobalTheory.MidVacLat.actO_mem_latO hA hA hB hB hmi hm1 hu
  have step : ∀ w, heisO ψ A B (actO A B g⁻¹ (1 : GA D B)⁻¹ w) f = f →
      heisO ψ A B w (om (g, 1) f) = om (g, 1) f := by
    intro w hw
    have h := hW.om_heis g 1 (actO A B g⁻¹ (1 : GA D B)⁻¹ w) f hf
    rw [hw, GlobalTheory.MidVacLat.actO_actO_inv] at h
    exact h.symm
  refine ⟨fun u hu => step _ ?_, fun e he u hu hh => step _ ?_⟩
  · rw [GlobalTheory.MidVacLat.actO_two_nsmul]
    exact hsph.1 _ (key u hu)
  · exact hsph.2 e he _ (key u hu) (GlobalTheory.MidVacLat.isHalf_actO _ _ hh)

end GlobalTheory.SphMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepKeepsSphericalOfLatticeStabilizerStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_keeps_spherical_of_lattice_stabilizer : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : GlobalTheory.Core.Rk.IP.WRep A B),
  IsWeilDatumO ψ A B χA χB om → ∀ (LA : Lat A) (LB : Lat B), IsSelfDualC A LA → IsSelfDualC B LB →
  ∀ (Sf : Finset (FinPl D)) (g : GA D A), g ∈ openOff A LA Sf → ∀ f, IsThetaFunO ψ A B f → IsSphOff ψ A B LA LB Sf f →
    IsSphOff ψ A B LA LB Sf (om (g, 1) f) := by
  first | exact @GlobalTheory.SphMove.isSphOff_om | exact GlobalTheory.SphMove.isSphOff_om | (intros; apply GlobalTheory.SphMove.isSphOff_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelUpperBoundCountRankAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelUpperBoundCountRankAmple
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.HSUpper

noncomputable def polyComb {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ) :
    (Fin δ → MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) →ₗ[ℤ] K :=
  ∑ i : Fin δ, LinearMap.mulRight ℤ (w i) ∘ₗ (MvPolynomial.aeval x).toLinearMap ∘ₗ
    (MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n).subtype ∘ₗ LinearMap.proj i

theorem polyComb_apply {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ) (T) :
    polyComb x w n T = ∑ i, MvPolynomial.aeval x (T i : MvPolynomial (Fin (D + 1)) ℤ) * w i := by
  simp [polyComb]

theorem fg_finrank_le {K : Type} [Field K] {D δ : ℕ} (x : Fin (D + 1) → K) (w : Fin δ → K) (n : ℕ)
    (H : AddSubgroup K) (hH : ∀ f ∈ H, ∃ T : Fin δ → MvPolynomial (Fin (D + 1)) ℤ,
      (∀ i, (T i).IsHomogeneous n) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i) :
    H.FG ∧ Module.finrank ℤ H ≤ δ * (n + D).choose D := by
  obtain ⟨-, -, -, hrk, hfin⟩ := GlobalTheory.T.card_bounded_homogeneous_int_form_families D n δ 0 le_rfl
  haveI := hfin
  haveI : Module.Free ℤ (MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) :=
    Module.free_of_finite_type_torsion_free'
  set Φ := polyComb x w n
  have hle : ∀ f ∈ H, f ∈ LinearMap.range Φ := by
    intro f hf
    obtain ⟨T, hT, rfl⟩ := hH f hf
    refine ⟨fun i => ⟨T i, (MvPolynomial.mem_homogeneousSubmodule n (T i)).2 (hT i)⟩, ?_⟩
    simp [Φ, polyComb_apply]
  let g : H →ₗ[ℤ] LinearMap.range Φ :=
    { toFun := fun f => ⟨f.1, hle f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun m f => by ext; simp }
  have hg : Function.Injective g := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI : Module.Finite ℤ H := Module.Finite.of_injective g hg
  refine ⟨(AddGroup.fg_iff_addSubgroup_fg H).1 (Module.Finite.iff_addGroup_fg.1 inferInstance), ?_⟩
  calc Module.finrank ℤ H ≤ Module.finrank ℤ (LinearMap.range Φ) := LinearMap.finrank_le_finrank_of_injective hg
    _ ≤ Module.finrank ℤ (Fin δ → MvPolynomial.homogeneousSubmodule (Fin (D + 1)) ℤ n) := LinearMap.finrank_range_le Φ
    _ = δ * (n + D).choose D := by
      rw [Module.finrank_pi_fintype, hrk]; simp

end GlobalTheory.HSAmp.HSUpper

theorem GlobalTheory.HSAmp.HSUpper.upper_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (P.H (e * q + a) b).FG ∧ Module.finrank ℤ (P.H (e * q + a) b) ≤ Module.finrank (ratF x) X.functionField * (q + c + D).choose D ∧ ∀ R κ : ℝ, 0 ≤ R → 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (P.Bl (e * q + a) b R).Finite ∧ (P.Bl (e * q + a) b R).ncard ≤ (2 * ⌊C * R / κ ^ (q + c)⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + c + D).choose D) := by
  intro k _ X _ p D hD P hA e x hx a b
  obtain ⟨c, w, C, hC, hrep⟩ := GlobalTheory.T.sections_eq_sum_aeval_boundedIntCoeff_ample k X p D hD P hA e x hx a b
  refine ⟨c, C, hC, fun q => ?_⟩
  obtain ⟨hfg, hrk⟩ := GlobalTheory.HSAmp.HSUpper.fg_finrank_le x w (q + c) (P.H (e * q + a) b) (fun f hf => by
    obtain ⟨T, hT, hf', -⟩ := hrep q f hf
    exact ⟨T, hT, hf'⟩)
  refine ⟨hfg, hrk, fun R κ hR hκ hcov => ?_⟩
  set R' : ℝ := C * R / κ ^ (q + c)
  have hR' : 0 ≤ R' := div_nonneg (mul_nonneg hC.le hR) (pow_pos hκ _).le
  obtain ⟨hSfin, hScard, -⟩ := GlobalTheory.T.card_bounded_homogeneous_int_form_families D (q + c) (Module.finrank (ratF x) X.functionField) R' hR'
  set S := {T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ |
    (∀ i, (T i).IsHomogeneous (q + c)) ∧ ∀ i α, |((AddMonoidAlgebra.coeff (T i) α : ℤ) : ℝ)| ≤ R'}
  have hsub : P.Bl (e * q + a) b R ⊆
      (fun T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ =>
        ∑ i, MvPolynomial.aeval x (T i) * w i) '' S := by
    intro f hf
    rw [← ballIn_H] at hf
    obtain ⟨hfH, hfR⟩ := hf
    obtain ⟨T, hT, hfT, hbd⟩ := hrep q f hfH
    exact ⟨T, ⟨hT, hbd R κ hκ hcov hfR⟩, hfT.symm⟩
  have himfin := hSfin.image (fun T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ =>
        ∑ i, MvPolynomial.aeval x (T i) * w i)
  refine ⟨himfin.subset hsub, ?_⟩
  calc (P.Bl (e * q + a) b R).ncard ≤ _ := Set.ncard_le_ncard hsub himfin
    _ ≤ S.ncard := Set.ncard_image_le hSfin
    _ = _ := hScard
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelUpperBoundCountRankAmpleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_upperBound_count_rank_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ a b : ℤ, ∃ (c : ℕ) (C : ℝ), 0 < C ∧ ∀ q : ℕ, (P.H (e * q + a) b).FG ∧ Module.finrank ℤ (P.H (e * q + a) b) ≤ Module.finrank (ratF x) X.functionField * (q + c + D).choose D ∧ ∀ R κ : ℝ, 0 ≤ R → 0 < κ → (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ l, κ ≤ P.nu e 0 σ y (x l)) → (P.Bl (e * q + a) b R).Finite ∧ (P.Bl (e * q + a) b R).ncard ≤ (2 * ⌊C * R / κ ^ (q + c)⌋₊ + 1) ^ (Module.finrank (ratF x) X.functionField * (q + c + D).choose D) := by
  first | exact @GlobalTheory.HSAmp.HSUpper.upper_bound | exact GlobalTheory.HSAmp.HSUpper.upper_bound | (intros; apply GlobalTheory.HSAmp.HSUpper.upper_bound <;> assumption)
end
end
