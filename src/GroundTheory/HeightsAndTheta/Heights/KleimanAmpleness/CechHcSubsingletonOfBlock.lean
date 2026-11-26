module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellHOfCellSec
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideSide
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHcSubsingletonOfBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart Cell CechC cellMon cechZc cechBc)

noncomputable section

def eulerChar (F : Type) [Field F] {K : Type} [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) : ℚ :=
  ∑ i ∈ Finset.range (∑ k, (Fintype.card (ι k) - 1) + 1),
    (-1 : ℚ) ^ i * (Module.finrank F (cechHc ι (quotPart F V) m i) : ℚ)

def EulerVar.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (v : Σ k, ι k),
    NumbersDVR.IsMultiHomogIdeal V →
    (∀ (m : K → ℤ) (i : ℕ), FiniteDimensional F (cechHc ι (quotPart F V) m i)) →
    (∀ (m : K → ℤ) (i : ℕ),
      FiniteDimensional F (cechHc ι (quotPart F (V.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}))) m i)) →
    (∀ (m : K → ℤ) (i : ℕ),
      FiniteDimensional F (cechHc ι (quotPart F (V ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) m i)) →
    ∀ m : K → ℤ, eulerChar F ι V m =
      eulerChar F ι (V.colon (Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)})) (m - Pi.single v.1 1) +
        eulerChar F ι (V ⊔ Ideal.span {(X v : MvPolynomial (Σ k, ι k) F)}) m

section Vanish

variable {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]


omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] in
theorem subsingleton_loc_of_block {V : Ideal (MvPolynomial (Σ k, ι k) F)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ V) (I : ∀ k, Finset (ι k)) (hI : (I k).Nonempty) :
    Subsingleton (LocalizedModule (cellMon F I) (MvPolynomial (Σ k, ι k) F ⧸ V)) := by
  obtain ⟨i, hi⟩ := hI
  have ht : (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ cellMon F I :=
    Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hz : ∀ x : LocalizedModule (cellMon F I) (MvPolynomial (Σ k, ι k) F ⧸ V), x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h a s =>
      rw [← LocalizedModule.zero_mk (1 : cellMon F I), LocalizedModule.mk_eq]
      refine ⟨⟨_, ht⟩, ?_⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      simp only [one_smul, smul_zero]
      rw [Submonoid.smul_def]
      change (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) • Ideal.Quotient.mk V a = 0
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact V.mul_mem_right _ (hk i)
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

theorem cechHc_subsingleton_of_block {V : Ideal (MvPolynomial (Σ k, ι k) F)} {k : K}
    (hk : ∀ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) F) ∈ V) (m : K → ℤ) (n : ℕ) :
    Subsingleton (cechHc ι (quotPart F V) m n) := by
  have hI : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n, Subsingleton (LocalizedModule (cellMon F I.1) (MvPolynomial (Σ k, ι k) F ⧸ V)) :=
    fun I => subsingleton_loc_of_block hk I.1 (I.2.1 k)
  have : Subsingleton (CechC F ι (MvPolynomial (Σ k, ι k) F ⧸ V) n) :=
    ⟨fun f g => funext fun I => (hI I).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

end Vanish

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftMapMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

noncomputable section

namespace SegreFibreIdeal

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type}

def thetaVal (ι : K → Type) (R : Type) [CommRing R] : (Σ k, segreIdx ι k) → Polynomial (MRing ι R)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (∏ k, X ⟨k, c k⟩)
  | ⟨Sum.inr k, i⟩ => Polynomial.C (X ⟨k, i⟩)

def theta (ι : K → Type) (R : Type) [CommRing R] : MRing (segreIdx ι) R →+* Polynomial (MRing ι R) :=
  eval₂Hom (Polynomial.C.comp C) (thetaVal ι R)

def chi (K : Type) [Fintype K] : MvPolynomial (Unit ⊕ K) Ω →+* Polynomial (MvPolynomial K Ω) :=
  eval₂Hom (Polynomial.C.comp C)
    (Sum.elim (fun _ => Polynomial.X * Polynomial.C (∏ k, X k)) (fun k => Polynomial.C (X k)))

theorem map_cone_theta (y : (Σ k, ι k) → Ω) :
    (Polynomial.mapRingHom (mConeMapOver O y).toRingHom).comp (theta ι O) =
      (chi K).comp (mConeMapOver O (segreJoin y)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [theta, chi, mConeMapOver]
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec,
        IndefiniteRowSideFullHecke.Kleiman2.oneBlock, NumbersDVR.segreVec, Polynomial.map_prod, Finset.prod_mul_distrib]
      ring
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]

theorem segreLiftMap_map (F : Type) [Field F] (φ : O →+* F) (W : Ideal (MRing ι F)) :
    (segreLiftMap ι F W).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom ((Ideal.Quotient.mk W).comp (MvPolynomial.map φ))).comp (theta ι O) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [theta, segreLiftMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_eval₂Hom, eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, map_C, aeval_C]
    rfl
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal, Polynomial.map_prod]
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal]

end SegreFibreIdeal

open SegreFibreIdeal in
theorem SegreFibreIdeal.proof : SegreFibreIdeal.Statement := by
  intro O _ Ω _ _ F _ φ K _ _ ι _ y
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨c, d, rfl⟩
    have hm : (segreY c * segreMon d - segreY d * segreMon c : MRing (segreIdx ι) O) ∈
        mIdealOver O (segreJoin y) := by
      simp only [mIdealOver, RingHom.mem_ker, map_sub, map_mul, map_prod, segreY, segreMon,
        mConeMapOver, aeval_X, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.oneBlock,
        NumbersDVR.segreVec, Sum.elim_inr, Finset.prod_mul_distrib]
      ring
    have := Ideal.mem_map_of_mem (MvPolynomial.map φ) hm
    rw [SetLike.mem_coe]
    convert this using 1
    simp [segreY, segreMon, map_prod]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    simp only [Ideal.mem_comap]
    have hr : segreIncl ι F (MvPolynomial.map φ f) = MvPolynomial.map φ (segreIncl ι O f) := by
      simp [segreIncl, MvPolynomial.map_rename]
    rw [hr]
    refine Ideal.mem_map_of_mem _ ?_
    have key : (mConeMapOver O (segreJoin y)).toRingHom.comp (segreIncl ι O).toRingHom =
        (rename (R := Ω) (Sum.inr : K → Unit ⊕ K)).toRingHom.comp (mConeMapOver O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [segreIncl, mConeMapOver]
      · rintro ⟨k, i⟩
        simp [segreIncl, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]
    have hc : mConeMapOver O (segreJoin y) (segreIncl ι O f) =
        rename Sum.inr (mConeMapOver O y f) := by
      simpa using congrArg (fun g => g f) key
    rw [mIdealOver, RingHom.mem_ker] at hf ⊢
    rw [hc, hf, map_zero]
  · intro W hW
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
    have h1 := congrArg (fun g => g f) (segreLiftMap_map F φ W)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
    rw [h1]
    have h2 := congrArg (fun g => g f) (map_cone_theta (O := O) y)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
    rw [mIdealOver, RingHom.mem_ker] at hf
    rw [hf, map_zero] at h2
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    apply hW
    apply Ideal.mem_map_of_mem
    rw [mIdealOver, RingHom.mem_ker]
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) h2
    simpa [Polynomial.coeff_map] using this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfIsSubvar
section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WeilNumbersImpVerticalDivisorsCommute
section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PCutByFormField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace CutByFormField

theorem vecCons_comp_finRotate {α : Type*} {n : ℕ} (c : α) (bs : Fin n → α) :
    Matrix.vecCons c bs ∘ finRotate (n + 1) = Fin.snoc (α := fun _ => α) bs c := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · rw [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.snoc_castSucc,
      Matrix.cons_val_succ]

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

end CutByFormField

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace VerticalDivisorsCommuting

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem intNum_snoc {F : Type u} [Field F] (V : Ideal (MRing ι F)) {n : ℕ} (L : Fin n → K → ℤ)
    (b : K → ℤ) :
    intNum F V (Fin.snoc (α := fun _ => K → ℤ) L b) = intNum F V (Matrix.vecCons b L) := by
  rw [← CutByFormField.vecCons_comp_finRotate]
  exact FieldNumbers.IntNumSymm.proof F K ι V (n + 1) _ _

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end VerticalDivisorsCommuting

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

theorem SectionCount.bound_from_one {X : ℝ} {d : ℕ} {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hC
  refine ⟨max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)), fun n hn => ?_⟩
  have hnd : (1 : ℝ) ≤ (n : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hn)
  have hfac : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rcases le_or_gt n₀ n with h | h
  · have h1 := hn₀ n h
    have h2 : C * (n : ℝ) ^ d ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) * (n : ℝ) ^ d :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  · have hX : X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) ≤
        |X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ hfac.le
      calc X * (n : ℝ) ^ (d + 1) ≤ |X| * (n : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self X) (by positivity)
        _ ≤ |X| * (n₀ : ℝ) ^ (d + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast h.le) _)
              (abs_nonneg X)
    have hM := le_max_right C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ))
    have hM0 : 0 ≤ max C (|X| * (n₀ : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ)) :=
      le_trans (by positivity) hM
    have h3 := le_mul_of_one_le_right hM0 hnd
    linarith [hf n]

theorem SectionCount.exists_ne_zero_of_isSubvar {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} {e : ℕ} (h : Kleiman.IsSubvar x (Kleiman.primeOf (S := k) x) e) : ∃ i, x i ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  refine ⟨i, fun h0 => hi ?_⟩
  rw [Kleiman.primeOf, ReciprocityTheory.ChartRestriction.G.Geo.coordIdeal, RingHom.mem_ker]
  simp [ReciprocityTheory.ChartRestriction.G.Geo.coneMap, h0]

theorem SectionCount.transfer (hBase : BaseRealises.Statement)
    (hP : PowRealises.Statement) (hN : NumModel.Statement)
    (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (N : ℕ) (e : ι k₀ ≃ Fin (N + 1))
    (x : Fin (N + 1) → Ω) (hx : x = IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)
    (hmod : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (Q : Kleiman.LineBundle F x) (ν : K → ℤ)
    (hQ : BundleRealises y k₀ Q ν) (d q : ℕ) (hsub : Kleiman.IsSubvar x (Kleiman.primeOf (S := F) x) (d + 1)) :
    ((Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) -
        ((d + 1 : ℕ) : ℤ) * Kleiman.interNum (Kleiman.primeOf (S := F) x)
          (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
            (fun _ : Fin d => Q.toSubSystem)) : ℤ) : ℝ) =
      (NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) : ℝ) -
        ((d + 1 : ℕ) : ℝ) * (NumbersDVR.intNum F (mIdealOver F y)
          (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) : ℝ) ∧
    ∀ n : ℕ, (Kleiman.twistMul Q.toSubSystem n (-((n : ℤ) * q))).secs =
      secOver F y (n • (ν - q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
  have h1 : Kleiman.interNum (Kleiman.primeOf (S := F) x) (fun _ : Fin (d + 1) => Q.toSubSystem) =
      NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => ν) :=
    hN F K ι Ω y k₀ N e x hx hmod (d + 1) (fun _ => Q) (fun _ => ν) (fun _ => hQ) hsub
  have hqs : ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) = q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    funext j; simp
  have hL : (fun i => (Fin.cons (α := fun _ => Kleiman.LineBundle F x) (Kleiman.twistBundle F x (q : ℤ))
      (fun _ : Fin d => Q) i).toSubSystem) =
      Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem) := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  have h2 : Kleiman.interNum (Kleiman.primeOf (S := F) x)
      (Fin.cons (α := fun _ => Kleiman.SubSystem F x Ω) (Kleiman.twistSys F x (q : ℤ))
        (fun _ : Fin d => Q.toSubSystem)) =
      NumbersDVR.intNum F (mIdealOver F y)
        (Fin.snoc (α := fun _ => K → ℤ) (fun _ : Fin d => ν) (q • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)) := by
    rw [NumbersDVR.VerticalDivisorsCommuting.intNum_snoc, ← hL, ← hqs]
    exact hN F K ι Ω y k₀ N e x hx hmod (d + 1) _ (Fin.cons ((q : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) fun _ => ν)
      (fun i => Fin.cases (hBase F K ι Ω y k₀ N e x hx hmod (q : ℤ)) (fun _ => hQ) i) hsub
  refine ⟨by rw [h1, h2]; push_cast; ring, fun n => ?_⟩
  rw [hP F K ι Ω y k₀ N e x hx hmod Q ν hQ n (-((n : ℤ) * q))]
  congr 1
  funext j
  simp only [smul_eq_mul, nsmul_eq_mul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply]
  ring

theorem SectionCount.equiv (hG : GraphModel.Statement) (hB : BundleOfDeg.Statement) (hD : ModelDim.Statement)
    (hBase : BaseRealises.Statement) (hP : PowRealises.Statement) (hV : VeryAmpleModel.Statement)
    (hN : NumModel.Statement) :
    Kleiman.SectionCount.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman2.SectionCount.Statement := by
  constructor
  · intro hA F _ K _ _ ι _ Ω _ _ y k₀ d ν q hmod hdim hva hq
    have hpos : 0 < Fintype.card (ι k₀) := by
      obtain ⟨i, -⟩ := hmod.1 k₀
      exact Fintype.card_pos_iff.2 ⟨i⟩
    obtain ⟨N, hN'⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    obtain ⟨e⟩ : Nonempty (ι k₀ ≃ Fin (N + 1)) := ⟨(Fintype.equivFin _).trans (finCongr hN')⟩
    obtain ⟨Q, hQ⟩ := hB F K ι Ω y k₀ N e hmod ν
    have hsub := (hD F K ι Ω y k₀ N e _ rfl hmod (d + 1)).2 hdim
    have hvaQ := (hV F K ι Ω y k₀ N e _ rfl hmod Q ν hQ).2 hva
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN F K ι Ω y k₀ N e _ rfl hmod Q ν hQ d q hsub
    obtain ⟨C, hC⟩ := hA F Ω N _ d Q q hsub hvaQ hq
    refine SectionCount.bound_from_one (fun n => Nat.cast_nonneg _) ⟨C, hC.mono fun n hn => ?_⟩
    rw [← hZ, ← hS n]
    exact hn
  · intro hB' k _ Ω _ _ N x d Nb b hsub hva hb
    obtain ⟨r, h, hby⟩ := hva
    have hgen : IsGraphGen Nb 0 h := fun I => by
      rw [Kleiman.SubSystem.twist_twistSys_zero]
      exact hby.generates I
    have hmod := hG k N Ω x Nb 0 (r + 1) h (SectionCount.exists_ne_zero_of_isSubvar hsub) hgen
    have hQ := realises_graph Nb 0 h hgen
    have hdim := (hD k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod (d + 1)).1 hsub
    have hvaB := (hV k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock N (Equiv.refl _) x rfl
      hmod Nb (graphDeg 0) hQ).1 ⟨r, h, hby⟩
    obtain ⟨hZ, hS⟩ := SectionCount.transfer hBase hP hN k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω
      (graphVec x h) baseBlock N (Equiv.refl _) x rfl hmod Nb (graphDeg 0) hQ d b hsub
    obtain ⟨C, hC⟩ := hB' k (Unit ⊕ Unit) (graphIdx N (r + 1)) Ω (graphVec x h) baseBlock d (graphDeg 0) b
      hmod hdim hvaB hb
    refine ⟨C, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
    rw [hZ, hS n]
    exact hC n hn

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreInclWeightedHomogeneousComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type} [Field F]


omit [Fintype K] in
theorem segre_weight_mapDomain (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (segreIdx ι))
        (Finsupp.mapDomain (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) e) =
      Sum.elim (fun _ => 0) (Finsupp.weight (NumbersDVR.blockWeight ι) e) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index
      (h := fun (v : Σ c, segreIdx ι c) (n : ℕ) => n • NumbersDVR.blockWeight (segreIdx ι) v)
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  funext c
  rcases c with ⟨⟨⟩⟩ | k
  · simp [Finsupp.sum, Finset.sum_apply, NumbersDVR.blockWeight]
  · simp [Finsupp.sum, Finset.sum_apply, NumbersDVR.blockWeight, Pi.single_apply]

theorem segreIncl_weightedHomogeneousComponent (b : K → ℕ) (f : MRing ι F) :
    segreIncl ι F (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (segreIdx ι)) (Sum.elim (fun _ => 0) b)
        (segreIncl ι F f) := by
  classical
  have hinj : Function.Injective (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) := by
    rintro ⟨k, i⟩ ⟨k', i'⟩ h
    have h1 := Sigma.mk.inj h
    obtain rfl := Sum.inr_injective h1.1
    obtain rfl := eq_of_heq h1.2
    rfl
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain
      (fun v : Σ k, ι k => (⟨Sum.inr v.1, v.2⟩ : Σ c, segreIdx ι c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [segreIncl, coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj,
      coeff_weightedHomogeneousComponent, segre_weight_mapDomain]
    by_cases hd : Finsupp.weight (NumbersDVR.blockWeight ι) e = b
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (funext fun k => congrFun h (Sum.inr k))]
  · push Not at he
    rw [segreIncl, coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

theorem segreLiftVal_eq (W : Ideal (MRing ι F)) (v : Σ c, segreIdx ι c) :
    ∃ β, segreLiftVal ι F W v =
      Polynomial.X ^ (NumbersDVR.blockWeight (segreIdx ι) v (Sum.inl ())) * Polynomial.C β := by
  rcases v with ⟨⟨⟨⟩⟩ | k, i⟩
  · exact ⟨Ideal.Quotient.mk W (∏ k, X ⟨k, i k⟩), by
      simp [segreLiftVal, NumbersDVR.blockWeight]⟩
  · exact ⟨Ideal.Quotient.mk W (X ⟨k, i⟩), by simp [segreLiftVal, NumbersDVR.blockWeight]⟩

theorem segreLiftMap_monomial (W : Ideal (MRing ι F)) (s : (Σ c, segreIdx ι c) →₀ ℕ) :
    ∀ r : F, ∃ a, segreLiftMap ι F W (monomial s r) =
      Polynomial.X ^ (Finsupp.weight (NumbersDVR.blockWeight (segreIdx ι)) s (Sum.inl ())) *
        Polynomial.C a := by
  refine Finsupp.induction s ?_ ?_
  · intro r
    refine ⟨algebraMap F _ r, ?_⟩
    simp [segreLiftMap, Polynomial.algebraMap_apply]
  · intro v n s _ _ ih r
    obtain ⟨a, ha⟩ := ih r
    obtain ⟨β, hβ⟩ := segreLiftVal_eq W v
    refine ⟨β ^ n * a, ?_⟩
    have hm : (monomial (Finsupp.single v n + s) r : MRing (segreIdx ι) F) =
        X v ^ n * monomial s r := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    rw [hm, map_mul, map_pow, ha, segreLiftMap, aeval_X, hβ, map_add (f := _), Pi.add_apply,
      Finsupp.weight_single, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
    ring

theorem segreLiftMap_of_isWeightedHomogeneous (W : Ideal (MRing ι F)) {f : MRing (segreIdx ι) F}
    {e : Unit ⊕ K → ℕ} (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight (segreIdx ι)) f e) :
    ∃ a, segreLiftMap ι F W f = Polynomial.X ^ e (Sum.inl ()) * Polynomial.C a := by
  classical
  choose a ha using fun s => segreLiftMap_monomial W s (AddMonoidAlgebra.coeff f s)
  refine ⟨∑ s ∈ f.support, a s, ?_⟩
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [ha s, hf (mem_support_iff.mp hs)]

end

theorem SegreLiftComap.proof : SegreLiftComap.Statement := by
  intro F _ K _ _ ι _ W' hW' hrel
  classical
  have := hW'.isPrime
  have hW : IsMultiProjPrime (W'.comap (segreIncl ι F)) := by
    refine ⟨inferInstance, ?_, ?_⟩
    · intro f hf b
      rw [Ideal.mem_comap, segreIncl_weightedHomogeneousComponent]
      exact hW'.multiHomog _ hf _
    · intro k
      obtain ⟨i, hi⟩ := hW'.relevant (Sum.inr k)
      exact ⟨i, by rwa [Ideal.mem_comap, segreIncl, rename_X]⟩
  refine ⟨hW, ?_⟩
  set W := W'.comap (segreIncl ι F) with hWdef

  choose c' hc using fun k => hW'.relevant (Sum.inr k)
  let c : ∀ k, ι k := c'
  let D := MRing (segreIdx ι) F ⧸ W'
  let L := FractionRing D
  let π : MRing (segreIdx ι) F →+* L := (algebraMap D L).comp (Ideal.Quotient.mk W')
  have hπ : ∀ f, π f = 0 ↔ f ∈ W' := by
    intro f
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (IsFractionRing.injective D L).eq_iff' (map_zero _)
  have hmc : segreMon (R := F) c ∉ W' := by
    intro h
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact hc k hk
  have hYc : segreY (R := F) c ∉ W' := by
    intro h
    obtain ⟨d, hd⟩ := hW'.relevant (Sum.inl ())
    have hr : segreY c * segreMon d - segreY d * segreMon c ∈ W' := hrel ⟨c, d, rfl⟩
    have : segreY (R := F) d * segreMon c ∈ W' := by
      have := W'.sub_mem (W'.mul_mem_right (segreMon d) h) hr
      rwa [sub_sub_cancel] at this
    exact (hW'.isPrime.mem_or_mem this).elim hd hmc
  have hMc : π (segreMon c) ≠ 0 := fun h => hmc ((hπ _).mp h)
  let u : L := π (segreY c) / π (segreMon c)
  have hu : u ≠ 0 := div_ne_zero (fun h => hYc ((hπ _).mp h)) hMc
  let j : MRing ι F ⧸ W →+* D :=
    Ideal.quotientMap W' (segreIncl ι F : MRing ι F →+* MRing (segreIdx ι) F) le_rfl
  have hj : Function.Injective j := Ideal.quotientMap_injective' le_rfl
  have hjmk : ∀ x, j (Ideal.Quotient.mk W x) = Ideal.Quotient.mk W' (segreIncl ι F x) :=
    fun x => Ideal.quotientMap_mk
  let Φ : Polynomial (MRing ι F ⧸ W) →+* L := Polynomial.eval₂RingHom ((algebraMap D L).comp j) u
  have hΦ : ∀ a, Φ (Polynomial.C a) = algebraMap D L (j a) := fun a => by
    simp [Φ]
  have hkey : ∀ f, Φ (segreLiftMap ι F W f) = π f := by
    have : Φ.comp (segreLiftMap ι F W : MRing (segreIdx ι) F →+* Polynomial (MRing ι F ⧸ W)) = π := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
      · simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_C,
          Polynomial.algebraMap_apply, hΦ]
        rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, hjmk, segreIncl, rename_C]
        rfl
      · rcases v with ⟨⟨⟨⟩⟩ | k, i⟩
        · have hs : π (segreY c) * π (segreMon i) = π (segreY i) * π (segreMon c) := by
            have := (hπ _).mpr (hrel ⟨c, i, rfl⟩)
            rwa [map_sub, map_mul, map_mul, sub_eq_zero] at this
          have hinc : segreIncl ι F (∏ k, X ⟨k, i k⟩) = segreMon i := by
            simp [segreIncl, segreMon, map_prod]
          simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_X, segreLiftVal,
            map_mul, hΦ]
          simp only [Φ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
          rw [hjmk, hinc]
          change u * π (segreMon i) = π (segreY i)
          rw [div_mul_eq_mul_div, div_eq_iff hMc, hs]
        · simp only [RingHom.comp_apply, RingHom.coe_coe, segreLiftMap, aeval_X, segreLiftVal, hΦ]
          rw [hjmk, segreIncl, rename_X]
          rfl
    intro f
    exact RingHom.congr_fun this f
  ext f
  rw [segreLift, RingHom.mem_ker]
  constructor
  · intro hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight (segreIdx ι)) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f), map_sum]
    refine Finset.sum_eq_zero fun e _ => ?_
    obtain ⟨a, ha⟩ := segreLiftMap_of_isWeightedHomogeneous W
      (weightedHomogeneousComponent_isWeightedHomogeneous
        (w := NumbersDVR.blockWeight (segreIdx ι)) e f)
    have h0 : Φ (Polynomial.X ^ e (Sum.inl ()) * Polynomial.C a) = 0 := by
      rw [← ha, hkey]
      exact (hπ _).mpr (hW'.multiHomog f hf e)
    rw [map_mul, map_pow, hΦ] at h0
    have h1 := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ (by simpa [Φ] using hu))
    have h2 : j a = 0 := (IsFractionRing.injective D L) (by rw [h1, map_zero])
    have h3 : a = 0 := hj (by rw [h2, map_zero])
    rw [ha, h3, map_zero, mul_zero]
  · intro hf
    exact (hπ f).mp (by rw [← hkey, hf, map_zero])

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XBaseMemMIdealOverGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

section Zero

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem X_mem_primeOf_of_eq_zero {i : Fin (N + 1)} (hi : x i = 0) :
    (X i : Kleiman.Poly S N) ∈ Kleiman.primeOf (S := S) x := by
  rw [Kleiman.primeOf_eq, RingHom.mem_ker]
  simp [Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, hi]

theorem X_base_mem_mIdealOver_graph (s : Fin m → Ω) {i : Fin (N + 1)} (hi : x i = 0) :
    (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) S) ∈ mIdealOver S (graphVec x s) := by
  change mConeMapOver S (graphVec x s) (X _) = 0
  simp [mConeMapOver, hi]
  exact hi

end Zero

theorem NefEq.proof (hC : CurveComap.Statement) (hL : CurveLift.Statement) (hD : DegEq.Statement) :
    NefEq.Statement := by
  intro k _ N Ω _ _ x Q n m s hgen
  by_cases hx : ∃ i, x i ≠ 0
  · constructor
    · intro hnef W hW hle hrel
      have hsub := (hC k N Ω x Q n m s hx hgen W hW hle 1).mp hrel
      rw [hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]
      exact hnef _ bot_le hsub
    · intro hnef pp _ hsub
      obtain ⟨W, hW, hle, rfl⟩ := hL k N Ω x Q n m s hx hgen pp 1 hsub
      rw [← hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]
      exact hnef W hW hle ((hC k N Ω x Q n m s hx hgen W hW hle 1).mpr hsub)
  · push Not at hx
    constructor
    · intro _ W hW hle _
      exfalso
      obtain ⟨i, hi⟩ := hW.relevant baseBlock
      exact hi (hle (X_base_mem_mIdealOver_graph s (hx i)))
    · intro _ pp _ hsub
      exfalso
      obtain ⟨i, hi⟩ := hsub.relevant
      exact hi (hsub.le (X_mem_primeOf_of_eq_zero (hx i)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FinrankSectionsOverEqH0
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver cechHc cechZc cechBc quotPart GlobalSectionsComparisonStatement)

noncomputable section

theorem altSum_eq_of_vanish (f : ℕ → ℕ) (B : ℕ) (h : ∀ i, 1 ≤ i → f i = 0) :
    ∑ i ∈ Finset.range (B + 1), (-1 : ℚ) ^ i * (f i : ℚ) = f 0 := by
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun i _ => by rw [h (i + 1) (by omega)]; simp]
  simp

theorem finrank_sectionsOver_eq_H0 (hB : GlobalSectionsComparisonStatement) {F : Type} [Field F] {K : Type} [Fintype K] [LinearOrder K]
    {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (n : K → ℤ) :
    Module.finrank F (secOver F y n) = Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) n 0) := by
  obtain ⟨φ, hinj, hrange, -⟩ := hB F K ι Ω y n hy
  let e1 : ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) ≃ₗ[F] secOver F y n :=
    (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hbot : (cechBc ι (quotPart F (mIdealOver F y)) n 0).comap
      (cechZc ι (quotPart F (mIdealOver F y)) n 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  let e2 : cechHc ι (quotPart F (mIdealOver F y)) n 0 ≃ₗ[F] ↥(cechZc ι (quotPart F (mIdealOver F y)) n 0) :=
    Submodule.quotEquivOfEqBot _ hbot
  rw [← e1.finrank_eq, e2.finrank_eq]

theorem SectionsPoly.proof (hB : GlobalSectionsComparisonStatement) (hE : EulerPoly.Statement) (hM : MultiSerre.Statement)
    (hR : RayVanish.Statement) : SectionsPoly.Statement := by
  intro F _ K _ dK ι _ Ω _ _ y k₀ hmod
  let lo : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain rfl : dK = @LinearOrder.toDecidableEq K lo := Subsingleton.elim _ _
  have hV : NumbersDVR.IsMultiHomogIdeal (mIdealOver F y) := isMultiHomogIdeal_mIdealOver y
  obtain ⟨B, χ, -, -, hχ⟩ := hE F K ι (mIdealOver F y) hV
  have key : ∀ m : K → ℤ, (∀ i : ℕ, 1 ≤ i → Subsingleton (cechHc ι (quotPart F (mIdealOver F y)) m i)) →
      (Module.finrank F (secOver F y m) : ℚ) = eval (fun k => (m k : ℚ)) χ := by
    intro m hm
    rw [← hχ m, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    refine (altSum_eq_of_vanish (fun i => Module.finrank F (cechHc ι (quotPart F (mIdealOver F y)) m i)) B
      fun i hi => ?_).symm
    have := hm i hi
    exact Module.finrank_zero_of_subsingleton
  refine ⟨χ, ?_, fun β => ?_⟩
  · filter_upwards [hM F K ι (mIdealOver F y) hV] with m hm
    rw [← hm.2, ← key m hm.1, finrank_sectionsOver_eq_H0 hB y hmod.1 m]
    push_cast
    rfl
  · filter_upwards [hR F K ι Ω y k₀ hmod β] with c hc
    exact key _ hc

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AltSumEqOfEventually
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

noncomputable section

section Poly

variable {K : Type}

theorem eval_bind₁_shift (p : MvPolynomial K ℚ) (a z : K → ℚ) :
    eval z (bind₁ (fun k => X k - C (a k)) p) = eval (z - a) p := by
  show eval₂Hom (RingHom.id ℚ) z _ = _
  rw [eval₂Hom_bind₁]
  have hfun : (fun i => eval₂Hom (RingHom.id ℚ) z (X i - C (a i))) = z - a := funext fun k => by simp
  rw [hfun]
  rfl

theorem altSum_eq_of_eventually (p : MvPolynomial K ℚ) {n : ℕ} (δ : Fin n → K → ℤ) (D : ℚ)
    (h : ∀ᶠ m : K → ℤ in atTop,
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D)
    (z : K → ℤ) :
    ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((z - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
  classical
  let q : MvPolynomial K ℚ := ∑ T : Finset (Fin n),
    C ((-1 : ℚ) ^ T.card) * bind₁ (fun k => X k - C (((∑ i ∈ T, δ i) k : ℤ) : ℚ)) p
  have hq : ∀ w : K → ℤ, eval (fun k => (w k : ℚ)) q =
      ∑ T : Finset (Fin n), (-1 : ℚ) ^ T.card * eval (fun k => (((w - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [q, map_sum, map_mul, eval_C, eval_bind₁_shift]
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 3
    funext k
    simp only [Pi.sub_apply, Int.cast_sub]
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp h
  let s : K → Set ℚ := fun k => (fun t : ℤ => (t : ℚ)) '' Set.Ici (m₀ k)
  have hs : ∀ k, (s k).Infinite := fun k =>
    (Set.Ici_infinite (m₀ k)).image (fun a _ b _ hab => Int.cast_injective hab)
  have hqD : q = C D := by
    refine funext_set s hs fun w hw => ?_
    have hw' : ∀ k, ∃ t : ℤ, m₀ k ≤ t ∧ (t : ℚ) = w k := fun k => hw k (Set.mem_univ k)
    choose m hm1 hm2 using hw'
    have hwm : w = fun k => (m k : ℚ) := funext fun k => (hm2 k).symm
    rw [hwm, hq, eval_C]
    exact hm₀ m hm1
  rw [← hq, hqD, eval_C]

end Poly

theorem NumModel.proof (hT : TensorRealise.Statement) (hS : SectionsPoly.Statement) (hD : ModelDim.Statement) :
    NumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n L δ hL hsub
  classical
  obtain ⟨i₀, hi₀⟩ := hmod.1 k₀
  have hj : x (e i₀) ≠ 0 := by
    rw [hx]
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi₀
  have hP := isMultiProjPrime_mIdealOver (S := F) y hmod.1
  have hdim := (hD F K ι Ω y k₀ N e x hx hmod n).mp hsub
  obtain ⟨p, hpH, hpS⟩ := hS F K ι Ω y k₀ hmod
  have hMD := (FieldNumbers.MixedDiffConst.full F K ι (mIdealOver F y) hP.multiHomog hP.relevant n hdim).1 δ
  set D := NumbersDVR.intNum F (mIdealOver F y) δ with hD_def

  have hev : ∀ᶠ m : K → ℤ in atTop, ∑ T : Finset (Fin n),
      (-1 : ℚ) ^ T.card * eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p = D := by
    have h2 : ∀ T : Finset (Fin n), ∀ᶠ m : K → ℤ in atTop,
        (NumbersDVR.hilbFn (mIdealOver F y) (m - ∑ i ∈ T, δ i) : ℚ) =
          eval (fun k => (((m - ∑ i ∈ T, δ i) k : ℤ) : ℚ)) p := fun T =>
      ((tendsto_atTop_add_const_right atTop (-(∑ i ∈ T, δ i)) tendsto_id).eventually hpH).mono
        fun m hm => by simpa only [id, sub_eq_add_neg] using hm
    filter_upwards [hMD, eventually_all.mpr h2] with m h1 h2
    rw [mixedDiff_eq_sum] at h1
    have h1' := congrArg (Int.cast : ℤ → ℚ) h1
    push_cast at h1'
    rw [← h1']
    exact Finset.sum_congr rfl fun T _ => by rw [h2 T]
  have hall := altSum_eq_of_eventually p δ (D : ℚ) hev

  have hsecs : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      ((restrLen (primeOf (S := F) x)
          ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys F x (c : ℤ))) : ℤ) : ℚ) =
        eval (fun k => (((∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k : ℤ) : ℚ)) p := fun T => by
    filter_upwards [hT F K ι Ω y k₀ N e x hx hmod n L δ hL T, hpS (∑ i ∈ T, δ i)] with c h1 h2
    rw [restrLen_primeOf_eq_finrank x hj, h1, ← h2]
    simp
  have hfin : ∀ᶠ c : ℕ in atTop, interSum (primeOf (S := F) x) (fun i => (L i).toSubSystem) c = D := by
    filter_upwards [eventually_all.mpr hsecs] with c hc
    apply Int.cast_injective (α := ℚ)
    rw [interSum, ← hall (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀)]
    push_cast
    refine Fintype.sum_bijective compl compl_involutive.bijective _ _ fun T => ?_
    have hcard : Tᶜ.card = n - T.card := by rw [Finset.card_compl, Fintype.card_fin]
    have hvec : (∑ i, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) - ∑ i ∈ Tᶜ, δ i =
        ∑ i ∈ T, δ i + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
      rw [← Finset.sum_add_sum_compl T δ]
      abel
    rw [hc T, hcard, hvec]
  unfold interNum
  exact (tendsto_const_nhds.congr' (hfin.mono fun c h => h.symm)).limUnder_eq

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
