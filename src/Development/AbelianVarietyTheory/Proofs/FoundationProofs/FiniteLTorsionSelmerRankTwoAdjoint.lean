module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.UnramifiedCocycleIsCoboundaryOfBernoulliUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

abbrev ResL (c : Coef l) : Type := c.O ⧸ Ideal.span {((l : ℕ) : c.O)}


open Classical in
def redL (c : Coef l) (x : Qbar l) : ResL c :=
  if h : x ∈ c.O then Ideal.Quotient.mk _ ⟨x, h⟩ else 0

theorem redL_of_mem (c : Coef l) {x : Qbar l} (h : x ∈ c.O) :
    redL c x = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)}) ⟨x, h⟩ := by
  simp [redL, h]

theorem redL_add (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x + y) = redL c x + redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.add_mem hx hy), ← map_add (f := _)]; rfl

theorem redL_sub (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x - y) = redL c x - redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.sub_mem hx hy), ← map_sub]; rfl

theorem redL_mul (c : Coef l) {x y : Qbar l} (hx : x ∈ c.O) (hy : y ∈ c.O) :
    redL c (x * y) = redL c x * redL c y := by
  rw [redL_of_mem c hx, redL_of_mem c hy, redL_of_mem c (c.O.mul_mem hx hy), ← map_mul]; rfl

theorem redL_zero (c : Coef l) : redL c 0 = 0 := by
  rw [redL_of_mem c c.O.zero_mem]; exact map_zero _

theorem redL_one (c : Coef l) : redL c 1 = 1 := by
  rw [redL_of_mem c c.O.one_mem]; exact map_one _

theorem redL_eq_zero_iff (c : Coef l) {x : Qbar l} (h : x ∈ c.O) :
    redL c x = 0 ↔ ∃ o ∈ c.O, x = (l : Qbar l) * o := by
  rw [redL_of_mem c h, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨o, ho⟩
    refine ⟨o, o.2, ?_⟩
    have : ((o * ((l : ℕ) : c.O) : c.O) : Qbar l) = x := congrArg Subtype.val ho
    rw [← this]; push_cast; ring
  · rintro ⟨o, ho, rfl⟩
    refine ⟨⟨o, ho⟩, Subtype.ext ?_⟩
    push_cast; ring

def ResPlane (c : Coef l) : Type := Fin 2 → ResL c

instance (c : Coef l) : AddCommGroup (ResPlane c) := inferInstanceAs (AddCommGroup (Fin 2 → ResL c))
instance (c : Coef l) : TopologicalSpace (ResPlane c) := ⊥
instance (c : Coef l) : DiscreteTopology (ResPlane c) := ⟨rfl⟩

theorem resL_natCast_l (c : Coef l) : ((l : ℕ) : ResL c) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : c.O)})), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

theorem resPlane_smul_eq_zero (c : Coef l) (m : ResPlane c) : (l ^ 1) • m = 0 := by
  funext i
  show (l ^ 1) • (m i : ResL c) = 0
  rw [nsmul_eq_mul, pow_one, resL_natCast_l, zero_mul]

instance (c : Coef l) : Module (ZMod (l ^ 1)) (ResPlane c) := AddCommGroup.zmodModule (resPlane_smul_eq_zero c)

instance (c : Coef l) : Finite (ResPlane c) := by
  have : CharZero c.O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l c.O).1
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have := (UpperTheory.V.X.So.levFacts l c.O ((l : ℕ) : c.O) hl0 (ResL c) ⟨LinearEquiv.refl _ _⟩).1
  exact inferInstanceAs (Finite (Fin 2 → ResL c))

def wRed (c : Coef l) (W : R2 Ω l) (s : G ℚ Ω) : Matrix (Fin 2) (Fin 2) (ResL c) := fun i j => redL c (mat W s i j)

def resMV (c : Coef l) (B : Matrix (Fin 2) (Fin 2) (ResL c)) : ResPlane c →+ ResPlane c where
  toFun m := B *ᵥ (m : Fin 2 → ResL c)
  map_zero' := Matrix.mulVec_zero B
  map_add' m m' := Matrix.mulVec_add B m m'

theorem wRed_one (c : Coef l) (W : R2 Ω l) : wRed c W 1 = 1 := by
  ext i j
  simp only [wRed, mat, map_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact redL_one c
  · exact redL_zero c

theorem wRed_mul (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (s t : G ℚ Ω) :
    wRed c W (s * t) = wRed c W s * wRed c W t := by
  ext i j
  have e : mat W (s * t) i j = mat W s i 0 * mat W t 0 j + mat W s i 1 * mat W t 1 j := by
    simp only [mat, map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp only [wRed, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e, redL_add c (c.O.mul_mem (hO _ _ _) (hO _ _ _)) (c.O.mul_mem (hO _ _ _) (hO _ _ _)),
    redL_mul c (hO _ _ _) (hO _ _ _), redL_mul c (hO _ _ _) (hO _ _ _)]

def resAct (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) :
    G ℚ Ω →* (ResPlane c →ₗ[ZMod (l ^ 1)] ResPlane c) where
  toFun s := AddMonoidHom.toZModLinearMap (l ^ 1) (resMV c (wRed c W s))
  map_one' := by
    refine LinearMap.ext fun m => ?_
    show wRed c W 1 *ᵥ (m : Fin 2 → ResL c) = m
    rw [wRed_one]; exact Matrix.one_mulVec _
  map_mul' s t := by
    refine LinearMap.ext fun m => ?_
    show wRed c W (s * t) *ᵥ (m : Fin 2 → ResL c) = wRed c W s *ᵥ (wRed c W t *ᵥ (m : Fin 2 → ResL c))
    rw [wRed_mul c W hO]; exact (Matrix.mulVec_mulVec _ _ _).symm

theorem resAct_apply (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω) (m : ResPlane c) :
    resAct c W hO s m = (wRed c W s *ᵥ (m : Fin 2 → ResL c) : Fin 2 → ResL c) := rfl

theorem resAct_eq_one (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) {a : G ℚ Ω} (ha : W a = 1) :
    resAct c W hO a = 1 := by
  refine LinearMap.ext fun m => ?_
  show wRed c W a *ᵥ (m : Fin 2 → ResL c) = m
  have : wRed c W a = wRed c W 1 := by unfold wRed mat; rw [ha, map_one]
  rw [this, wRed_one]; exact Matrix.one_mulVec _

def resRep (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) :
    Representation (ZMod (l ^ 1)) (GS Ω (S : Set Pl)) (ResPlane c) :=
  QuotientGroup.lift (NS Ω (S : Set Pl)) (resAct c W hO) fun a ha =>
    resAct_eq_one c W hO (hN a ((QuotientGroup.eq_one_iff a).2 ha))

theorem resRep_toGS (c : Coef l) (W : R2 Ω l) (hO : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) (s : G ℚ Ω) :
    resRep c W hO S hN (toGS Ω (S : Set Pl) s) = resAct c W hO s := rfl

def descS (S : Finset Pl) {X : Type} (f : G ℚ Ω → X) : GS Ω (S : Set Pl) → X := fun g => f g.out

def resCoc (c : Coef l) (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l) (y : Fin 2 → Qbar l) : G ℚ Ω → ResPlane c :=
  fun s i => redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i)

theorem resCoc_mul_ker (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s a : G ℚ Ω)
    (ha : a ∈ (toGS Ω (S : Set Pl)).ker) : resCoc c W z y (s * a) = resCoc c W z y s := by
  obtain ⟨-, h2, -, h4, -, -⟩ := hz
  funext i
  have hWa : mat W (s * a) = mat W s := by simp only [mat, map_mul, hN a ha, mul_one]
  have hza : (mat W s *ᵥ z a) i ∈ c.O := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hO _ _ _) (h4 a ha 0)) (c.O.mul_mem (hO _ _ _) (h4 a ha 1))
  have hd : z (s * a) i - z s i ∈ c.O := by
    have := c.O.add_mem (h2 s a i) hza
    simpa using this
  have e : (l : Qbar l) * z (s * a) i - (mat W (s * a) *ᵥ y - y) i =
      ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) + (l : Qbar l) * (z (s * a) i - z s i) := by
    rw [hWa]; ring
  show redL c _ = redL c _
  rw [e, redL_add c (hzy s i) (c.O.mul_mem (c.O.natCast_mem l) hd), (redL_eq_zero_iff c (c.O.mul_mem (c.O.natCast_mem l) hd)).2 ⟨_, hd, rfl⟩, add_zero]

theorem descS_resCoc_toGS (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s : G ℚ Ω) :
    descS S (resCoc c W z y) (toGS Ω (S : Set Pl) s) = resCoc c W z y s := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (NS Ω (S : Set Pl)) s
  show resCoc c W z y ((toGS Ω (S : Set Pl) s).out) = _
  have e : (toGS Ω (S : Set Pl) s).out = s * h := hh
  rw [e]
  exact resCoc_mul_ker c W S A hO hN hz y hzy s h ((QuotientGroup.eq_one_iff (h : G ℚ Ω)).2 h.2)

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaloisRepLocallyConstantModPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaloisRepLocallyConstantModPrimePow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.Ord2.locConst_mod_pow :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l), Continuous W →
      (∀ s i j, mat W s i j ∈ c.O) → ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j,
        ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o := by
  intro l _ Ω _ _ c W hW hO n s
  have hc : ∀ i j, Continuous fun t => mat W t i j := fun i j =>
    ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (Qbar l))).comp hW).matrix_elem i j
  have hr : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := by
    rw [norm_pos_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
  have hev : ∀ᶠ t in nhds s, mat W t i j ∈ Metric.closedBall (mat W s i j) ‖((l : ℕ) : Qbar l) ^ n‖ :=
    (hc i j).continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)
  filter_upwards [hev] with t ht
  rw [Metric.mem_closedBall, dist_eq_norm] at ht
  have hmem : mat W t i j - mat W s i j ∈ c.O := c.O.sub_mem (hO t i j) (hO s i j)
  obtain ⟨o, ho⟩ := (GlobalTheory.Coef.norm_le_norm_pow_iff_dvd l c n ⟨_, hmem⟩).1 ht
  refine ⟨(o : Qbar l), o.2, ?_⟩
  have := congrArg (fun x : c.O => (x : Qbar l)) ho
  simpa using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaloisRepLocallyConstantModPrimePowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGaloisRep_locallyConstant_modPrimePow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o := by
  first | exact @GlobalTheory.Ord2.locConst_mod_pow | exact GlobalTheory.Ord2.locConst_mod_pow | (intros; apply GlobalTheory.Ord2.locConst_mod_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousResiduePlaneGaloisRepUnramifiedOutside
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousResiduePlaneGaloisRepUnramifiedOutside
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem resRep_contAction : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  intro l _ Ω _ _ S W c hO hN hW

  have hred : ∀ m : ResPlane c, Continuous fun s : G ℚ Ω => resAct c W hO s m := by
    intro m
    rw [continuous_iff_continuousAt]
    intro s
    refine tendsto_nhds_of_eventually_eq ?_
    filter_upwards [locConst_mod_pow l Ω c W hW hO 1 s] with t ht
    have hw : wRed c W t = wRed c W s := by
      ext i j
      obtain ⟨o, ho, e⟩ := ht i j
      have hd : mat W t i j - mat W s i j ∈ c.O := c.O.sub_mem (hO t i j) (hO s i j)
      have h0 : redL c (mat W t i j - mat W s i j) = 0 :=
        (redL_eq_zero_iff c hd).2 ⟨o, ho, by rw [e, pow_one]⟩
      rw [redL_sub c (hO t i j) (hO s i j)] at h0
      exact sub_eq_zero.1 h0
    rw [resAct_apply, resAct_apply, hw]
  have hq : ∀ m : ResPlane c, Continuous fun g : GS Ω (S : Set Pl) => resRep c W hO S hN g m := by
    intro m
    rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    exact hred m
  show Continuous fun p : GS Ω (S : Set Pl) × ResPlane c => (resRep c W hO S hN p.1) p.2
  exact continuous_prod_of_discrete_right.2 hq

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousResiduePlaneGaloisRepUnramifiedOutsideStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_residuePlaneGaloisRep_unramifiedOutside : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  first | exact @GlobalTheory.Ord2.resRep_contAction | exact GlobalTheory.Ord2.resRep_contAction | (intros; apply GlobalTheory.Ord2.resRep_contAction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedSelmerCochainMemContinuousCocyclesOfCont
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedSelmerCochainMemContinuousCocyclesOfCont
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.ResidualCocycleReduction

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem redL_add_l_mul (c : Coef l) {x d : Qbar l} (hx : x ∈ c.O) (hd : d ∈ c.O) :
    redL c (x + (l : Qbar l) * d) = redL c x := by
  rw [redL_add c hx (c.O.mul_mem (c.O.natCast_mem l) hd),
    (redL_eq_zero_iff c (c.O.mul_mem (c.O.natCast_mem l) hd)).2 ⟨d, hd, rfl⟩, add_zero]

theorem redL_mulVec (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (v : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hv : ∀ j, v j ∈ c.O) (i : Fin 2) :
    redL c ((M *ᵥ v) i) = ((fun i j => redL c (M i j)) *ᵥ (fun j => redL c (v j))) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [redL_add c (c.O.mul_mem (hM _ _) (hv _)) (c.O.mul_mem (hM _ _) (hv _)),
    redL_mul c (hM _ _) (hv _), redL_mul c (hM _ _) (hv _)]

theorem mulVec_mem (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (v : Fin 2 → Qbar l)
    (hM : ∀ i j, M i j ∈ c.O) (hv : ∀ j, v j ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM _ _) (hv _)) (c.O.mul_mem (hM _ _) (hv _))

theorem resCoc_mul (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) (y : Fin 2 → Qbar l)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) (s t : G ℚ Ω) :
    resCoc c W z y (s * t) = resCoc c W z y s + resAct c W hO s (resCoc c W z y t) := by
  obtain ⟨-, h2, -, -, -, -⟩ := hz
  funext i
  have hM : mat W (s * t) = mat W s * mat W t := by simp only [mat, map_mul, Units.val_mul]
  set a : G ℚ Ω → Fin 2 → Qbar l := fun s i => (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i with ha
  have e : (l : Qbar l) * z (s * t) i - (mat W (s * t) *ᵥ y - y) i =
      (a s i + (mat W s *ᵥ a t) i) + (l : Qbar l) * (z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
    have ea : a t = (l : Qbar l) • z t - (mat W t *ᵥ y - y) := by
      funext j; simp only [ha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hM, ea, ← Matrix.mulVec_mulVec]
    simp only [ha, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hat : ∀ j, a t j ∈ c.O := fun j => hzy t j
  show redL c _ = redL c (a s i) + (wRed c W s *ᵥ (fun j => redL c (a t j))) i
  rw [e, redL_add_l_mul c (c.O.add_mem (hzy s i) (mulVec_mem c _ _ (hO s) hat i)) (h2 s t i),
    redL_add c (hzy s i) (mulVec_mem c _ _ (hO s) hat i), redL_mulVec c _ _ (hO s) hat i]
  rfl

theorem resCoc_locConst (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hlc : ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) {y : Fin 2 → Qbar l} (hy : VecE c y)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) :
    IsLocallyConstant (resCoc c W z y) := by
  obtain ⟨-, -, h3, -, -, -⟩ := hz
  obtain ⟨k, hk⟩ := hy
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun s => ?_
  filter_upwards [h3 s, hlc (k + 1) s] with t ht hW
  funext i
  choose o ho he using hW
  have e : (l : Qbar l) * z t i - (mat W t *ᵥ y - y) i =
      ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) + (l : Qbar l) *
        ((z t i - z s i) - (o i 0 * ((l : Qbar l) ^ k * y 0) + o i 1 * ((l : Qbar l) ^ k * y 1))) := by
    have h0 : mat W t i 0 = mat W s i 0 + (l : Qbar l) ^ (k + 1) * o i 0 := by rw [← he i 0]; ring
    have h1 : mat W t i 1 = mat W s i 1 + (l : Qbar l) ^ (k + 1) * o i 1 := by rw [← he i 1]; ring
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [h0, h1]; ring
  show redL c _ = redL c _
  rw [e, redL_add_l_mul c (hzy s i) (c.O.sub_mem (ht i) (c.O.add_mem (c.O.mul_mem (ho i 0) (hk 0))
    (c.O.mul_mem (ho i 1) (hk 1))))]

theorem reduced_selmer_cochain_mem_continuous_cocycles_S (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1)
    (hlc : ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o)
    {z : G ℚ Ω → Fin 2 → Qbar l} (hz : z ∈ divSelCoc c W S A) {y : Fin 2 → Qbar l} (hy : VecE c y)
    (hzy : ∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) :
    descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  have hd : ∀ s, descS S (resCoc c W z y) (toGS Ω (S : Set Pl) s) = resCoc c W z y s :=
    descS_resCoc_toGS c W S A hO hN hz y hzy
  refine ⟨?_, fun g h => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk (NS Ω (S : Set Pl))).continuous_iff]
    have : descS S (resCoc c W z y) ∘ (QuotientGroup.mk : G ℚ Ω → GS Ω (S : Set Pl)) = resCoc c W z y :=
      funext fun s => hd s
    rw [this]
    exact (resCoc_locConst c W S A hlc hz hy hzy).continuous
  · obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective h
    have e1 : ((s : GS Ω (S : Set Pl)) * (t : GS Ω (S : Set Pl))) = toGS Ω (S : Set Pl) (s * t) := rfl
    have e2 : (s : GS Ω (S : Set Pl)) = toGS Ω (S : Set Pl) s := rfl
    have e3 : (t : GS Ω (S : Set Pl)) = toGS Ω (S : Set Pl) t := rfl
    rw [e1, e2, e3, hd, hd, hd, resRep_toGS]
    exact resCoc_mul c W S A hO hz y hzy s t

theorem _root_.GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O)
    (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ∀ z ∈ divSelCoc c W S A,
    ∀ y : Fin 2 → Qbar l, VecE c y → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  intro l _ Ω _ _ S A W c hO hN hW z hz y hy hzy
  exact GlobalTheory.Ord2.ResidualCocycleReduction.reduced_selmer_cochain_mem_continuous_cocycles_S c W S A hO hN (GlobalTheory.T.integralGaloisRep_locallyConstant_modPrimePow l Ω c W hW hO) hz hy hzy

end GlobalTheory.Ord2.ResidualCocycleReduction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedSelmerCochainMemContinuousCocyclesOfContStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduced_selmer_cochain_mem_continuous_cocycles_of_cont : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ∀ z ∈ divSelCoc c W S A, ∀ y : Fin 2 → Qbar l, VecE c y → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) → descS S (resCoc c W z y) ∈ Z1 (resRep c W hO S hN) := by
  first | exact @GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous | exact GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous | (intros; apply GlobalTheory.Ord2.descS_resCoc_mem_z1_of_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivCoboundaryOfReducedCocyclesCohomologous
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivCoboundaryOfReducedCocyclesCohomologous
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

theorem divCob_of_resCoc_cohom : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l)
    (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l),
    VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) →
    (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) →
    (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) →
    z - z' ∈ divCob c W := by
  intro l _ Ω _ _ W c hO z z' y y' hy hy' hz hz' ⟨m, hm⟩

  have hlift : ∀ i, ∃ x : Qbar l, ∃ hx : x ∈ c.O, redL c x = m i := by
    intro i
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (m i : ResL c)
    exact ⟨a.1, a.2, by rw [redL_of_mem c a.2]; exact ha⟩
  choose u hu hum using hlift
  have hl0 : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hWu : ∀ s i, (mat W s *ᵥ u) i ∈ c.O := by
    intro s i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact c.O.add_mem (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1))
  have hWuR : ∀ s i, redL c ((mat W s *ᵥ u) i) = (resAct c W hO s m) i := by
    intro s i
    rw [resAct_apply]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, wRed]
    rw [redL_add c (c.O.mul_mem (hO _ _ _) (hu 0)) (c.O.mul_mem (hO _ _ _) (hu 1)),
      redL_mul c (hO _ _ _) (hu 0), redL_mul c (hO _ _ _) (hu 1), hum 0, hum 1]
  have key : ∀ s i, ∃ o ∈ c.O, ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
      ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i) = (l : Qbar l) * o := by
    intro s i
    have h1 := hz s i
    have h2 := hz' s i
    have h3 : (mat W s *ᵥ u) i - u i ∈ c.O := c.O.sub_mem (hWu s i) (hu i)
    have hmem := c.O.sub_mem (c.O.sub_mem h1 h2) h3
    refine (redL_eq_zero_iff c hmem).1 ?_
    have e := congrFun (hm s) i
    rw [redL_sub c (c.O.sub_mem h1 h2) h3, redL_sub c h1 h2, redL_sub c (hWu s i) (hu i), hWuR, hum]
    have e' : redL c ((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
        redL c ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) = (resAct c W hO s m) i - m i := e
    rw [e', sub_self]
  choose o ho hoe using key
  refine ⟨(l : Qbar l)⁻¹ • (y - y' + u), ?_, fun s i => ?_⟩
  · obtain ⟨k, hk⟩ := hy
    obtain ⟨k', hk'⟩ := hy'
    refine ⟨k + k' + 1, fun i => ?_⟩
    have e : (l : Qbar l) ^ (k + k' + 1) * ((l : Qbar l)⁻¹ • (y - y' + u)) i =
        (l : Qbar l) ^ k' * ((l : Qbar l) ^ k * y i) - (l : Qbar l) ^ k * ((l : Qbar l) ^ k' * y' i)
          + (l : Qbar l) ^ (k + k') * u i := by
      simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
      rw [pow_succ]; field_simp; ring
    rw [e]
    exact c.O.add_mem (c.O.sub_mem (c.O.mul_mem (natPow_mem c _) (hk i)) (c.O.mul_mem (natPow_mem c _) (hk' i)))
      (c.O.mul_mem (natPow_mem c _) (hu i))
  · have e : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i = o s i := by
      have h := hoe s i
      have e2 : (z - z') s i - (mat W s *ᵥ ((l : Qbar l)⁻¹ • (y - y' + u)) - (l : Qbar l)⁻¹ • (y - y' + u)) i =
          (l : Qbar l)⁻¹ * (((l : Qbar l) * z s i - (mat W s *ᵥ y - y) i) -
            ((l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i) - ((mat W s *ᵥ u) i - u i)) := by
        simp only [Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        field_simp; ring
      rw [e2, h, ← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
    rw [e]; exact ho s i

end GlobalTheory.Ord2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivCoboundaryOfReducedCocyclesCohomologousStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divCoboundary_of_reducedCocycles_cohomologous : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l), VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) → (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) → (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) → z - z' ∈ divCob c W := by
  first | exact @GlobalTheory.Ord2.divCob_of_resCoc_cohom | exact GlobalTheory.Ord2.divCob_of_resCoc_cohom | (intros; apply GlobalTheory.Ord2.divCob_of_resCoc_cohom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteLTorsionSelmerRankTwoAdjoint
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem finite_lTorsion_divSel : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), ContainsAbove S l → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → Finite {x : DivSel c W S A // l • x = 0} := by
  intro hL l _ Ω _ _ _ S A W c hS hW hO hN
  have hH : Finite (H1 (resRep c W hO S hN)) :=
    (hL.gf ℚ Ω l 1 (ResPlane c) S (resRep c W hO S hN) one_pos hS (GlobalTheory.T.continuous_residuePlaneGaloisRep_unramifiedOutside l Ω S W c hO hN hW)).2.1
  have key : ∀ x : {x : DivSel c W S A // l • x = 0}, ∃ (z : G ℚ Ω → Fin 2 → Qbar l) (hz : z ∈ divSelCoc c W S A)
      (y : Fin 2 → Qbar l), VecE c y ∧ (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
      (QuotientAddGroup.mk ⟨z, hz⟩ : DivSel c W S A) = x.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨y, hy, hzy⟩ := hx
    refine ⟨z, hz, y, hy, fun s i => ?_, rfl⟩
    have := hzy s i
    simpa only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] using this
  choose z hz y hy hzy hx using key
  refine Finite.of_injective (fun x => (Submodule.Quotient.mk
    ⟨descS S (resCoc c W (z x) (y x)), GlobalTheory.T.reduced_selmer_cochain_mem_continuous_cocycles_of_cont l Ω S A W c hO hN hW (z x) (hz x) (y x) (hy x) (hzy x)⟩ :
      H1 (resRep c W hO S hN))) ?_
  intro x x' h
  rw [Submodule.Quotient.eq, Submodule.mem_comap, (mem_coboundaries1 _ _)] at h
  obtain ⟨m, hm⟩ := h
  have hd := GlobalTheory.T.divCoboundary_of_reducedCocycles_cohomologous l Ω W c hO (z x) (z x') (y x) (y x') (hy x) (hy x') (hzy x) (hzy x') ⟨m, fun s => by
    have := hm (toGS Ω (S : Set Pl) s)
    simp only [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply] at this
    rw [descS_resCoc_toGS c W S A hO hN (hz x) (y x) (hzy x) s,
      descS_resCoc_toGS c W S A hO hN (hz x') (y x') (hzy x') s] at this
    rw [this, resRep_toGS]⟩
  apply Subtype.ext
  rw [← hx x, ← hx x', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : (↑(-(⟨z x, hz x⟩ : divSelCoc c W S A) + ⟨z x', hz x'⟩) : G ℚ Ω → Fin 2 → Qbar l) = -(z x - z x') := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
  rw [this]
  exact (divCob c W).neg_mem hd

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteLTorsionSelmerRankTwoAdjointStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lTorsion_selmer_rank_two_adjoint : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), ContainsAbove S l → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → Finite {x : DivSel c W S A // l • x = 0} := by
  first | exact @GlobalTheory.Ord2.finite_lTorsion_divSel | exact GlobalTheory.Ord2.finite_lTorsion_divSel | (intros; apply GlobalTheory.Ord2.finite_lTorsion_divSel <;> assumption)
end
