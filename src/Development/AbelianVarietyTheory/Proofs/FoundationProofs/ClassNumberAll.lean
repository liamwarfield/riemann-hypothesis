module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabiliserSelfDualLatticeLevelIndexFormula

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TrivialColumnStabiliser
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def GAf (D : D7) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def GRat (D : D7) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

def colU (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  ColLevel.U (Lv u)

def stabGroup (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  GRat D ⊓ (colU D Lv u).map (MulAut.conj y).toMonoidHom

def ColumnStabilisersTrivial : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
      ∀ y ∈ GAf D, stabGroup D Lv u y = ⊥

theorem mem_stabGroup (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y γ : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    γ ∈ stabGroup D Lv u y ↔ γ ∈ GRat D ∧ y⁻¹ * γ * y ∈ colU D Lv u := by
  unfold stabGroup
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, ?_⟩⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · simp [mul_assoc]

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ColumnStabiliser
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      Subgroup (GL (Fin D.R.k) D.host.E) :=
  letI := D.host.cmStar
  fun y =>
    UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ⊓
      ((Lv u).U.comap (MulAut.conj (y : GL (Fin D.R.k)
          (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))⁻¹).toMonoidHom).comap
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))

theorem mem_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ (y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      (γ : GL (Fin D.R.k) D.host.E),
      γ ∈ colStab D Lv u y ↔
        γ ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 ∧
          (y : GL (Fin D.R.k) _)⁻¹ *
            bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ *
            (y : GL (Fin D.R.k) _) ∈ (Lv u).U := by
  intro y γ
  simp [colStab, Subgroup.mem_inf, Subgroup.mem_comap]

def ColStabTrivialAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      colStab D Lv u y = ⊥

def ColStabTrivial : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), ColStabTrivialAt D Lv u

theorem map_colStab (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    letI := D.host.cmStar
    ∀ y : UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (colStab D Lv u y).map (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) =
        ratPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
          (Lv u).U.map (MulAut.conj (y : GL (Fin D.R.k) _)).toMonoidHom := by
  intro y
  ext x
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨h1, h2⟩ := (mem_colStab D Lv u y γ).1 hγ
    exact ⟨⟨γ, h1, rfl⟩, ⟨_, h2, by simp [mul_assoc]⟩⟩
  · rintro ⟨⟨γ, h1, rfl⟩, z, hz, hz'⟩
    refine ⟨γ, (mem_colStab D Lv u y γ).2 ⟨h1, ?_⟩, rfl⟩
    rw [← hz']
    simpa [mul_assoc] using hz

end GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLattice
namespace GlobalTheory.OverObj

theorem selfDualOverBase : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase :=
  GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice

end GlobalTheory.OverObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLatticeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_over_columnBaseLattice : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase := by
  first | exact @GlobalTheory.OverObj.selfDualOverBase | exact GlobalTheory.OverObj.selfDualOverBase | (intros; apply GlobalTheory.OverObj.selfDualOverBase <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfMembership
noncomputable section

namespace GlobalTheory.Proof.EqOneOfMembership

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser
open scoped TensorProduct

section Local

variable {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}

theorem eq_one_of_red_eq_one {M : Matrix (Fin n) (Fin n) O}
    (hM : M.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) = 1) {m : ℕ}
    (hm : IsUnit (m : O)) (hpow : M ^ m = 1) : M = 1 := by
  set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) with hπ
  have hM' : π.mapMatrix M = 1 := hM
  have h1 : (∑ i ∈ Finset.range m, M ^ i) * (M - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have h2 : π.mapMatrix (∑ i ∈ Finset.range m, M ^ i) = (m : Matrix (Fin n) (Fin n) _) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_pow, hM', one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have h3 : IsUnit (π (∑ i ∈ Finset.range m, M ^ i).det) := by
    rw [RingHom.map_det, h2, ← Matrix.isUnit_iff_isUnit_det]
    have := (hm.map π).map (algebraMap _ (Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O)))
    simpa using this
  have h4 : IsUnit (∑ i ∈ Finset.range m, M ^ i).det := by
    by_contra h
    have : π (∑ i ∈ Finset.range m, M ^ i).det = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [this] at h3
    exact not_isUnit_zero h3
  have h5 := (Matrix.isUnit_iff_isUnit_det _).2 h4
  exact sub_eq_zero.1 (h5.mul_right_eq_zero.1 h1)

theorem pow_prime_pow_eq_one {A : Type} [Ring A] {g r : ℕ} (hg : g.Prime) (h0 : (g : A) = 0)
    {a : A} (ha : (a - 1) ^ r = 0) : a ^ g ^ r = 1 := by
  have e2 := (Commute.one_right (a - 1)).add_pow_prime_pow_eq hg r
  have hle : r ≤ g ^ r := (Nat.lt_pow_self hg.one_lt).le
  rw [sub_add_cancel, h0, pow_eq_zero_of_le hle ha] at e2
  simpa using e2

theorem exists_pow_eq_one {g : ℕ} (hg : g.Prime) (hgm : (g : O) ∈ IsLocalRing.maximalIdeal O)
    {M : Matrix (Fin n) (Fin n) O}
    (hM : IsNilpotent (M.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) - 1))
    (hfin : IsOfFinOrder M) : ∃ a : ℕ, M ^ g ^ a = 1 := by
  obtain ⟨r, hr⟩ := hM
  set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) with hπ
  have h0 : (g : Matrix (Fin n) (Fin n) (O ⧸ IsLocalRing.maximalIdeal O)) = 0 := by
    have : (g : O ⧸ IsLocalRing.maximalIdeal O) = 0 := by
      rw [← map_natCast π]; exact Ideal.Quotient.eq_zero_iff_mem.2 hgm
    rw [← map_natCast (algebraMap (O ⧸ IsLocalRing.maximalIdeal O) _), this, map_zero]
  have h1 : (π.mapMatrix M) ^ g ^ r = 1 := pow_prime_pow_eq_one hg h0 hr
  obtain ⟨e, m, hm, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := orderOf M) hfin.orderOf_pos.ne' g hg.ne_one
  refine ⟨r + e, eq_one_of_red_eq_one (m := m) ?_ ?_ ?_⟩
  · change π.mapMatrix _ = 1
    rw [map_pow, pow_add, pow_mul, h1, one_pow]
  · have hc : IsCoprime (m : O) (g : O) := by
      have := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hg).mpr hm).symm
      simpa using this.map (Int.castRingHom O)
    by_contra h
    obtain ⟨u, v, huv⟩ := hc
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [← huv]
      exact add_mem (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 h))
        (Ideal.mul_mem_left _ _ hgm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  · rw [← pow_mul, pow_add, mul_assoc, ← hord, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

end Local

theorem isNilpotent_of_mem_closure {A : Type} [CommRing A] {k : ℕ} {x : GL (Fin k) A}
    (hx : x ∈ Subgroup.closure (upperUni k A)) :
    IsNilpotent ((x : Matrix (Fin k) (Fin k) A) - 1) := by
  have key : ∀ y : GL (Fin k) A, y ∈ upperUni k A ↔
      (y : Matrix (Fin k) (Fin k) A).BlockTriangular id ∧
        ∀ i, (y : Matrix (Fin k) (Fin k) A) i i = 1 := fun y =>
    ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2⟩,
      fun h i j => ⟨fun hij => h.1 hij, h.2 i⟩⟩
  have diag : ∀ a b : Matrix (Fin k) (Fin k) A, a.BlockTriangular id → b.BlockTriangular id →
      ∀ i, (a * b) i i = a i i * b i i := by
    intro a b ha hb i
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
    rcases lt_or_gt_of_ne hj with h | h
    · rw [ha (show id j < id i from h), zero_mul]
    · rw [hb (show id i < id j from h), mul_zero]
  have hx' : x ∈ upperUni k A := by
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact (key _).2 ⟨Matrix.blockTriangular_one, fun i => by simp⟩
    | mul a b _ _ ha hb =>
      rw [key] at ha hb ⊢
      exact ⟨ha.1.mul hb.1, fun i => by rw [Units.val_mul, diag _ _ ha.1 hb.1, ha.2, hb.2, one_mul]⟩
    | inv a _ ha =>
      rw [key] at ha ⊢
      let _ := a.invertible
      have h1 : ((a⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A).BlockTriangular id := by
        rw [Matrix.coe_units_inv]
        exact Matrix.blockTriangular_inv_of_blockTriangular ha.1
      refine ⟨h1, fun i => ?_⟩
      have := diag _ _ h1 ha.1 i
      rw [Units.inv_mul, ha.2, mul_one, Matrix.one_apply_eq] at this
      exact this.symm
  rw [key] at hx'
  set h := (x : Matrix (Fin k) (Fin k) A)
  have h1 : h.charpoly = ∏ i : Fin k, (Polynomial.X - Polynomial.C (h i i)) :=
    Matrix.charpoly_of_isUpperTriangular h hx'.1
  have h2 := Matrix.aeval_self_charpoly h
  rw [h1] at h2
  exact ⟨k, by simpa [hx'.2, Finset.prod_const] using h2⟩

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] {k : ℕ} {φ : A →+* B}
    (hφ : Function.Injective φ) : Function.Injective (bc (n := Fin k) φ) := by
  intro a b h
  refine Units.ext (Matrix.ext fun i j => hφ ?_)
  exact congrArg (fun g : GL (Fin k) B => g.val i j) h

theorem bc_bc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {k : ℕ} (φ : A →+* B)
    (ψ : B →+* C) (x : GL (Fin k) A) : bc ψ (bc φ x) = bc (ψ.comp φ) x :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem iwU_pow_eq_one {F : Type} [Field F] [NumberField F] {k g : ℕ} (hg : g.Prime)
    {v : HeightOneSpectrum (𝓞 F)} (hv : (g : 𝓞 F) ∈ v.asIdeal)
    {x : GL (Fin k) (v.adicCompletion F)} (hx : x ∈ iwU F k v) (hfin : IsOfFinOrder x) :
    ∃ a : ℕ, x ^ g ^ a = 1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hinj : Function.Injective
      (bc (n := Fin k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))) :=
    bc_injective Subtype.val_injective
  have hz' : IsOfFinOrder z := (hinj.isOfFinOrder_iff).1 hfin
  have hgm : (g : v.adicCompletionIntegers F) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have e : (((g : v.adicCompletionIntegers F)) : v.adicCompletion F) =
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (g : 𝓞 F)) := by
      rw [map_natCast, map_natCast]; rfl
    rw [e, HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ((v.valuation_lt_one_iff_mem _).2 hv).ne
  obtain ⟨a, ha⟩ := exists_pow_eq_one hg hgm (M := z.val) (isNilpotent_of_mem_closure hz)
    (Units.isOfFinOrder_val.2 hz')
  refine ⟨a, ?_⟩
  rw [← map_pow, show z ^ g ^ a = 1 from Units.ext (by simpa using ha), map_one]

theorem eq_one_of_pow_prime_pow {E : Type} [Field E] [NumberField E] {k g : ℕ} (hg : g.Prime)
    (hbig : Module.finrank ℚ E * k < g - 1) (a : ℕ) :
    ∀ x : GL (Fin k) E, x ^ g ^ a = 1 → x = 1 := by
  induction a with
  | zero => intro x hx; simpa using hx
  | succ a ih =>
    intro x hx
    apply ih
    by_contra hne
    have := Formalism.LogVandermondeBounds.StandardLattice.primeOrderFinrank E k g (x ^ g ^ a).val hg
      (by rw [← Units.val_pow_eq_pow_val, ← pow_mul, ← pow_succ, hx, Units.val_one])
      (fun h => hne (Units.ext h))
    omega

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem isOfFinOrder_of_mem (L : ColLevel R F E sp gp C A clsLat)
    {y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hy : y ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    {γ : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hγ1 : γ ∈ ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    (hγ2 : y⁻¹ * γ * y ∈ L.U) : IsOfFinOrder γ := by
  obtain ⟨c, hc⟩ := L.y_bij.2 (Quotient.mk'' ⟨y, hy⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hc
  have hab' : y = a.1 * (L.y c).1 * b.1 := congrArg Subtype.val hab
  have ha' : a.1 ∈ ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) := ha
  have hb' : b.1 ∈ L.U := hb
  have h2 : a.1⁻¹ * γ * a.1 ∈ L.U.map (MulAut.conj (L.y c).1).toMonoidHom := by
    refine ⟨_, mul_mem (mul_mem hb' hγ2) (inv_mem hb'), ?_⟩
    rw [hab', MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨δ, hδ, hδe⟩ := mul_mem (mul_mem (inv_mem ha') hγ1) ha'
  rw [← hδe] at h2
  obtain ⟨s, hs⟩ := (L.stabI_range c δ hδ).2 h2
  have h4 : IsOfFinOrder δ := by
    have := (Subgroup.subtype _).isOfFinOrder ((L.stabI c).isOfFinOrder
      (isOfFinOrder_of_finite s))
    rw [hs] at this
    exact this
  have h5 := (MulAut.conj a.1).toMonoidHom.isOfFinOrder
    ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).isOfFinOrder h4)
  rw [hδe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h5
  convert h5 using 1
  group

theorem eq_one_of_mem (L : ColLevel R F E sp gp C A clsLat) (i : Fin 2) (hg : (gp i).Prime)
    (hi : Module.finrank ℚ E * R.k < gp i - 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : (gp i : 𝓞 F) ∈ v.asIdeal)
    {y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hy : y ∈ UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    {γ : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (hγ1 : γ ∈ ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))
    (hU : y⁻¹ * γ * y ∈ L.U) : γ = 1 := by
  have hfin := isOfFinOrder_of_mem L hy hγ1 hU
  obtain ⟨δ, hδ, rfl⟩ := hγ1
  have hloc := ((L.U_eq _).1 hU).2 v
  have hiw := (L.Uloc_g i v hv _ (L.Uloc_le v hloc)).1 hloc
  rw [bc_bc] at hiw
  generalize ((RingHom.fst _ _).comp (L.splitG i v hv).toRingHom).comp
    (prV (E := E) v) = ψ at hiw
  generalize L.frG i v hv = w at hiw
  rw [map_mul, map_mul, map_inv, bc_bc] at hiw
  have hfin1 := (bc ψ).isOfFinOrder hfin
  rw [bc_bc] at hfin1
  generalize ψ.comp (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = j at hiw hfin1
  generalize bc ψ y = t at hiw
  let Φ : GL (Fin R.k) E →* GL (Fin R.k) (v.adicCompletion F) :=
    (MulAut.conj (t * w)⁻¹).toMonoidHom.comp (bc j)
  have hΦinj : Function.Injective Φ :=
    (MulAut.conj (t * w)⁻¹).injective.comp (bc_injective j.injective)
  have hmem : Φ δ ∈ iwU F R.k v := by
    convert hiw using 1
    change (t * w)⁻¹ * bc j δ * (t * w)⁻¹⁻¹ = _
    group
  have hfin' : IsOfFinOrder (Φ δ) := (MulAut.conj (t * w)⁻¹).toMonoidHom.isOfFinOrder hfin1
  obtain ⟨a, ha⟩ := iwU_pow_eq_one hg hv hmem hfin'
  have h1 : δ ^ gp i ^ a = 1 := hΦinj (by rw [map_pow, ha, map_one])
  rw [eq_one_of_pow_prime_pow hg hi a δ h1, map_one]

end Level

theorem columnStabilisersTrivial : ColumnStabilisersTrivial := by
  intro D Lv u hbig hs y hy
  let _ := D.host.cmStar
  obtain ⟨i, hi⟩ := hbig
  have hf : D.R.f ≠ 0 := by
    unfold Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  obtain ⟨v, hv⟩ := (Nat.card_ne_zero.1 ((hs i).1.trans_ne hf)).1
  rw [eq_bot_iff]
  intro γ hγ
  rw [mem_stabGroup] at hγ
  exact Subgroup.mem_bot.2 (eq_one_of_mem (Lv u) i (D.host.g_prime i)
    (by rw [finrank_host D]; exact hi) hv hy hγ.1 hγ.2)

end GlobalTheory.Proof.EqOneOfMembership

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabilizerGroupMap
noncomputable section

namespace GlobalTheory.Proof.StabilizerGroupMap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

theorem bc_inclE_injective (D : D7) :
    Function.Injective
      (bc (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
        GL (Fin D.R.k) D.host.E →*
          GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    exact (evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) := inferInstance
  intro a b hab
  refine Units.ext (Matrix.ext fun i j => ?_)
  apply (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).injective
  have h2 := congrArg (fun g : GL (Fin D.R.k) _ => g.val i j) hab
  simpa [bc] using h2

theorem stabGroup_eq_map (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y =
      (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y).map
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.map_colStab D Lv u y).symm

theorem stabGroup_eq_bot_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥ ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y = ⊥ := by
  rw [stabGroup_eq_map, Subgroup.map_eq_bot_iff_of_injective _ (bc_inclE_injective D)]

theorem at_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    (GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D, GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥) ↔
      GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivialAt D Lv u := by
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact ⟨fun h y => (stabGroup_eq_bot_iff D Lv u y).1 (h y.1 y.2),
    fun h y hy => (stabGroup_eq_bot_iff D Lv u ⟨y, hy⟩).2 (h ⟨y, hy⟩)⟩

theorem columnStabilisersTrivial_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.ColumnStabilisersTrivial ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivial :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => at_iff D Lv u

end GlobalTheory.Proof.StabilizerGroupMap

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DoubleCosetCount
section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabiliserCardinality
namespace GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

def stab {G : Type} [Group G] (Γ K : Subgroup G) (y : G) : Subgroup G :=
  Γ ⊓ K.map (MulAut.conj y).toMonoidHom

theorem mem_stab {G : Type} [Group G] (Γ K : Subgroup G) (y γ : G) :
    γ ∈ stab Γ K y ↔ γ ∈ Γ ∧ y⁻¹ * γ * y ∈ K := by
  unfold stab
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  rintro ⟨k, hk, rfl⟩
  simpa [mul_assoc] using hk

def DoubleCosetCount : Prop :=
  ∀ (G : Type) [Group G] (Γ U K : Subgroup G), U ≤ K →
    (U.subgroupOf K).FiniteIndex →
    ∀ [Fintype (DoubleCoset.Quotient (Γ : Set G) (K : Set G))],
    (∀ y : G, Finite (stab Γ K y)) →
    (∀ x : G, stab Γ U x = ⊥) →
    ∀ rep : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → G,
      (∀ c, DoubleCoset.mk Γ K (rep c) = c) →
      Finite (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) ∧
      (Nat.card (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) : ℚ) =
        (U.relIndex K : ℚ) *
          ∑ c : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
            1 / (Nat.card (stab Γ K (rep c)) : ℚ)

end GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality
end

namespace GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation

open GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

theorem card_fiber_mul_card_stab {G : Type} [Group G] (Γ U K : Subgroup G) (hUK : U ≤ K)
    (hfree : ∀ x : G, stab Γ U x = ⊥) (y : G) :
    Nat.card {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y} * Nat.card (stab Γ K y) =
      U.relIndex K := by
  have hex : ∀ d : {d : DoubleCoset.Quotient (Γ : Set G) (U : Set G) //
        DoubleCoset.mk Γ K d.out = DoubleCoset.mk Γ K y},
      ∃ k : K, DoubleCoset.mk Γ U (y * k) = d.1 := by
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, k, hk, h⟩ := (@DoubleCoset.eq _ _ Γ K _ _).1 hd.symm
    refine ⟨⟨k, hk⟩, ?_⟩
    refine Eq.trans ?_ (DoubleCoset.out_eq' (H := Γ) (K := U) d)
    exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨a, ha, 1, U.one_mem, by rw [h]; group⟩
  choose κ hκ using hex
  rw [← Nat.card_prod, Subgroup.relIndex, Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p => ((⟨y⁻¹ * p.2.1 * y, ((mem_stab Γ K y _).1 p.2.2).2⟩ * κ p.1 : K) :
      K ⧸ U.subgroupOf K)) ⟨?_, ?_⟩)
  · rintro ⟨d, s, hs⟩ ⟨e, t, ht⟩ h
    have hs' := ((mem_stab Γ K y _).1 hs).1
    have ht' := ((mem_stab Γ K y _).1 ht).1
    have h1 := QuotientGroup.eq.1 h
    rw [Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have hde : d = e := by
      apply Subtype.ext
      rw [← hκ d, ← hκ e]
      exact (@DoubleCoset.eq _ _ Γ U _ _).2 ⟨t⁻¹ * s, Γ.mul_mem (Γ.inv_mem ht') hs', _, h1, by group⟩
    subst hde
    have h2 : s⁻¹ * t ∈ stab Γ U (y * κ d) := by
      refine (mem_stab Γ U _ _).2 ⟨Γ.mul_mem (Γ.inv_mem hs') ht', ?_⟩
      convert h1 using 1
      group
    rw [hfree, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      have hd : DoubleCoset.mk Γ K (DoubleCoset.mk Γ U (y * k)).out = DoubleCoset.mk Γ K y := by
        obtain ⟨a, ha, u, hu, h⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1
          (DoubleCoset.out_eq' (H := Γ) (K := U) (DoubleCoset.mk Γ U (y * k))).symm
        symm
        exact (@DoubleCoset.eq _ _ Γ K _ _).2
          ⟨a, ha, k * u, K.mul_mem k.2 (hUK hu), h.trans (by group)⟩
      obtain ⟨a, ha, u, hu, h⟩ := (@DoubleCoset.eq _ _ Γ U _ _).1 (hκ ⟨_, hd⟩)
      have hk : y⁻¹ * a * y = k * u⁻¹ * (κ ⟨_, hd⟩ : G)⁻¹ := by
        generalize (κ ⟨_, hd⟩ : G) = m at h ⊢
        rw [show (k : G) = y⁻¹ * (y * k) by group, h]
        group
      have hs : a ∈ stab Γ K y := by
        refine (mem_stab Γ K y _).2 ⟨ha, ?_⟩
        rw [hk]
        exact K.mul_mem (K.mul_mem k.2 (K.inv_mem (hUK hu))) (K.inv_mem (κ _).2)
      refine ⟨⟨⟨_, hd⟩, ⟨a, hs⟩⟩, QuotientGroup.eq.2 ?_⟩
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hk]
      convert hu using 1
      group

theorem doubleCosetCount : DoubleCosetCount := by
  intro G _ Γ U K hUK hfi _ hfin hfree rep hrep
  have hne : U.relIndex K ≠ 0 := hfi.index_ne_zero
  let π : DoubleCoset.Quotient (Γ : Set G) (U : Set G) →
      DoubleCoset.Quotient (Γ : Set G) (K : Set G) := fun d => DoubleCoset.mk Γ K d.out
  have key : ∀ c, Nat.card {d // π d = c} * Nat.card (stab Γ K (rep c)) = U.relIndex K := by
    intro c
    have := card_fiber_mul_card_stab Γ U K hUK hfree (rep c)
    rw [hrep c] at this
    exact this
  have : ∀ c, Finite {d // π d = c} := fun c =>
    Nat.finite_of_card_ne_zero fun h => hne (by rw [← key c, h, zero_mul])
  refine ⟨Finite.of_equiv _ (Equiv.sigmaFiberEquiv π), ?_⟩
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv π), Nat.card_sigma, Finset.mul_sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hs : (Nat.card (stab Γ K (rep c)) : ℚ) ≠ 0 := by
    have := hfin (rep c)
    exact_mod_cast Nat.card_pos.ne'
  rw [← key c]
  push_cast
  field_simp

end GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassSelfDualLatticeFirstSpaceEq
noncomputable section

namespace GlobalTheory.ColClassNumber

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open GlobalTheory.IndefiniteRowSideFullHecke

theorem card_eq_index_mul_mass {G : Type} [Group G] (Γ U K : Subgroup G) (m : ℝ) (hUK : U ≤ K)
    (hidx : U.relIndex K ≠ 0) (hm : ClassesDoubleCosets.CosetMass Γ K m)
    (hfree : ∀ x γ : G, γ ∈ Γ → x⁻¹ * γ * x ∈ U → γ = 1) :
    (Nat.card (ClassSet Γ U) : ℝ) = (U.relIndex K : ℝ) * m := by
  obtain ⟨hfin, hst, hsum⟩ := hm
  letI : Fintype (ClassSet Γ K) := Fintype.ofFinite _
  have e : ∀ y : G, StabiliserCardinality.stab Γ K y ≃ stabAt Γ K y := fun y =>
    { toFun := fun γ => ⟨⟨γ.1, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).1⟩, ((StabiliserCardinality.mem_stab Γ K y _).1 γ.2).2⟩
      invFun := fun γ => ⟨γ.1.1, (StabiliserCardinality.mem_stab Γ K y _).2 ⟨γ.1.2, γ.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : ∀ c : ClassSet Γ K, DoubleCoset.mk Γ K (Quotient.out c) = c := fun c => Quotient.out_eq' c
  have h := (GlobalTheory.Proof.DoubleCosetCountGlobalInterpolation.doubleCosetCount G Γ U K hUK ⟨hidx⟩
    (fun y => have := hst y; Finite.of_equiv _ (e y).symm)
    (fun x => (Subgroup.eq_bot_iff_forall _).2 fun γ hγ =>
      hfree x γ ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).1 ((StabiliserCardinality.mem_stab Γ U x γ).1 hγ).2)
    _ hs).2
  have h' := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at h'
  rw [h', ← hsum _ hs]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [one_div, Nat.card_congr (e _)]

section Lattice

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (sp : Spaces R F E)

theorem exists_lattice (N : Submodule (𝓞 E) (Fin R.k → E)) (hfin : Module.Finite (𝓞 E) N)
    (hspan : Submodule.span E (N : Set (Fin R.k → E)) = ⊤)
    (hdual : dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E))) :
    ∃ M : Submodule (𝓞 E) (sp.X 0).V, Submodule.IsLattice E M ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (sp.X 0).hT M ∧ sp.crdLat0 M = N := by
  let e : (sp.X 0).V ≃ₗ[𝓞 E] (Fin R.k → E) := sp.crd0.restrictScalars (𝓞 E)
  have hmem : ∀ x, x ∈ N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V) ↔ sp.crd0 x ∈ N := fun x => by
    rw [Submodule.mem_map_equiv]; rfl
  refine ⟨N.map (e.symm : (Fin R.k → E) →ₗ[𝓞 E] (sp.X 0).V), ?_, ?_, ?_⟩
  · exact Submodule.IsLattice.of_fg E ((Module.Finite.iff_fg.1 hfin).map _)
  · ext x
    rw [hmem, ← SetLike.mem_coe (p := N), ← hdual]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one, hmem, sp.hermitianForm_base_coordinates, dualSet, Set.mem_setOf_eq,
      RingHom.mem_range]
    constructor
    · intro h y hy
      have := h (sp.crd0.symm y) (by simpa using hy)
      simpa using this
    · intro h y hy
      exact h _ hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).1 hx
    · intro hy
      exact ⟨sp.crd0.symm y, (hmem _).2 (by simpa using hy), by simp⟩

end Lattice

theorem idx_pos (D : D7) : 0 < idxPi D (D.host.g 0) (D.host.g 1) := by
  have h : ∀ g k : ℕ, g.Prime → 0 < idxColLoc g k := by
    intro g k hg
    haveI : NeZero g := ⟨hg.ne_zero⟩
    haveI : Nonempty {A : GL (Fin k) (ZMod g) // IsUnitri (A : Matrix (Fin k) (Fin k) (ZMod g))} :=
      ⟨⟨1, fun i j h => by simp [h.ne'], fun i => by simp⟩⟩
    exact div_pos (Nat.cast_pos.2 Nat.card_pos) (Nat.cast_pos.2 Nat.card_pos)
  exact mul_pos (pow_pos (h _ _ (D.host.g_prime 0)) _) (pow_pos (h _ _ (D.host.g_prime 1)) _)

theorem mass_selfDualLattice_firstSpace_eq (D : D7) : letI := D.host.cmStar
    ∀ M : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Submodule.IsLattice D.host.E M →
      Formalism.HermitianLatticesTheory.IsUnimodular (D.sp.X 0).hT M → Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT M = massI D D.R.k := by
  letI := D.host.cmStar
  intro M hM hu
  rw [← D.sp.rank0]
  exact GlobalTheory.genusMassStd D { D.sp.X 0 with L0 := M, standardTuple_isLattice := hM, baseLattice_isUnimodular := hu } (D.sp.X_sig 0)
    (baseSpace_posDef _ _ D.sp)

theorem classNumber (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (hcos : ClassesDoubleCosets.ClassesAsDoubleCosets) (hstab : ColumnStabiliser.ColStabTrivial)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv := by
  letI := D.host.cmStar
  intro hg hs u hT
  obtain ⟨-, N, ⟨hfin, hspan, hdual, -⟩, -, -, hUK⟩ := hover D Lv u hT
  obtain ⟨M, hM, hu, rfl⟩ := exists_lattice D.sp N hfin hspan hdual
  have hidx := hindex D Lv u hs hT _ ⟨hfin, hspan, hdual.symm⟩ hUK
  have hm := hcos.2 D Lv u M hM hu
  rw [mass_selfDualLattice_firstSpace_eq D M hM hu] at hm
  have hrel := Subgroup.relIndex_subgroupOf (H := SelfDualLatticeIndex.levelU D Lv u)
    (SelfDualLatticeIndex.stabHat_le D (D.sp.crdLat0 M))
  have hne : (SelfDualLatticeIndex.levelU D Lv u).relIndex (SelfDualLatticeIndex.stabHat D (D.sp.crdLat0 M)) ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hidx
    exact (mul_pos (idx_pos D) (SelfDualLatticeIndex.factorT_pos D u)).ne hidx
  have h := card_eq_index_mul_mass _ ((Lv u).U.subgroupOf _) _ _ (Subgroup.comap_mono hUK)
    (hrel.trans_ne hne) hm (by
      intro x γ hγ hx
      have h1 := ColumnStabiliser.map_colStab D Lv u x
      rw [hstab D Lv u hg hs x, Subgroup.map_bot] at h1
      have h2 : γ.1 ∈ (⊥ : Subgroup _) := by
        rw [h1]
        exact ⟨hγ, ⟨_, hx, by simp [mul_assoc]⟩⟩
      exact Subtype.ext (Subgroup.mem_bot.1 h2))
  rw [Nat.card_eq_of_bijective _ (Lv u).y_bij]
  refine h.trans ?_
  rw [mul_assoc (massI D D.R.k), mul_comm (massI D D.R.k)]
  exact congrArg (· * massI D D.R.k) ((congrArg (fun n : ℕ => (n : ℝ)) hrel).trans hidx)

theorem classNumber_of_index (hover : SplittingProjection.SelfDualOverBase) (hindex : SelfDualLatticeIndex.StabiliserLevelIndexFormula)
    (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv :=
  classNumber hover hindex (GlobalTheory.Proof.CosetGroupEquiv.massAsCosetSum_iff.1 GlobalTheory.Proof.TotallyDefiniteMass.massAsCosetSum)
    (GlobalTheory.Proof.StabilizerGroupMap.columnStabilisersTrivial_iff.1 GlobalTheory.Proof.EqOneOfMembership.columnStabilisersTrivial) D Lv

end GlobalTheory.ColClassNumber

end
end

namespace GlobalTheory.ColClassNumber

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice

theorem classNumber_all (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv :=
  classNumber_of_index GlobalTheory.T.selfDualLattice_over_columnBaseLattice GlobalTheory.T.stabiliser_self_dual_lattice_level_index_formula D Lv

end GlobalTheory.ColClassNumber
