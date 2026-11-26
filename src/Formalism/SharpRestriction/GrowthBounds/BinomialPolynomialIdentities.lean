module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.LatticeGeneratedLowestWeight
public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.SplittingThirdPartHolds
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhDetZpowMem
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.RationalBitableauLatticeStatement
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Branch
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.WeylGT

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.AdmissibleLowerSetSpan
namespace Formalism.MainNotions.G.ColumnFamilies

theorem admissible_lowerSet_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.SaturatedLowerSetSpan D := saturatedLowerSetSpan_of_lowerSetTypesSpan D (lower_set_types_span D)

end Formalism.MainNotions.G.ColumnFamilies
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ToralGalois
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem weight_projector_mem_weight_space {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (htop : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (mu : Fin n → ℤ) (e : Module.End K V) (he : IsWtProj E mu e)
    (x : V) : e x ∈ weightSp E mu := by
  have hx : x ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by rw [htop]; trivial
  refine Submodule.iSup_induction (fun nu => weightSp E nu) (motive := fun y => e y ∈ weightSp E mu) hx ?_ ?_ ?_
  · intro nu y hy
    by_cases h : nu = mu
    · subst h
      rw [he.1 y hy]
      exact hy
    · rw [he.2 nu h y hy]
      exact zero_mem _
  · rw [map_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [map_add (f := _)]
    exact add_mem ha hb

theorem adm_eleven (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := by
  intro p _ O _ _ _ _ _S n V _ _ _ _ E mu La hrep _hdom _hiso hlat hproj

  have hstab : ∀ u ∈ UZmon E, ∀ x ∈ La, u x ∈ La := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu => exact hlat.1 u hu
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, y, hy, -, rfl⟩
    exact hstab u hu y hy
  · intro y hy u hu e he
    exact ⟨hproj _ (hstab u hu y hy) mu e he, weight_projector_mem_weight_space E hrep.2.2 mu e he _⟩

end Formalism.MainNotions.G.ColumnFamilies
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore
section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.InducedSectionsSpanStatement
section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhCountAll
section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhMemDualWeyl
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_generic {B : Type} [CommRing B] [IsDomain B] [Algebra R B] (bm gm : Matrix (Fin n) (Fin n) B)
    (hb : ∀ a c, a < c → bm a c = 0) (hbd : ∀ a, bm a a ≠ 0) (hg : gm.det ≠ 0)
    (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    aeval (fun v : Fin n × Fin n => (bm * gm) v.2 v.1) Q =
      (∏ a, bm a a ^ ν a) * aeval (fun v : Fin n × Fin n => gm v.2 v.1) Q := by
  let F := FractionRing B
  let φ : B →+* F := algebraMap B F
  have hinj : Function.Injective φ := IsFractionRing.injective B F
  have hbdet : (φ.mapMatrix bm).det ≠ 0 := by
    rw [← RingHom.map_det, Matrix.det_of_isLowerTriangular _ (fun i j hij => hb i j hij),
      map_ne_zero_iff _ hinj]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hbd a
  have hgdet : (φ.mapMatrix gm).det ≠ 0 := by
    rw [← RingHom.map_det, map_ne_zero_iff _ hinj]; exact hg
  let b' : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hbdet
  let g' : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hgdet
  have hb' : b'.val = φ.mapMatrix bm := rfl
  have hg' : g'.val = φ.mapMatrix gm := rfl
  have h := hQ F b' g' (by intro a c hac; rw [hb']; show φ (bm a c) = 0; rw [hb a c hac, map_zero])
  have hev : ∀ (M : Matrix (Fin n) (Fin n) B) (h' : GL (Fin n) F), h'.val = φ.mapMatrix M →
      evGLR h' (algebraMap _ (GLCoord R n) (rename Prod.swap Q)) =
        φ (aeval (fun v : Fin n × Fin n => M v.2 v.1) Q) := by
    intro M h' hh
    rw [qh_evGLR_alg, coe_eval₂Hom, eval₂_rename, aeval_def, eval₂_comp_left, hh]
    rw [IsScalarTower.algebraMap_eq R B F]
    rfl
  rw [hev (bm * gm) (b' * g') (by rw [Units.val_mul, hb', hg', map_mul]), hev gm g' hg'] at h
  apply hinj
  rw [map_mul, map_prod]
  simp only [map_pow]
  simpa [hb'] using h

lemma qh_det_ne [IsDomain R] {B : Type} [CommRing B] (φ : MvPolynomial (Fin n × Fin n) R →+* B)
    (hφ : Function.Injective φ) : (Matrix.of fun a c : Fin n => φ (X (c, a))).det ≠ 0 := by
  have h : (Matrix.of fun a c : Fin n => φ (X (c, a))) =
      (φ.mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) R)).transpose := by
    ext a c; simp [Matrix.mvPolynomialX]
  rw [h, Matrix.det_transpose, ← RingHom.map_det, map_ne_zero_iff _ hφ]
  exact Matrix.det_mvPolynomialX_ne_zero _ _

def qhPhi (R : Type) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  aeval fun v : Fin n × Fin n => X v.2 * C (X v)

lemma qh_phi_mono1 (d : Fin n × Fin n →₀ ℕ) :
    qhPhi R n (monomial d 1) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d 1) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d1 d2 h1 h2 =>
    have e : (monomial (d1 + d2) (1 : R)) = monomial d1 1 * monomial d2 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, h1, h2, monomial_mul, Finsupp.mapDomain_add]
  | single v e =>
    rw [← X_pow_eq_monomial, map_pow, qhPhi, aeval_X, mul_pow, Finsupp.mapDomain_single, ← map_pow,
      X_pow_eq_monomial, mul_comm, C_mul_monomial, mul_one]

lemma qh_phi_mono (d : Fin n × Fin n →₀ ℕ) (r : R) :
    qhPhi R n (monomial d r) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d r) := by
  have e : monomial d r = r • monomial d (1 : R) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, qh_phi_mono1, smul_monomial]

lemma qh_phi_coeff (Q : MvPolynomial (Fin n × Fin n) R) (d0 : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (AddMonoidAlgebra.coeff (qhPhi R n Q) (Finsupp.mapDomain Prod.snd d0)) d0 = AddMonoidAlgebra.coeff Q d0 := by
  induction Q using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [qh_phi_mono]
    by_cases h : d = d0
    · subst h; simp
    · rw [coeff_monomial, coeff_monomial, if_neg h]
      split_ifs
      · rw [coeff_monomial, if_neg h]
      · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]

lemma qh_weight (d : Fin n × Fin n →₀ ℕ) :
    Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) d = ⇑(Finsupp.mapDomain Prod.snd d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d1 d2 h1 h2 => rw [map_add (f := _), h1, h2, Finsupp.mapDomain_add, Finsupp.coe_add]
  | single v e =>
    rw [Finsupp.weight_single, Finsupp.mapDomain_single]
    funext a
    simp [Formalism.GradedWeylDivisibility.colW, Finsupp.single_apply, Pi.single_apply, eq_comm]

lemma qh_homog [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) Q ν := by
  have h := qh_generic (B := MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))
    (Matrix.diagonal fun a => X a) (Matrix.of fun a c : Fin n => C (X (c, a)))
    (fun a c hac => Matrix.diagonal_apply_ne _ hac.ne) (fun a => by simp)
    (qh_det_ne (C : _ →+* MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R)) (C_injective _ _)) Q ν hQ
  have e1 : aeval (fun v : Fin n × Fin n => ((Matrix.diagonal fun a => X a) *
      (Matrix.of fun a c : Fin n => (C (X (c, a)) : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) :
        Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) v.2 v.1) Q
      = qhPhi R n Q := by
    rw [qhPhi]; congr 2; funext v; simp [Matrix.diagonal_mul]
  have e2 : aeval (fun v : Fin n × Fin n =>
      (Matrix.of fun a c : Fin n => (C (X (c, a)) : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) v.2 v.1) Q
      = C Q := by
    have := MvPolynomial.comp_aeval_apply (R := R) (fun v : Fin n × Fin n => (X v : MvPolynomial (Fin n × Fin n) R))
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) Q
    rw [aeval_X_left_apply] at this
    exact this.symm
  have e3 : (∏ a, (Matrix.diagonal fun a => (X a : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) a a ^ ν a) =
      monomial (Finsupp.equivFunOnFinite.symm ν) 1 := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp
  rw [e1, e2, e3, mul_comm, C_mul_monomial, mul_one] at h
  intro d hd
  rw [qh_weight]
  by_contra hne
  apply hd
  have hne' : Finsupp.equivFunOnFinite.symm ν ≠ Finsupp.mapDomain Prod.snd d := by
    intro heq
    apply hne
    rw [← heq]; rfl
  rw [← qh_phi_coeff, h, coeff_monomial, if_neg hne']
  simp

lemma qh_invariant [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ)))
    (l j : Fin n) (hlj : l < j) :
    Formalism.GradedWeylDivisibility.colAddGen R l j Q = rename some Q := by
  have h := qh_generic (B := MvPolynomial (Option (Fin n × Fin n)) R)
    (Matrix.transvection j l (X none)) (Matrix.of fun a c : Fin n => X (some (c, a)))
    (fun a c hac => by
      have : ¬ (j = a ∧ l = c) := by rintro ⟨rfl, rfl⟩; exact absurd hlj (not_lt.2 hac.le)
      simp [Matrix.transvection, hac.ne, this])
    (fun a => by
      have : ¬ (j = a ∧ l = a) := by rintro ⟨rfl, h⟩; exact hlj.ne h
      simp [Matrix.transvection, this])
    (qh_det_ne (rename some : MvPolynomial (Fin n × Fin n) R →ₐ[R] _).toRingHom
      (rename_injective _ (Option.some_injective _)) |> fun h => by simpa using h) Q ν hQ
  have e3 : (∏ a, (Matrix.transvection j l (X none : MvPolynomial (Option (Fin n × Fin n)) R)) a a ^ ν a) = 1 := by
    apply Finset.prod_eq_one
    intro a _
    have : ¬ (j = a ∧ l = a) := by rintro ⟨rfl, h⟩; exact hlj.ne h
    simp [Matrix.transvection, this]
  rw [e3, one_mul] at h
  have e1 : Formalism.GradedWeylDivisibility.colAddGen R l j Q = aeval (fun v : Fin n × Fin n => ((Matrix.transvection j l (X none)) *
      (Matrix.of fun a c : Fin n => (X (some (c, a)) : MvPolynomial (Option (Fin n × Fin n)) R)) :
        Matrix (Fin n) (Fin n) (MvPolynomial (Option (Fin n × Fin n)) R)) v.2 v.1) Q := by
    rw [Formalism.GradedWeylDivisibility.colAddGen]; congr 2; funext v
    by_cases hv : v.2 = j
    · rw [if_pos hv, hv, Matrix.transvection_mul_apply_same]
      simp [← hv]
    · rw [if_neg hv, Matrix.transvection_mul_apply_of_ne _ _ _ _ hv]
      simp
  rw [e1, h, ← aeval_X_left_apply (rename some Q), aeval_rename]
  rfl

lemma qh_mem_dualWeyl [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n ν := by
  rw [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf]
  refine ⟨qh_homog Q ν hQ, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  intro l j hlj
  exact qh_invariant Q ν hQ l j hlj

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section -- merged from Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QhEquivOfCount
noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_lt_colH_iff {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      exact (not_le.mpr hc) (hm.2.trans (hmu hmt))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega
  · intro h
    have hsub : Finset.Iic t ⊆ (univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ m, h.trans (hmu hm)⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega

lemma qh_le_last [NeZero n] (a : Fin n) : a ≤ lastIdx n := by
  rw [Fin.le_iff_val_le_val]
  show a.val ≤ n - 1
  have := a.isLt
  omega

lemma qh_count [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) :
    ((TCols mu).filter (fun c => t.val < colH mu c)).card = (mu t - mu (lastIdx n)).toNat := by
  have h0 : mu t ≤ mu 0 := hmu (by first | exact Fin.zero_le _ | (rw [Fin.le_iff_val_le_val]; simp))
  have hset : (TCols mu).filter (fun c => t.val < colH mu c) =
      Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    simp only [Finset.mem_filter, qh_lt_colH_iff hmu, TCols, Finset.mem_Ioc]
    exact ⟨fun hh => ⟨hh.1.1, hh.2⟩, fun hh => ⟨⟨hh.1, hh.2.trans h0⟩, hh.2⟩⟩
  rw [hset, Int.card_Ioc]

lemma qh_weight_sum [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun _ : Fin n => mu (lastIdx n)) +
      ∑ c : ↥(TCols mu), (fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0) = mu := by
  funext a
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [Finset.sum_coe_sort (TCols mu) (fun c => if a.val < colH mu c then (1 : ℤ) else 0),
    Finset.sum_boole, qh_count hmu a,
    Int.toNat_of_nonneg (sub_nonneg.mpr (hmu (qh_le_last a)))]
  ring

lemma qh_mapCoord_alg (P : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) R (algebraMap _ _ P) = algebraMap _ _ (MvPolynomial.map (Int.castRingHom R) P) := by
  first
    | (rw [mapCoord, IsLocalization.Away.AwayMap.lift_eq]; try rfl; done)
    | (rw [mapCoord, IsLocalization.Away.lift_eq]; try rfl; done)
    | (simp [mapCoord]; done)
    | (unfold mapCoord; exact IsLocalization.lift_eq _ _)

lemma qh_mapCoord_detU (z : ℤ) :
    mapCoord R ((detU n ^ z : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((qhDet R n ^ z : (GLCoord R n)ˣ) : GLCoord R n) := by
  have h1 : Units.map (mapCoord (n := n) R).toMonoidHom (detU n) = qhDet R n := by
    apply Units.ext
    rw [Units.coe_map, qhDet_val]
    show mapCoord (n := n) R (algebraMap _ _ (genMat ℤ n).det) = _
    rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R)) (genMat ℤ n),
      genMat_map_coord]
  rw [← h1, ← map_zpow (Units.map (mapCoord (n := n) R).toMonoidHom) (detU n) z, Units.coe_map]
  try rfl

lemma qh_can_emb [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have hmem : ∀ x : Fin (colH mu c), Fin.castLE (colH_le mu c) x ∈ (canT mu c).1 := by
    intro x
    first
      | (simp only [canT, Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨x, rfl⟩)
      | simp [canT]
  have hmono : StrictMono (Fin.castLE (colH_le mu c)) := by
    intro x y hxy
    rw [Fin.lt_iff_val_lt_val] at hxy ⊢
    exact hxy
  exact (congrFun (Finset.orderEmbOfFin_unique (canT mu c).2 hmem hmono) a).symm

lemma qh_mapCoord_minor [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (S : Finset (Fin n))
    (hS : S.card = colH mu c) :
    mapCoord R (minorC (canT mu c).1 S (canT mu c).2 hS) =
      qhN R (colH mu c) (colH_le mu c) (fun q => S.orderEmbOfFin hS q) := by
  unfold minorC qhN
  rw [qh_mapCoord_alg, RingHom.map_det (MvPolynomial.map (Int.castRingHom R))]
  congr 2
  ext p q
  first
    | (simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, genMat, MvPolynomial.map_X,
        qh_can_emb]; done)
    | simp [genMat, qh_can_emb]

lemma qh_mapCoord_brk [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord R (brk mu I) = ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) *
      ∏ c : ↥(TCols mu), qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q) := by
  first
    | (simp only [brk, TMat]
       rw [map_mul, map_prod, qh_mapCoord_detU]
       congr 1
       refine Finset.prod_congr rfl (fun c _ => ?_)
       exact qh_mapCoord_minor mu c _ _)
    | (simp only [brk, TMat, map_mul, map_prod, qh_mapCoord_detU,
        qh_mapCoord_minor])

lemma qh_brk_mem [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    mapCoord R (brk mu I) ∈ inducedSections R mu := by
  rw [qh_mapCoord_brk]
  have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) (mu (lastIdx n)))
    (qh_prod_mem (R := R) (Finset.univ : Finset ↥(TCols mu))
      (fun c => qhN R (colH mu c) (colH_le mu c) (fun q => (I c).1.orderEmbOfFin (I c).2 q))
      (fun c => fun a : Fin n => if a.val < colH mu c then (1 : ℤ) else 0)
      (fun c _ => qh_N_mem (R := R) (colH mu c) (colH_le mu c) _))
  first
    | (rw [qh_weight_sum hmu] at h; exact h)
    | (convert h using 2; exact (qh_weight_sum hmu).symm)

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

def qhM (R : Type) [CommRing R] {n : ℕ} (s : ℕ) (J : ℕ → Fin n) : GLCoord R n :=
  if hs : s ≤ n then qhN R s hs (fun q => J q.val) else 0

lemma qhM_zero (J : ℕ → Fin n) : qhM R 0 J = 1 := by
  unfold qhM qhN
  rw [dite_eq_left (Nat.zero_le n)]
  simp [Matrix.det_isEmpty]

lemma qhM_full (J : ℕ → Fin n) : ∃ ε : R, qhM R n J = ε • ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) := by
  unfold qhM
  rw [dite_eq_left le_rfl]
  unfold qhN
  by_cases hJ : Function.Injective (fun q : Fin n => J q.val)
  · let σ : Equiv.Perm (Fin n) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hJ)
    refine ⟨((Equiv.Perm.sign σ : ℤ) : R), ?_⟩
    have hM : (Matrix.of fun p q : Fin n => genMat R n (Fin.castLE le_rfl p) (J q.val)) =
        (genMat R n).submatrix id σ := by
      ext p q
      simp [σ]
    rw [hM, Matrix.det_permute']
    change _ = _ • algebraMap _ (GLCoord R n) (genMat R n).det
    simp [Algebra.smul_def, map_mul, map_intCast]
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hJ
    refine ⟨0, ?_⟩
    have hz : (Matrix.of fun p q : Fin n => genMat R n (Fin.castLE le_rfl p) (J q.val)).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.of_apply, hab])
    simp only [hz, map_zero, zero_smul]

lemma qh_initMinor [NeZero n] {s : ℕ} (I : Fin s → Fin n) (hs : s ≤ n) :
    algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.initMinor R I hs)) =
      qhM R s (fun q => if h : q < s then I ⟨q, h⟩ else 0) := by
  unfold qhM qhN Formalism.GradedWeylDivisibility.initMinor
  rw [dite_eq_left hs]
  congr 1
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp [genMat, AlgHom.mapMatrix_apply, Matrix.transpose_apply]

private theorem lt_colH_iff_le_of_dominant {mu : Fin n → ℤ} (hmu : Dominant mu) (t : Fin n) (c : ℤ) :
    t.val < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (univ.filter fun m : Fin n => c ≤ mu m) ⊆ Iio t := by
      intro m hm
      simp only [mem_filter, mem_univ, true_and] at hm
      rw [mem_Iio]
      by_contra hmt
      push_neg at hmt
      have := hmu hmt
      linarith
    have := card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hsub : Iic t ⊆ (univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [mem_Iic] at hm
      simp only [mem_filter, mem_univ, true_and]
      exact le_trans h (hmu hm)
    have := card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

lemma qh_count_all [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (k : ℕ) (hk : 0 ≤ mu (lastIdx n) + k)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ κ, sz κ ≤ n)
    (hshape : ∀ t : Fin n, (Formalism.GradedWeylDivisibility.shapeDeg sz t : ℤ) = mu t + k) (t : ℕ) :
    (univ.filter fun κ : {κ // 0 < sz κ} => t < sz κ.1).card =
      (univ.filter fun x : Fin (mu (lastIdx n) + k).toNat ⊕ ↥(TCols mu) =>
        t < Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c) x).card := by
  by_cases htn : t < n
  · have h1 : (univ.filter fun κ : {κ // 0 < sz κ} => t < sz κ.1).card =
        (univ.filter fun κ : Fin K => t < sz κ).card := by
      refine Finset.card_bij (fun κ _ => κ.1) ?_ ?_ ?_
      · intro κ hκ
        simpa using hκ
      · intro a _ b _ h
        exact Subtype.ext h
      · intro κ hκ
        simp only [mem_filter, mem_univ, true_and] at hκ
        exact ⟨⟨κ, by omega⟩, by simpa using hκ, rfl⟩
    have h2 := hshape ⟨t, htn⟩
    unfold Formalism.GradedWeylDivisibility.shapeDeg at h2
    simp only [Fin.val_mk] at h2
    have hle : mu ⟨t, htn⟩ ≤ mu 0 := hmu (by rw [Fin.le_def]; simp)
    have hlast : mu (lastIdx n) ≤ mu ⟨t, htn⟩ := hmu (by rw [Fin.le_def]; simp [lastIdx]; omega)
    have key : (univ.filter fun c : ↥(TCols mu) => t < colH mu c.1).card =
        (Ioc (mu (lastIdx n)) (mu ⟨t, htn⟩)).card := by
      refine Finset.card_bij (fun c _ => c.1) ?_ ?_ ?_
      · intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc
        have hc2 := c.2
        simp only [TCols, mem_Ioc] at hc2
        rw [mem_Ioc]
        exact ⟨hc2.1, (lt_colH_iff_le_of_dominant hmu ⟨t, htn⟩ c.1).mp hc⟩
      · intro a _ b _ h
        exact Subtype.ext h
      · intro c hc
        rw [mem_Ioc] at hc
        refine ⟨⟨c, by simp only [TCols, mem_Ioc]; exact ⟨hc.1, hc.2.trans hle⟩⟩, ?_, rfl⟩
        simp only [mem_filter, mem_univ, true_and]
        exact (lt_colH_iff_le_of_dominant hmu ⟨t, htn⟩ c).mpr hc.2
    have hR : (univ.filter fun x : Fin (mu (lastIdx n) + k).toNat ⊕ ↥(TCols mu) =>
        t < Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c) x).card =
        (mu (lastIdx n) + k).toNat + (univ.filter fun c : ↥(TCols mu) => t < colH mu c.1).card := by
      rw [card_filter, card_filter, Fintype.sum_sum_type]
      simp [htn]
      exact (card_filter _ _).symm
    rw [h1, hR, key, Int.card_Ioc]
    omega
  · push_neg at htn
    have a : ∀ κ : {κ // 0 < sz κ}, ¬ t < sz κ.1 := by
      intro κ
      have := hsz κ.1
      omega
    have b : ∀ x : Fin (mu (lastIdx n) + k).toNat ⊕ ↥(TCols mu),
        ¬ t < Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c) x := by
      intro x
      cases x with
      | inl _ =>
        simp only [Sum.elim_inl]
        omega
      | inr c =>
        simp only [Sum.elim_inr]
        have : colH mu c ≤ n := by
          unfold colH
          exact (card_filter_le _ _).trans (by simp)
        omega
    rw [card_eq_zero.mpr (filter_false_of_mem fun κ _ => a κ),
      card_eq_zero.mpr (filter_false_of_mem fun x _ => b x)]

private theorem mapCoord_mvPolynomial_int (x : MvPolynomial (Fin n × Fin n) ℤ) :
    mapCoord (n := n) R (algebraMap _ (GLCoord ℤ n) x) =
      algebraMap _ (GLCoord R n) (MvPolynomial.map (Int.castRingHom R) x) := by
  unfold mapCoord
  simp [IsLocalization.Away.lift]

private theorem exists_qhM_eq_smul_det {s : ℕ} (hs : s ≤ n) (J : ℕ → Fin n) :
    ∃ (S : Finset (Fin n)) (hS : S.card = s) (ε : R), qhM R s J =
      ε • algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)
        (Matrix.of fun a b : Fin s => genMat R n (Fin.castLE hs a) (S.orderEmbOfFin hS b)).det := by
  unfold qhM qhN
  rw [dite_eq_left hs]
  by_cases hJ : Function.Injective (fun q : Fin s => J q.val)
  · let S := univ.image (fun q : Fin s => J q.val)
    have hS : S.card = s := by
      rw [card_image_of_injective _ hJ]
      simp
    have hmem : ∀ b : Fin s, J b.val ∈ S := fun b => mem_image_of_mem _ (mem_univ b)
    let g : Fin s → Fin s := fun b => (S.orderIsoOfFin hS).symm ⟨J b.val, hmem b⟩
    have hg : ∀ b, S.orderEmbOfFin hS (g b) = J b.val := by
      intro b
      rw [← Finset.coe_orderIsoOfFin_apply]
      simp only [g, OrderIso.apply_symm_apply]
    have ginj : Function.Injective g := by
      intro a b h
      apply hJ
      simp only
      rw [← hg a, ← hg b, h]
    let σ : Equiv.Perm (Fin s) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp ginj)
    refine ⟨S, hS, ((Equiv.Perm.sign σ : ℤ) : R), ?_⟩
    have hM : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q.val)) =
        (Matrix.of fun a b : Fin s => genMat R n (Fin.castLE hs a) (S.orderEmbOfFin hS b)).submatrix id σ := by
      ext p q
      simp only [Matrix.of_apply, Matrix.submatrix_apply, id]
      rw [show σ q = g q from rfl, hg q]
    rw [hM, Matrix.det_permute']
    simp [Algebra.smul_def, map_mul, map_intCast]
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hJ
    refine ⟨univ.map (Fin.castLEEmb hs), by simp, 0, ?_⟩
    have hz : (Matrix.of fun p q : Fin s => genMat R n (Fin.castLE hs p) (J q.val)).det = 0 :=
      Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.of_apply, hab])
    simp only [hz, map_zero, zero_smul]

private theorem exists_equiv_comp_eq_of_card_filter_lt_eq {α β : Type} [Fintype α] [Fintype β] (f : α → ℕ) (g : β → ℕ)
    (hf : ∀ x, 0 < f x) (hg : ∀ y, 0 < g y)
    (h : ∀ t, (univ.filter fun x => t < f x).card = (univ.filter fun y => t < g y).card) :
    ∃ e : α ≃ β, ∀ x, g (e x) = f x := by
  have key : ∀ {γ : Type} [Fintype γ] (u : γ → ℕ) (v : ℕ), 0 < v →
      (univ.filter fun x => v - 1 < u x).card =
        (univ.filter fun x => u x = v).card + (univ.filter fun x => v < u x).card := by
    intro γ _ u v hv
    classical
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_union]
      omega
    · rw [disjoint_filter]
      intro x _ h1 h2
      omega
  have hfib : ∀ v, Fintype.card {x // f x = v} = Fintype.card {y // g y = v} := by
    intro v
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases Nat.eq_zero_or_pos v with hv | hv
    · subst hv
      rw [filter_false_of_mem (fun x _ => (hf x).ne'), filter_false_of_mem (fun y _ => (hg y).ne')]
      simp
    · have a := key f v hv
      have b := key g v hv
      rw [h (v - 1), h v] at a
      omega
  let e : α ≃ β := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun v => Fintype.equivOfCardEq (hfib v)).trans (Equiv.sigmaFiberEquiv g))
  exact ⟨e, fun x => (Fintype.equivOfCardEq (hfib (f x)) ⟨x, rfl⟩).2⟩

private theorem mapCoord_card_eq_finsets {h : ℕ} (J S : Finset (Fin n)) (hJ : J.card = h) (hS : S.card = h) :
    mapCoord (n := n) R (minorC J S hJ hS) =
      algebraMap _ (GLCoord R n)
        (Matrix.of fun a b : Fin h => genMat R n (J.orderEmbOfFin hJ a) (S.orderEmbOfFin hS b)).det := by
  unfold minorC
  rw [mapCoord_mvPolynomial_int, RingHom.map_det]
  refine congrArg _ (congrArg Matrix.det ?_)
  ext a b
  simp [genMat]

private theorem orderEmbOfFin_canT_eq_castLE [NeZero n] (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (canT mu c).2 (f := Fin.castLE (colH_le mu c))
    (fun x => by simp [canT]) (fun a b h => by rw [Fin.lt_def] at h ⊢; simpa using h)
  rw [← this]

private theorem mapCoord_intCast (m : ℤ) :
    mapCoord (n := n) R ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) =
      ((qhDet R n ^ m : (GLCoord R n)ˣ) : GLCoord R n) := by
  have hu : Units.map (mapCoord (n := n) R).toMonoidHom (detU n) = qhDet R n := by
    ext
    rw [Units.coe_map, qhDet_val]
    show mapCoord (n := n) R (algebraMap _ _ (genMat ℤ n).det) = _
    rw [mapCoord_mvPolynomial_int, RingHom.map_det, genMat_map_coord]
  calc mapCoord (n := n) R ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)
      = ((Units.map (mapCoord (n := n) R).toMonoidHom (detU n ^ m) : (GLCoord R n)ˣ) : GLCoord R n) :=
        (Units.coe_map _ _).symm
    _ = ((qhDet R n ^ m : (GLCoord R n)ˣ) : GLCoord R n) := by rw [map_zpow, hu]

lemma qh_bidet_mem [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (k : ℕ) (hk : 0 ≤ mu (lastIdx n) + k)
    {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ κ, sz κ ≤ n) (I : ∀ κ, Fin (sz κ) → Fin n)
    (hshape : ∀ t : Fin n, (Formalism.GradedWeylDivisibility.shapeDeg sz t : ℤ) = mu t + k) :
    ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
      algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I)) ∈
      Submodule.span R (Set.range fun I : TIdx mu => mapCoord (n := n) R (brk mu I)) := by
  have h0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hpos_c : ∀ c : ↥(TCols mu), 0 < colH mu c := by
    intro c
    have hc := c.2
    simp only [TCols, mem_Ioc] at hc
    have e0 : (⟨0, h0⟩ : Fin n) = 0 := Fin.ext (by simp)
    exact (lt_colH_iff_le_of_dominant hmu ⟨0, h0⟩ c.1).mpr (by rw [e0]; exact hc.2)
  obtain ⟨e, he⟩ := exists_equiv_comp_eq_of_card_filter_lt_eq (fun κ : {κ // 0 < sz κ} => sz κ.1)
    (Sum.elim (fun _ => n) (fun c : ↥(TCols mu) => colH mu c)) (fun κ => κ.2)
    (by
      intro y
      cases y with
      | inl _ => exact h0
      | inr c => exact hpos_c c)
    (qh_count_all hmu k hk sz hsz hshape)
  have hprod : algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I)) =
      ∏ κ, qhM R (sz κ) (fun q => if h : q < sz κ then I κ ⟨q, h⟩ else 0) := by
    unfold Formalism.GradedWeylDivisibility.bideterminant
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl (fun κ _ => qh_initMinor (I κ) (hsz κ))
  set F : Fin K → GLCoord R n := fun κ => qhM R (sz κ) (fun q => if h : q < sz κ then I κ ⟨q, h⟩ else 0)
    with hF
  have gen0 : ∀ s (J : ℕ → Fin n), s = 0 → qhM R s J = 1 := by
    intro s J hs
    rw [hs]
    exact qhM_zero J
  have hone : ∀ κ : {κ // ¬ 0 < sz κ}, F κ.1 = 1 := by
    intro κ
    have hz : sz κ.1 = 0 := by
      have := κ.2
      omega
    simp only [hF]
    exact gen0 _ _ hz
  have hsub : ∏ κ, F κ = ∏ κ : {κ // 0 < sz κ}, F κ.1 := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun κ => 0 < sz κ) F, Fintype.prod_eq_one _ hone, mul_one]
  have hre : ∏ κ : {κ // 0 < sz κ}, F κ.1 = ∏ y, F (e.symm y).1 :=
    Fintype.prod_equiv e _ _ (fun x => by simp)
  have hsz_l : ∀ i, sz (e.symm (Sum.inl i)).1 = n := by
    intro i
    have := he (e.symm (Sum.inl i))
    simp only [Equiv.apply_symm_apply, Sum.elim_inl] at this
    exact this.symm
  have hsz_r : ∀ c, sz (e.symm (Sum.inr c)).1 = colH mu c := by
    intro c
    have := he (e.symm (Sum.inr c))
    simp only [Equiv.apply_symm_apply, Sum.elim_inr] at this
    exact this.symm
  have hl : ∀ i, ∃ ε : R, F (e.symm (Sum.inl i)).1 = ε • (qhDet R n : GLCoord R n) := by
    intro i
    have gen : ∀ s (J : ℕ → Fin n), s = n → ∃ ε : R, qhM R s J = ε • (qhDet R n : GLCoord R n) := by
      intro s J hs
      rw [hs]
      exact qhM_full J
    simp only [hF]
    exact gen _ _ (hsz_l i)
  choose ε1 hε1 using hl
  have hr : ∀ c : ↥(TCols mu), ∃ (S : Finset (Fin n)) (hS : S.card = colH mu c) (ε : R),
      F (e.symm (Sum.inr c)).1 = ε • algebraMap _ (GLCoord R n)
        (Matrix.of fun a b : Fin (colH mu c) =>
          genMat R n (Fin.castLE (colH_le mu c) a) (S.orderEmbOfFin hS b)).det := by
    intro c
    have gen : ∀ s (J : ℕ → Fin n), s = colH mu c → ∃ (S : Finset (Fin n)) (hS : S.card = colH mu c) (ε : R),
        qhM R s J = ε • algebraMap _ (GLCoord R n)
          (Matrix.of fun a b : Fin (colH mu c) =>
            genMat R n (Fin.castLE (colH_le mu c) a) (S.orderEmbOfFin hS b)).det := by
      intro s J hs
      subst hs
      exact exists_qhM_eq_smul_det (colH_le mu c) J
    simp only [hF]
    exact gen _ _ (hsz_r c)
  choose S hS ε2 hε2 using hr
  let I' : TIdx mu := fun c => ⟨S c, hS c⟩
  have hbrk : mapCoord (n := n) R (brk mu I') =
      ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) *
        ∏ c : ↥(TCols mu), algebraMap _ (GLCoord R n)
          (Matrix.of fun a b : Fin (colH mu c) =>
            genMat R n (Fin.castLE (colH_le mu c) a) ((S c).orderEmbOfFin (hS c) b)).det := by
    unfold brk TMat
    rw [map_mul, map_prod, mapCoord_intCast]
    congr 1
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [mapCoord_card_eq_finsets]
    refine congrArg _ (congrArg Matrix.det ?_)
    ext a b
    simp only [Matrix.of_apply]
    rw [orderEmbOfFin_canT_eq_castLE]
  have hD : ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
      (qhDet R n : GLCoord R n) ^ (mu (lastIdx n) + k).toNat =
      ((qhDet R n ^ mu (lastIdx n) : (GLCoord R n)ˣ) : GLCoord R n) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
    congr 2
    omega
  have hval : ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
      algebraMap _ (GLCoord R n) (rename Prod.swap (Formalism.GradedWeylDivisibility.bideterminant R sz hsz I)) =
      ((∏ i, ε1 i) * ∏ c, ε2 c) • mapCoord (n := n) R (brk mu I') := by
    rw [hprod, hsub, hre, Fintype.prod_sum_type, Finset.prod_congr rfl (fun i _ => hε1 i),
      Finset.prod_congr rfl (fun c _ => hε2 c), hbrk, ← hD]
    simp only [Algebra.smul_def, Finset.prod_mul_distrib, map_mul, map_prod, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  rw [hval]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I', rfl⟩)

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} {R : Type} [CommRing R]

lemma qh_reduce [IsDomain R] (mu : Fin n → ℤ) (f : GLCoord R n) (hf : f ∈ inducedSections R mu) :
    ∃ (k : ℕ) (Q : MvPolynomial (Fin n × Fin n) R), (∀ a, 0 ≤ mu a + k) ∧
      f = ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
        algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∧
      Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n (fun a => (mu a + k).toNat) := by
  obtain ⟨N, P, hNP⟩ := IsLocalization.Away.surj (genMat R n).det f
  have hk : ∀ a, 0 ≤ mu a + ((N + (Finset.univ.sup fun b => (-mu b).toNat) : ℕ) : ℤ) := by
    intro a
    have h1 := Int.self_le_toNat (-mu a)
    have h2 : (-mu a).toNat ≤ Finset.univ.sup fun b => (-mu b).toNat :=
      Finset.le_sup (f := fun b => (-mu b).toNat) (Finset.mem_univ a)
    push_cast
    omega
  set M : ℕ := Finset.univ.sup fun b => (-mu b).toNat with hM
  have hswap : rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M)) = P * (genMat R n).det ^ M := by
    rw [rename_rename, Prod.swap_swap_eq, rename_id_apply]
  have hmain : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) =
      f * algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [hswap, map_mul, map_pow, pow_add, ← mul_assoc, hNP]
  have hunit : ((qhDet R n ^ ((N + M : ℕ) : ℤ) : (GLCoord R n)ˣ) : GLCoord R n) =
      algebraMap _ (GLCoord R n) (genMat R n).det ^ (N + M) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, qhDet_val]
  refine ⟨N + M, rename Prod.swap (P * (genMat R n).det ^ M), hk, ?_, ?_⟩
  · rw [hmain, ← hunit, mul_comm f, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, one_mul]
  · have hmem : algebraMap _ (GLCoord R n) (rename Prod.swap (rename Prod.swap (P * (genMat R n).det ^ M))) ∈
        inducedSections R (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) := by
      rw [hmain, mul_comm, ← hunit]
      have h := qh_mul_mem (qh_det_zpow_mem (R := R) (n := n) ((N + M : ℕ) : ℤ)) hf
      have e : (fun a => ((mu a + ((N + M : ℕ) : ℤ)).toNat : ℤ)) = (fun _ : Fin n => ((N + M : ℕ) : ℤ)) + mu := by
        funext a
        rw [Pi.add_apply, Int.toNat_of_nonneg (hk a), add_comm]
      rw [e]
      exact h
    exact qh_mem_dualWeyl _ _ hmem

lemma qh_span_transfer (T : Submodule R (GLCoord R n)) (u : GLCoord R n)
    (S : Set (MvPolynomial (Fin n × Fin n) R))
    (h : ∀ x ∈ S, u * algebraMap _ (GLCoord R n) (rename Prod.swap x) ∈ T)
    (Q : MvPolynomial (Fin n × Fin n) R) (hQ : Q ∈ Submodule.span R S) :
    u * algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ T := by
  let L : MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
    (LinearMap.mulLeft R u).comp ((IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap.comp
      (rename Prod.swap).toLinearMap)
  have hle : Submodule.span R S ≤ T.comap L := Submodule.span_le.mpr (fun x hx => h x hx)
  exact hle hQ

private theorem antitone_of_step_lemma {n : ℕ} (g : Fin n → ℤ) (h : ∀ l j : Fin n, (j : ℕ) = l + 1 → g j ≤ g l) :
    Antitone g := by
  intro a b hab
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  simp only [Fin.mk_le_mk] at hab
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro hb; exact le_rfl
  | succ b hab ih =>
    intro hb
    exact (h ⟨b, by omega⟩ ⟨b + 1, hb⟩ rfl).trans (ih (by omega))

theorem highest_weight_corollary_one : InducedSectionsSpanStatement := by
  intro n _ mu R _ _ _
  constructor
  · intro hmu
    apply Set.Subset.antisymm
    · intro f hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R n n] at hQ
      rw [SetLike.mem_coe, hfQ]
      refine qh_span_transfer (Submodule.span R (Set.range fun I : TIdx mu => mapCoord R (brk mu I))) _ _ ?_ Q hQ
      rintro x ⟨K, sz, hsz, I, hsh, rfl⟩
      exact qh_bidet_mem hmu k (hk _) sz hsz I (fun t => by rw [hsh]; exact Int.toNat_of_nonneg (hk t))
    · exact qh_span_le (by rintro _ ⟨I, rfl⟩; exact qh_brk_mem hmu I)
  · intro hmu
    ext f
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hf
      obtain ⟨k, Q, hk, hfQ, hQ⟩ := qh_reduce mu f hf
      by_contra hf0
      have hQ0 : Q ≠ 0 := by
        rintro rfl
        apply hf0
        rw [hfQ]
        simp
      apply hmu
      have hInt := Formalism.GradedWeylDivisibility.leadInterlaced R n n _ Q hQ hQ0
      have hcol := Formalism.GradedWeylDivisibility.colSums R n n _ Q hQ _ (MonomialOrder.degree_mem_support (m := Formalism.GradedWeylDivisibility.colLex n n) hQ0)
      set m := (Formalism.GradedWeylDivisibility.colLex n n).degree Q
      apply antitone_of_step_lemma mu
      intro l j hlj
      have hI : Formalism.GradedWeylDivisibility.InterlacedAt 0 l j m := hInt l j hlj
      have hI2 := hI (lastIdx n)
      have e1 : (∑ b : Fin n with b ≤ lastIdx n, m (b, j)) = ∑ b, m (b, j) := by
        rw [Finset.filter_true_of_mem (fun b _ => qh_le_last b)]
      have e2 : (∑ b : Fin n with b < lastIdx n, m (b, l)) ≤ ∑ b, m (b, l) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      have cj := hcol j
      have cl := hcol l
      have tj := Int.toNat_of_nonneg (hk j)
      have tl := Int.toNat_of_nonneg (hk l)
      omega
    · rintro rfl
      exact qh_zero_mem mu

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

section B1
end B1

section B2
end B2

section B9
theorem global_sections_schur (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.GlobalSectionsSchur D := fun n _ mu R _ _ hR =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one n mu R hR
end B9

section lowerOffDiagonalCoeff
theorem bracket_polynomial_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.BracketPolynomialSpan D := fun n _ mu hmu =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two n mu hmu
end lowerOffDiagonalCoeff

section Mod

end Mod

section B6
end B6

end Formalism.MainNotions.G.ColumnFamilies
end
end

namespace Formalism.MainNotions.G.ColumnFamilies.Top

open Formalism.MainNotions.CovariantDegrees

theorem b9 (D : Formalism.BasicNotions.D7) : GlobalSectionsSchur D := global_sections_schur D
theorem b10 (D : Formalism.BasicNotions.D7) : BracketPolynomialSpan D := bracket_polynomial_span D
theorem b11 (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := adm_eleven D
theorem b15 (D : Formalism.BasicNotions.D7) : SaturatedLowerSetSpan D := admissible_lowerSet_span D
theorem b19 (D : Formalism.BasicNotions.D7) : WeylDualityLattice D := admissible_lattice_biduality D
theorem a2 (D : Formalism.BasicNotions.D7) : PathColumnBasis D := admissible_polynomial_basis D

end Formalism.MainNotions.G.ColumnFamilies.Top
