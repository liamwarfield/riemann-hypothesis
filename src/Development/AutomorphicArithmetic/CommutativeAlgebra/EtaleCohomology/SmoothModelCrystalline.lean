module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.EndEx
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.BInEx
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.PinFixed
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiIterPull
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitPointGeneric
public import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsFiniteSectionsDeterminingRingHomOfSmooth
public import Development.AutomorphicArithmetic.EtaleIdempotents.NatCastPrimeNeZeroAndNotIsUnitIntegers
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiAIter
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EqZeroOfCoord
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PullbackFinRelation
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGeoSide
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiStepOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmooth2

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ResidueExistence.ResEx
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison

theorem UpperTheory.Gal.CD.resEx :
    CrystallineSemistableComparison.ResEx := CrystallineSemistableComparison.resEx
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Final
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

def CIn (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (r : Res l K) (f : ℕ) : Prop :=
  ∃ (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (N : ℕ) (F : Pb.Fac r N), (per l K).Facts ∧ EtSide (l := l) (K := K) Model.Sm ∧
    (dat Amp).Laws Model.Sm ∧ Nonempty (BMap Model.Sm (dat Amp)) ∧ Nonempty (PMap Model.Sm (dat Amp)) ∧ f ∣ N ∧ Pb.Mid.TeichmullerCongruence r N ∧
    ∀ M : Model l K, M.Sm → ∀ j, Pin F M j ∧ BIn M j

def Final : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  [IsDomain (OK l K)] [IsDiscreteValuationRing (OK l K)] (r : Res l K) (f : ℕ), 0 < f → (∀ x : r.k, x ^ l ^ f = x) → CIn l K r f →
  ∀ (ϖ : OK l K), Irreducible ϖ → ∀ (M : Model l K), M.Sm → ∀ (n j : ℕ) (T : Fin (n + 1) → Corr l M.X)
    (hr : ∀ i, (T i).r ≫ M.p = (T i).p ≫ M.p), PtId l (l ^ f) n (fn M.p ϖ) T →
  ∀ A : Fin (n + 1) → (M.V j →ₗ[ℚ_[l]] M.V j), (∀ i, IsHk M (T i) (hr i) j (A i)) → ∀ B₀ : PB l K, ∃ N : ℕ, ∀ x, IsInv B₀ M j x →
    ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)) •
      TensorProduct.map (A i) (B₀.φ.toLinearMap ^ (f * (n - i + N))) x = 0

end UpperTheory.Ru.crystallineComparison
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CIn
open CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

theorem cIn (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K) (f : ℕ)
    (hf : 0 < f) : CIn l K r f := by
  obtain ⟨N, h1, h2, F, h3⟩ := CrystallineSemistableComparison.crystallineComparison.pinEx l K r f hf
  obtain ⟨Amp, -, -, -, a1, a2, a3, a4, a5, -⟩ := CrystallineSemistableComparison.crystallineComparison.endEx (fun l _ K _ => UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K) l K
  exact ⟨Amp, N, F, a1, a2, a3, a4, a5, h1, h2, fun M hM j => ⟨h3 M hM j, CrystallineSemistableComparison.crystallineComparison.bInEx l K M hM j⟩⟩

end UpperTheory.Ru.crystallineComparison
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FinAllOf
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.QuasiCompactOfProj
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EPin
open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.ePin :
    ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (G : Model l K → Prop) (Amp : ∀ M : Model l K, E.LineData M.X → Prop) (e : E.EtFam l K), e.Good → ∃ e' : EMap G (dat Amp), ∀ (M : Model l K) (a : (dat Amp).Ch M) (j : ℕ) (v : M.T j) (n : ℕ), (show (M.MS j).lim from e'.e a j v).1 n = e M n j (v.lev n) := by
  intro l _ K G Amp e he
  refine ⟨{
    e := fun {M} _ j => GlueE.eMap e he.red M j
    lin := fun {M} _ _ j z v => GlueE.eMap_lin e he.red M j (per l K).z z v
    act := fun {M} _ _ j _ v => GlueE.eMap_act e he.red he.equi M j _ v
    phi := fun {M} _ _ j v => GlueE.eMap_phi e he.red he.phi M j v
    nat := fun {_ _ u hu _ _} _ _ _ j v => GlueE.eMap_nat e he.red he.nat u hu j v
    cup := fun {M} _ _ _ _ x y z h => GlueE.eMap_cup e he.red he.cup M x y z h
    one := fun {M} _ _ => GlueE.eMap_one e he.red he.one M
    c1 := fun {M} a _ => GlueE.etale_map_first_chern e he.red he.c1 M a.1 (per l K).t rfl }, ?_⟩
  intro M a j v n
  rfl
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiHIterSmul
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.MapUSharp
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private theorem normOfPt' : NormOfPt :=
  normPt_of (sameNormRing_of (normRead_of (normInt_of (normEx_of matRep_of detSplit_of) splitsBC_of
    (injSplit_of (rankDeg_of splitsField_of) splitsEquiv_of) coeffInt_of liftingProperty) etUnit_of splitsField_of valPts_of)
    valLift_of ptsProd_of congrRad_of) (baseChart_of (baseSmooth_of smoothClosed_of smoothRed_of)) secChart_of
    (etAway_of secChart_of etChart_of) genChart_of ptChart_of

private theorem wzSum {P : Type} (q n : ℕ) {I : Fin (n + 1) → Type} [∀ j, Fintype (I j)] (v : ∀ j, I j → P)
    (h : pts (wEv q) v = pts (wOd q) v) :
    ∑ x : (Σ j, I j), Finsupp.single (v x.1 x.2) ((-1 : ℤ) ^ (x.1 : ℕ) * ((q ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ)) = 0 := by
  classical
  let Φ : Multiset P →+ (P →₀ ℤ) := (Multiset.sumAddMonoidHom).comp (Multiset.mapAddMonoidHom fun p => Finsupp.single p (1 : ℤ))
  let G : Fin (n + 1) → (P →₀ ℤ) := fun j => ∑ i, Finsupp.single (v j i) (1 : ℤ)
  have hG : ∀ j, Φ (Finset.univ.val.map (v j)) = G j := fun j => by
    change ((Finset.univ.val.map (v j)).map fun p => Finsupp.single p (1 : ℤ)).sum = _
    rw [Multiset.map_map]
    rfl
  have key : ∀ a : Fin (n + 1) → ℕ, Φ (pts a v) = ∑ j, a j • G j := fun a => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pts, map_sum, map_nsmul, hG]
  have h0 : ∑ j, wEv q j • G j = ∑ j, wOd q j • G j := by rw [← key, ← key, h]
  rw [Fintype.sum_sigma]
  have e : ∀ j : Fin (n + 1), ∑ i, Finsupp.single (v j i) ((-1 : ℤ) ^ (j : ℕ) * ((q ^ ((j : ℕ).choose 2) : ℕ) : ℤ)) =
      ((wEv q j : ℤ) - (wOd q j : ℤ)) • G j := fun j => by
    have : (-1 : ℤ) ^ (j : ℕ) * ((q ^ ((j : ℕ).choose 2) : ℕ) : ℤ) = (wEv q j : ℤ) - (wOd q j : ℤ) := by
      by_cases hj : Even (j : ℕ)
      · simp [wEv, wOd, hj, hj.neg_one_pow]
      · simp [wEv, wOd, hj, (Nat.not_even_iff_odd.1 hj).neg_one_pow]
    rw [this, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Finsupp.smul_single]
  simp only [e, sub_smul, Finset.sum_sub_distrib, natCast_zsmul]
  rw [h0, sub_self]

private theorem wzPts {J P : Type} [Fintype J] {I : J → Type} [∀ j, Fintype (I j)] (a : J → ℕ) (v : ∀ j, I j → P) :
    pts a v = Finset.univ.val.map (fun x : (Σ j, Fin (a j) × I j) => v x.1 x.2.2) := by
  have hm : ∀ {K : Type} [Fintype K] (g : K → P), Finset.univ.val.map g = ∑ x, ({g x} : Multiset P) := fun {K} _ g => by
    have := Multiset.sum_map_singleton (Finset.univ.val.map g)
    rw [Multiset.map_map] at this
    exact this.symm
  simp only [pts, hm]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_prod_type]
  simp

private theorem frob_pow' (A : PAlg l) (k : ℕ) (a : A.A) : (A.frob ^ k) a = a ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih]
    change (a ^ l ^ k) ^ l = _
    rw [← pow_mul, pow_succ]

private theorem wzPhi (A : PAlg l) (m : ℕ) : ∃ φ : Qb A →+* Qb A, ∀ x, φ x = x ^ l ^ m := by
  refine ⟨Ideal.quotientMap _ (A.frob ^ m) ?_, fun x => ?_⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, frob_pow']
    exact Ideal.mem_span_singleton.2 (dvd_pow_self _ (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, frob_pow', map_pow]

private theorem wzPsi (A : PAlg l) (m : ℕ) : ∃ ψ : A.U →+* Qb A, ∀ x : A.W,
    ψ (A.th x) = Ideal.Quotient.mk _ (x.coeff 0) ^ l ^ m := by
  obtain ⟨φ, hφ⟩ := wzPhi A m
  have hxi : (Ideal.Quotient.mk (Ideal.span {A.s (pFlat l)})).comp WittVector.constantCoeff A.xi = 0 := by
    have e : WittVector.constantCoeff A.xi = - A.s (pFlat l) := by
      rw [PAlg.xi, PAlg.sW, xi0, map_sub, map_sub, map_natCast, map_natCast, PAlg.natCast_l, WittVector.map_teichmuller]
      simp [WittVector.constantCoeff_apply]
    rw [RingHom.comp_apply, e, map_neg, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), neg_zero]
  let ψ₀ : A.U →+* Qb A := Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp WittVector.constantCoeff) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hxi, mul_zero])
  refine ⟨φ.comp ψ₀, fun x => ?_⟩
  rw [RingHom.comp_apply, hφ]
  rfl

private theorem ptOf_pre {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {B C : Type} [CommRing B] [CommRing C]
    (ρ : B →+* C) (f : Γ(Y, V) →+* B) :
    Spec.map (CommRingCat.ofHom ρ) ≫ ptOf hV B f = ptOf hV C (ρ.comp f) := by
  simp only [ptOf, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

private theorem wzFr {O : Type} [CommRing O] {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of O)} {g : O →+* Qo l}
    {f : ℕ} {F : PQ q g ⟶ PQ q g} (hF : IsFr f F) (A : PAlg l) (φ : Qb A →+* Qb A) (hφ : ∀ x, φ x = x ^ l ^ f)
    {V : Y.Opens} (hV : IsAffineOpen V) (β : Γ(Y, V) →+* Qb A) (P : (PQ q g).obj A) (hP : P.1 = ptOf hV _ β) (k : ℕ) :
    ((itE F k).app A P).1 = ptOf hV _ ((φ ^ k).comp β) := by
  induction k with
  | zero =>
    simpa [itE, RingHom.one_def] using hP
  | succ k ih =>
    have e : itE F (k + 1) = itE F k ≫ F := by
      simp only [itE, pow_succ']
      rfl
    rw [e]
    change (F.app A ((itE F k).app A P)).1 = _
    rw [hF A φ hφ, ih, ptOf_pre, pow_succ', RingHom.mul_def, RingHom.comp_assoc]

private theorem wzPhiPow {B : Type} [CommRing B] (φ : B →+* B) (Q : ℕ) (hφ : ∀ x, φ x = x ^ Q) (k : ℕ) (x : B) :
    (φ ^ k) x = x ^ Q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, hφ, ← pow_mul, pow_succ]

private theorem wzNontriv (A : PAlg l) (h : ¬ Subsingleton A.A) : Nontrivial (Qb A) := by
  refine Ideal.Quotient.nontrivial_iff.2 fun ht => h ⟨fun a b => ?_⟩
  have hz : ∀ x : A.A, x = 0 := fun x => by
    have := A.compl.toIsHausdorff
    refine this.haus' x fun n => ?_
    rw [ht]
    simp [SModEq.zero, Ideal.top_pow]
  rw [hz a, hz b]

private theorem wzCore (f n : ℕ) {O : Type} [CommRing O] {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)) (g : O →+* Qo l)
    {V : Y.Opens} (hV : IsAffineOpen V) (d : Fin (n + 1) → ℕ) (N : ℕ)
    (hN : ((∑ j, wEv (l ^ f) j * d j) + 1) ^ (∑ j, wEv (l ^ f) j * d j) ≤ (l ^ f) ^ N)
    (A : Test l) (β : ∀ j, Fin (d j) → (Γ(Y, V) →+* Qb A.obj)) (φ : Qb A.obj →+* Qb A.obj)
    (hφ : ∀ x, φ x = x ^ l ^ f) (v : ∀ j, Fin (d j) → (PQ q g).obj A.obj)
    (hv : ∀ j i, (v j i).1 = ptOf hV _ ((φ ^ (n - j + N)).comp (β j i)))
    {ι : Type} [Fintype ι] (x : ι → Γ(Y, V))
    (hx : ∀ (R : Type) [CommRing R] (f₁ f₂ : Γ(Y, V) →+* R),
      ptOf hV R f₁ ≫ q = ptOf hV R f₂ ≫ q → (∀ i, f₁ (x i) = f₂ (x i)) → f₁ = f₂)
    (hS : SameNorm (pts (wEv (l ^ f)) fun j i k => β j i (x k) ^ (l ^ f) ^ (n - j))
      (pts (wOd (l ^ f)) fun j i k => β j i (x k) ^ (l ^ f) ^ (n - j))) :
    ∃ S : Fam A, IsDec S ∧ ∀ s,
      pts (wEv (l ^ f)) (fun j i => (PQ q g).map (S.f s).hom (v j i)) =
        pts (wOd (l ^ f)) (fun j i => (PQ q g).map (S.f s).hom (v j i)) ∨ Subsingleton (S.B s).obj.A := by
  classical
  by_cases hsub : Subsingleton A.obj.A
  · refine ⟨⟨Unit, fun _ => A, fun _ => 𝟙 A⟩, ⟨fun a b hab => congrFun hab (), fun b => ⟨b (), funext fun _ => rfl⟩⟩,
      fun _ => Or.inr hsub⟩
  have hnt := wzNontriv A.obj hsub
  let c : (Σ j, Fin (wEv (l ^ f) j) × Fin (d j)) → ι → Qb A.obj := fun e k => β e.1 e.2.2 (x k) ^ (l ^ f) ^ (n - e.1)
  let c' : (Σ j, Fin (wOd (l ^ f) j) × Fin (d j)) → ι → Qb A.obj := fun e k => β e.1 e.2.2 (x k) ^ (l ^ f) ^ (n - e.1)
  have hS' : SameNorm (Finset.univ.val.map c) (Finset.univ.val.map c') := by
    rw [wzPts, wzPts] at hS
    exact hS
  have hcI : Fintype.card (Σ j, Fin (wEv (l ^ f) j) × Fin (d j)) = ∑ j, wEv (l ^ f) j * d j := by
    simp [Fintype.card_sigma]
  have hcI' : Fintype.card (Σ j, Fin (wOd (l ^ f) j) × Fin (d j)) = ∑ j, wEv (l ^ f) j * d j := by
    have := (snBasic_of (Qb A.obj) ι).2.2.1 hnt _ _ hS'
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ] at this
    rw [← this, hcI]
  have hL : (l ^ f) ^ N = l ^ (f * N) := by rw [pow_mul]
  obtain ⟨e, he, hm⟩ := UpperTheory.exists_orthogonalIdempotents_matching_of_sameNorm l A.obj A.property (f * N) _ hcI hcI' (by rw [← hL]; exact hN) c c' hS'
  obtain ⟨B, fσ, hd, h1⟩ := decEx l A _ e he
  refine ⟨⟨_, B, fσ⟩, hd, fun σ => Or.inl ?_⟩
  rw [wzPts, wzPts]
  rw [← Multiset.map_univ_val_equiv σ, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  have hi := hm σ i
  let f₀ := (fσ σ).hom
  change (PQ q g).map f₀ (v i.1 i.2.2) = (PQ q g).map f₀ (v (σ i).1 (σ i).2.2)
  apply Subtype.ext
  have hpt : ∀ (j) (t), ((PQ q g).map f₀ (v j t)).1 =
      ptOf hV _ ((PAlg.mapQ f₀ (pFlat l)).comp ((φ ^ (n - j + N)).comp (β j t))) := fun j t => by
    change Spec.map (CommRingCat.ofHom (PAlg.mapQ f₀ (pFlat l))) ≫ (v j t).1 = _
    rw [hv, ptOf_pre]
  rw [hpt, hpt]
  refine congrArg _ (hx _ _ _ ?_ fun k => ?_)
  · rw [← hpt, ← hpt, ((PQ q g).map f₀ (v i.1 i.2.2)).2, ((PQ q g).map f₀ (v (σ i).1 (σ i).2.2)).2]
  · have a : ∀ (j : Fin (n + 1)) t, (φ ^ (n - j + N)) (β j t (x k)) = (β j t (x k) ^ (l ^ f) ^ (n - j)) ^ l ^ (f * N) := fun j t => by
      rw [wzPhiPow φ (l ^ f) hφ, pow_add, pow_mul, ← hL]
    have h1' : PAlg.mapQ f₀ (pFlat l) (Ideal.Quotient.mk _ (e σ)) = 1 := by
      rw [PAlg.mapQ, Ideal.quotientMap_mk]
      change Ideal.Quotient.mk _ (PAlg.Hom.f (fσ σ).hom (e σ)) = 1
      rw [h1 σ, map_one]
    have := congrArg (PAlg.mapQ f₀ (pFlat l)) (hi k)
    rw [map_mul, map_mul, h1', one_mul, one_mul] at this
    simp only [RingHom.comp_apply]
    rw [a, a]
    exact this

private theorem mapU_sharp' {A B : PAlg l} (f : A ⟶ B) (a : A.A) : PAlg.mapU f (A.sharp a) = B.sharp (PAlg.Hom.f f a) := by
  change B.th (PAlg.mapW f (WittVector.teichmuller l a)) = B.th (WittVector.teichmuller l (PAlg.Hom.f f a))
  rw [PAlg.mapW, WittVector.map_teichmuller]

private theorem wzChart {Y : Scheme.{0}} (hY : AffFin Y) {J : Type} [Finite J] (T : J → Corr l Y) (A : Test l)
    (y : Spec (CommRingCat.of A.obj.U) ⟶ Y) :
    ∃ S : Fam A, IsDec S ∧ ∀ s, ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧
      (∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V) ∧
      ⊤ ≤ (Spec.map (CommRingCat.ofHom (PAlg.mapU (S.f s).hom)) ≫ y) ⁻¹ᵁ U := by
  classical
  have hT := testFacts l A.obj A.property
  choose U V hU hV hx hUV using charts_of l Y hY J T
  obtain ⟨I, _, e, a, he, hea⟩ := UpperTheory.exists_orthogonalIdempotents_subordinate_of_etale_sections A.obj.U hT.2.2.2.1 Y (fun x => y ⁻¹' (U x : Set Y))
    (fun x => (U x).isOpen.preimage y.continuous) (fun p => ⟨y p, hx _⟩)
  obtain ⟨e₀, he₀, hs⟩ := UpperTheory.exists_orthogonalIdempotents_lift_through_sharp l A I e he
  obtain ⟨B, f, hd, h1⟩ := decEx l A I e₀ he₀
  refine ⟨⟨I, B, f⟩, hd, fun s => ⟨U (a s), V (a s), hU _, hV _, hUV _, fun p _ => ?_⟩⟩
  have h2 : PAlg.mapU (f s).hom (e s) = 1 := by
    rw [← hs, mapU_sharp']
    change (B s).obj.sharp (PAlg.Hom.f (f s).hom (e₀ s)) = 1
    rw [h1 s]
    simp [PAlg.sharp]
  have := hea s (PrimeSpectrum.comap (PAlg.mapU (f s).hom) p) (fun hmem => by
    have h3 : PAlg.mapU (f s).hom (e s) ∈ p.asIdeal := hmem
    rw [h2] at h3
    exact p.2.ne_top ((Ideal.eq_top_iff_one _).2 h3))
  exact this

private theorem wzNat {C : Type 1} [Category.{0} C] {F G : C ⥤ Type} (u : F ⟶ G) {A B : C} (f : A ⟶ B) (y : F.obj A) :
    u.app B (F.map f y) = G.map f (u.app A y) := u.naturality_apply f y

private theorem wzLocal {O : Type} [CommRing O] (f n : ℕ) {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of O)) (hq : Smooth q)
    (ϖ : O) (T : Fin (n + 1) → Corr l Y) (hr : ∀ j, (T j).r ≫ q = (T j).p ≫ q) (κ : O →+* OC l) (g : O →+* Qo l)
    (hg : g ϖ = 0) (m : ℕ) (F : PQ q g ⟶ PQ q g) (ρ : PX q κ ⟶ PQ q g) (hF : IsFr f F) (hρ : IsRd m ρ) (D : WDat l T)
    (N : ℕ) (hN : ((∑ j, wEv (l ^ f) j * (T j).d) + 1) ^ (∑ j, wEv (l ^ f) j * (T j).d) ≤ (l ^ f) ^ N)
    (A : Test l) (y : (PX (D.π ≫ q) κ).obj A.obj) {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : ∀ j, (T j).p ⁻¹ᵁ U ≤ (T j).r ⁻¹ᵁ V) (hy : ⊤ ≤ (y.1 ≫ D.π) ⁻¹ᵁ U)
    (hn : NormOn l (l ^ f) n (fn q ϖ) T U V h) :
    ∃ S : Fam A, IsDec S ∧ ∀ s,
      ∑ x : (Σ j : Fin (n + 1), Fin (T j).d), Finsupp.single
        ((pxMap (p := D.π ≫ q) κ (D.s x.1 x.2 ≫ (T x.1).r) (by rw [Category.assoc, hr, ← Category.assoc, D.hs]) ≫
          ρ ≫ itE F (n - x.1 + N)).app _ ((PX (D.π ≫ q) κ).map (S.f s).hom y))
        ((-1 : ℤ) ^ (x.1 : ℕ) * (((l ^ f) ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ)) = 0 ∨ Subsingleton (S.B s).obj.A := by
  obtain ⟨φ, hφ⟩ := wzPhi A.obj f
  obtain ⟨ψ, hψ⟩ := wzPsi A.obj m
  let y' : (PX q κ).obj A.obj := ⟨y.1 ≫ D.π, by rw [Category.assoc]; exact y.2⟩
  have hc : ∀ x : O, ψ (A.obj.oC (κ x)) = qs A.obj (g x) := by
    have h1 := (ρ.app A.obj y').2
    rw [hρ A.obj ψ hψ y', Category.assoc, y'.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
    have h2 := Spec.map_injective h1
    intro x
    exact RingHom.congr_fun (CommRingCat.hom_ext_iff.1 h2) x
  obtain ⟨α, hα, hnorm⟩ := UpperTheory.correspondence_norm_bound_of_affine_opens l q ϖ (l ^ f) n T κ D A y hU hV h hy hn ψ (by rw [hc, hg, map_zero])
  obtain ⟨k, x, hx⟩ := UpperTheory.exists_finite_sections_determining_ringHom_of_smooth q hq hV
  let u : ∀ j, Fin (T j).d → (PX (D.π ≫ q) κ ⟶ PQ q g) := fun j i =>
    pxMap (p := D.π ≫ q) κ (D.s j i ≫ (T j).r) (by rw [Category.assoc, hr, ← Category.assoc, D.hs]) ≫
          ρ ≫ itE F (n - j + N)
  have hv : ∀ j i, ((u j i).app A.obj y).1 = ptOf hV _ ((φ ^ (n - j + N)).comp (ψ.comp (α j i))) := fun j i => by
    let yy : (PX q κ).obj A.obj := (pxMap (p := D.π ≫ q) κ (D.s j i ≫ (T j).r)
      (by rw [Category.assoc, hr, ← Category.assoc, D.hs])).app A.obj y
    have e1 : (ρ.app A.obj yy).1 = ptOf hV _ (ψ.comp (α j i)) := by
      rw [hρ A.obj ψ hψ yy, ← ptOf_pre, ← hα]
      rfl
    exact wzFr hF A.obj φ hφ hV (ψ.comp (α j i)) (ρ.app A.obj yy) e1 _
  obtain ⟨S, hS, hs⟩ := wzCore f n q g hV (fun j => (T j).d) N hN A (fun j i => ψ.comp (α j i)) φ hφ
    (fun j i => (u j i).app A.obj y) hv x hx (hnorm _ x)
  refine ⟨S, hS, fun s => (hs s).imp (fun e => ?_) id⟩
  have nat : ∀ j i, (u j i).app (S.B s).obj ((PX (D.π ≫ q) κ).map (S.f s).hom y) =
      (PQ q g).map (S.f s).hom ((u j i).app A.obj y) :=
    fun j i => wzNat (u j i) (S.f s).hom y
  have e3 := wzSum (l ^ f) n (I := fun j => Fin (T j).d)
    (fun j i => (PQ q g).map (S.f s).hom ((u j i).app A.obj y)) e
  refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) e3
  exact congrArg (fun w => Finsupp.single w ((-1 : ℤ) ^ (x.1 : ℕ) * (((l ^ f) ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ))) (nat x.1 x.2)

theorem wZero : UpperTheory.Ru.crystallineComparison.WZero := by
  intro l _ f n O _ _ _ ϖ hϖ hl0 hlu Y q hq hqc hY hf T hr hpt κ g hg m F ρ hF hρ _ D
  have hl2 : 2 ≤ l ^ f := by
    have h2 := (Fact.out : l.Prime).two_le
    exact h2.trans (Nat.le_self_pow hf.ne' l)
  refine ⟨((∑ j, wEv (l ^ f) j * (T j).d) + 1) ^ (∑ j, wEv (l ^ f) j * (T j).d), ?_⟩
  intro A y
  obtain ⟨S, hS, hch⟩ := wzChart hY T A (y.1 ≫ D.π)
  choose U V hU hV h hy using hch
  have hpar := fun s => wzLocal f n q hq ϖ T hr κ g hg m F ρ hF hρ D _ (Nat.lt_pow_self (by omega)).le (S.B s)
    ((PX (D.π ≫ q) κ).map (S.f s).hom y) (hU s) (hV s) (h s)
    (by
      have e : ((PX (D.π ≫ q) κ).map (S.f s).hom y).1 ≫ D.π =
          Spec.map (CommRingCat.ofHom (PAlg.mapU (S.f s).hom)) ≫ y.1 ≫ D.π := Category.assoc _ _ _
      rw [e]; exact hy s) (normOfPt' l f n (Fact.out) O ϖ hϖ hl0 hlu Y q hq T hpt _ _ (hU s) (hV s) (h s))
  choose R hR hz using hpar
  obtain ⟨Pa, hPa⟩ := partsEx l
  have hd := (hPa A _).1 (Pa.trans S R ((hPa A S).2 hS) fun s => (hPa _ _).2 (hR s))
  refine ⟨_, hd, ?_⟩
  rintro ⟨s, t⟩
  have e := hz s t
  have e2 : (PX (D.π ≫ q) κ).map (S.f s ≫ (R s).f t).hom y =
      (PX (D.π ≫ q) κ).map ((R s).f t).hom ((PX (D.π ≫ q) κ).map (S.f s).hom y) :=
    Functor.map_comp_apply _ _ _ _
  change (∑ i, _) = 0 ∨ _
  simp only [e2]
  exact e

end UpperTheory.Ru.crystallineComparison
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AveragingTransferKills
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumTransport
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

private lemma sec_nat {P : C ⥤ Type} {K : Coef C} (c : Sec P K) {A B : C} (φ : A ⟶ B)
    (y : P.obj A) : (K.map φ).hom (c.1 A y) = c.1 B (P.map φ y) :=
  c.2 φ y

private lemma sum_transport {Q : C ⥤ Type} {K : Coef C} (c : Sec Q K) {I : Type} [Fintype I]
    (g : I → (Q ⟶ Q)) {A B : C} (φ : A ⟶ B) (w : Q.obj A) :
    (K.map φ).hom (∑ i, c.1 A ((g i).app A w)) =
      ((Finset.univ.val.map fun i => (g i).app B (Q.map φ w)).map (c.1 B)).sum := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Multiset.map_map]
  change _ = ∑ i, c.1 B ((g i).app B (Q.map φ w))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sec_nat c φ, ← NatTrans.naturality_apply (g i) φ]

private lemma avg_indep (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) {A : C}
    {w w' : Q.obj A} (hw : p.app A w = p.app A w') :
    ∑ i, c.1 A ((g i).app A w) = ∑ i, c.1 A ((g i).app A w') := by
  obtain ⟨S, hS, hm⟩ := h.2.2 A w w' hw
  apply (hK A S hS).1
  funext s
  change (K.map (S.f s)).hom _ = (K.map (S.f s)).hom _
  rw [sum_transport, sum_transport, hm s]

private def lift (Pa : Parts C) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (A : C) (y : P.obj A) : Q.obj A :=
  Classical.choose ((show ∀ A, Function.Surjective (p.app A) from h.2.1) A y)

private lemma lift_spec (Pa : Parts C) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (A : C) (y : P.obj A) :
    p.app A (lift Pa h A y) = y :=
  Classical.choose_spec ((show ∀ A, Function.Surjective (p.app A) from h.2.1) A y)

private def avg (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) : Sec P K :=
  ⟨fun A y => ∑ i, c.1 A ((g i).app A (lift Pa h A y)), by
    intro A B φ y
    have hw : p.app B (Q.map φ (lift Pa h A y)) = p.app B (lift Pa h B (P.map φ y)) := by
      rw [lift_spec, NatTrans.naturality_apply p φ, lift_spec]
    change (K.map φ).hom (∑ i, c.1 A ((g i).app A (lift Pa h A y))) =
      ∑ i, c.1 B ((g i).app B (lift Pa h B (P.map φ y)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← avg_indep Pa hK h c hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_nat c φ, ← NatTrans.naturality_apply (g i) φ]⟩

private lemma avg_apply (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) (A : C)
    (y : P.obj A) :
    (avg Pa hK h c).1 A y = ∑ i, c.1 A ((g i).app A (lift Pa h A y)) := rfl

private lemma avg_pull (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (s : Sec P K) (c : Sec Q K)
    (hc : ∀ (A : C) (q : Q.obj A), c.1 A q = s.1 A (p.app A q)) :
    avg Pa hK h c = Fintype.card I • s := by
  apply Subtype.ext
  funext A y
  have hg : ∀ (i : I) (w : Q.obj A), p.app A ((g i).app A w) = p.app A w := fun i w => by
    have hgi : g i ≫ p = p := (show ∀ i, g i ≫ p = p from h.1) i
    have : (g i ≫ p).app A w = p.app A w := by rw [hgi]
    exact this
  rw [avg_apply]
  simp only [hc, hg, lift_spec]
  simp

private lemma avg_map (Pa : Parts C) {K L : Coef C} (hK : Pa.Add K) (hL : Pa.Add L)
    {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g)
    (α : K ⟶ L) (c : Sec Q K) (c' : Sec Q L)
    (hc : ∀ (A : C) (q : Q.obj A), c'.1 A q = (α.app A).hom (c.1 A q)) (A : C) (y : P.obj A) :
    (avg Pa hL h c').1 A y = (α.app A).hom ((avg Pa hK h c).1 A y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_apply, avg_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => hc _ _

private lemma zero_case (Pa : Parts C) (T : Theory C) {K L : Coef C} (hK : Pa.Add K)
    (hL : Pa.Add L) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I] {g : I → (Q ⟶ Q)}
    (h : Pa.LocTrans p g) (π : K ⟶ L) (x' : T.H P L 0) (k : T.H Q K 0)
    (hk : T.map Q π 0 k = T.pull p L 0 x') :
    Fintype.card I • x' ∈ Set.range (T.map P π 0) := by
  refine ⟨(T.zero P K).symm (avg Pa hK h (T.zero Q K k)), ?_⟩
  apply (T.zero P L).injective
  apply Subtype.ext
  funext A y
  have e1 : avg Pa hL h (T.zero Q L (T.pull p L 0 x')) = Fintype.card I • T.zero P L x' :=
    avg_pull Pa hL h _ _ fun A q => T.zero_pull p L x' A q
  have e2 := avg_map Pa hK hL h π (T.zero Q K k) (T.zero Q L (T.map Q π 0 k))
    (fun A q => T.zero_map Q π k A q) A y
  rw [T.zero_map, map_nsmul, ← e1, ← hk, e2, AddEquiv.apply_symm_apply]

private lemma step (Pa : Parts C) (T : Theory C) {Q P : C ⥤ Type} (p : Q ⟶ P) (n : ℕ)
    (S : ShortComplex (Coef C)) (hS : S.ShortExact) (hK : Injective S.X₂) (j : ℕ)
    (hr : ∀ (x' : T.H P S.X₃ j) (k : T.H Q S.X₂ j), T.map Q S.g j k = T.pull p S.X₃ j x' →
      n • x' ∈ Set.range (T.map P S.g j))
    (x : T.H P S.X₁ (j + 1)) (hx : T.pull p S.X₁ (j + 1) x = 0) : n • x = 0 := by
  have h0 : T.map P S.f (j + 1) x = 0 := (T.inj P S.X₂ hK j).elim _ _
  obtain ⟨x', rfl⟩ := (T.ex₁ P S hS j x).1 h0
  have hpull : T.δ Q S hS j (T.pull p S.X₃ j x') = 0 := by
    rw [← T.pull_δ]
    exact hx
  obtain ⟨k, hk⟩ := (T.ex₃ Q S hS j _).1 hpull
  obtain ⟨k', hk'⟩ := hr x' k hk
  rw [← map_nsmul, ← hk']
  exact (T.ex₃ P S hS j _).2 ⟨k', rfl⟩

end UpperTheory.Ru.crystallineComparison

open CategoryTheory CategoryTheory.Limits UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.locAvg :
    UpperTheory.Ru.crystallineComparison.LocAvg := by
  intro C _ Pa T F hF Q P p I _ g h j
  induction j generalizing F with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by
      apply (T.zero P F).injective
      rw [map_zero]
      apply Subtype.ext
      funext A y
      obtain ⟨w, rfl⟩ := h.2.1 A y
      rw [← T.zero_pull p F x A w, hx, map_zero]
      rfl
    rw [hx0, smul_zero]
  | succ j ih =>
    intro x hx
    obtain ⟨K, ι, hm, hi, hK⟩ := emb C Pa F hF
    have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
      { exact := ShortComplex.exact_cokernel ι, mono_f := hm, epi_g := inferInstance }
    have hL : Pa.Add (cokernel ι) := quotAdd C Pa _ hS hF hK
    refine step Pa T p _ _ hS hi j ?_ x hx
    intro x' k hk
    cases j with
    | zero =>
      exact zero_case Pa T hK hL h _ x' k hk
    | succ j =>
      have hk0 : k = 0 := (T.inj Q K hi j).elim _ _
      rw [hk0, map_zero] at hk
      exact ⟨0, by rw [map_zero, ih _ hL x' hk.symm]⟩
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private abbrev coefT (l : ℕ) [Fact l.Prime] (n : ℕ) : Test l ⥤ ModuleCat.{0} (Acris l) :=
  CH.modF (testι l ⋙ AcrA l n)

private lemma add_gen {C : Type 1} [Category.{0} C] (Pa : Parts C) {R : Type} [CommRing R]
    (F : C ⥤ ModuleCat.{0} R)
    (hF : ∀ (A : C) (S : Fam A), Pa.Cov S →
      Function.Bijective fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x)
    (F' : Coef C) (c : ∀ A, F.obj A ≃+ F'.obj A)
    (hc : ∀ {A B : C} (φ : A ⟶ B) (x : F.obj A), c B ((F.map φ).hom x) = (F'.map φ).hom (c A x)) :
    Pa.Add F' := by
  intro A S hS
  have e : (fun (x : F'.obj A) (i : S.ι) => (F'.map (S.f i)).hom x) =
      (fun (v : ∀ i, F.obj (S.B i)) (i : S.ι) => c (S.B i) (v i)) ∘
        (fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x) ∘ (c A).symm := by
    funext x i
    have := hc (S.f i) ((c A).symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e]
  exact (Equiv.piCongrRight fun i => (c (S.B i)).toEquiv).bijective.comp
    ((hF A S hS).comp (c A).symm.bijective)

private lemma coefT_add (hA : AcrAdd) (Pa : Parts (Test l))
    (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S) (n : ℕ) (A : Test l) (S : Fam A)
    (hS : Pa.Cov S) :
    Function.Bijective fun (x : (coefT l n).obj A) (i : S.ι) => ((coefT l n).map (S.f i)).hom x :=
  hA l n A S ((hPa A S).1 hS)

private lemma avg_gen (hLA : LocAvg) {C : Type 1} [Category.{0} C] (Pa : Parts C) (T : Theory C)
    {R : Type} [CommRing R] (F : C ⥤ ModuleCat.{0} R) (F' : Coef C) (hF : Pa.Add F')
    (e : ∀ (P : C ⥤ Type) (j : ℕ), CH.H (CategoryOfElements.π P ⋙ F) j ≃+ T.H P F' j)
    {Q P : C ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (hL : Pa.LocTrans p g)
    (m : CH.Mor (CategoryOfElements.π P ⋙ F) (CategoryOfElements.π Q ⋙ F) (RingHom.id R)) (j : ℕ)
    (hm : ∀ x, e Q j (m.pull j x) = T.pull p F' j (e P j x))
    (x : CH.H (CategoryOfElements.π P ⋙ F) j) (hx : m.pull j x = 0) : Fintype.card I • x = 0 := by
  have h0 : T.pull p F' j (e P j x) = 0 := by
    simpa only [hx, AddEquiv.map_zero] using (hm x).symm
  apply (e P j).injective
  change (e P j).toAddMonoidHom (Fintype.card I • x) = (e P j).toAddMonoidHom 0
  rw [map_nsmul, map_zero]
  exact hLA C Pa T F' hF Q P p I g hL j _ h0

private def pullT {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) (n : ℕ) :
    CH.Mor (CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n)
      (CategoryOfElements.π (testι l ⋙ Q) ⋙ coefT l n) (RingHom.id _) := pullMor p n

private lemma locTrans_of {Q P : PAlg l ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : TTrans p g) (Pa : Parts (Test l))
    (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S) :
    Pa.LocTrans (Functor.whiskerLeft (testι l) p)
      (fun i => Functor.whiskerLeft (testι l) (g i)) := by
  refine ⟨fun i => ?_, fun A => h.2.1 A, fun A y y' hy => ?_⟩
  · rw [← Functor.whiskerLeft_comp, h.1 i]
  · obtain ⟨S, hS, hm⟩ := h.2.2 A y y' hy
    exact ⟨S, (hPa A S).2 hS, hm⟩

private lemma averaging_transfer_kills (hLA : LocAvg) (hP : PartsEx) (hA : AcrAdd) (hT : TheoryEx)
    {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : TTrans p g)
    (n j : ℕ) (x : CH.H (CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n) j)
    (hx : (pullT p n).pull j x = 0) : Fintype.card I • x = 0 := by
  refine Exists.elim (hP l) fun Pa hPa => Exists.elim (hT (Test l)) fun T hT => ?_
  refine Exists.elim (hT (Acris l) (coefT l n)) fun F' h1 => Exists.elim h1 fun c h2 =>
    Exists.elim h2 fun e h3 => ?_
  have hF : Pa.Add F' := add_gen Pa (coefT l n) (coefT_add hA Pa hPa n) F' c h3.1
  have hG : (pullT p n).G = CategoryOfElements.map (Functor.whiskerLeft (testι l) p) := rfl
  have hτ : ∀ (T : (testι l ⋙ Q).Elements) (y : ((CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n).obj ((pullT p n).G.obj T))),
      HEq ((pullT p n).τ T y) y := fun _ _ => HEq.rfl
  have hm := h3.2 (Functor.whiskerLeft (testι l) p) (pullT p n) hG hτ j
  have hL := locTrans_of h Pa hPa
  exact avg_gen hLA Pa T (coefT l n) F' hF e (Functor.whiskerLeft (testι l) p) hL (pullT p n) j hm x hx

end UpperTheory.Ru.crystallineComparison

open CategoryTheory CategoryTheory.Limits GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.avgMH :
    UpperTheory.Ru.crystallineComparison.AvgMH := by
  intro l _ Q P p I _ g h n j x hx
  exact averaging_transfer_kills locAvg partsEx acrAdd theoryEx p h n j x hx
end
end

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

private theorem phiTL {l : ℕ} [Fact l.Prime] : phiA l (tA l) = (l : Acris l) * tA l := ACris.phi_periodT_eq_mul _

private lemma eqAbs {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (Φ : H → H) (ph : A → A)
    (hs : ∀ c x, Φ (c • x) = ph c • Φ x) {c1 c2 c1' c2' : A} {E E' Y Y' : H} (hX : c1 • E = c2 • Y)
    (h1 : ph c1 = c1') (h2 : ph c2 = c2') (hE : Φ E = E') (hY : Φ Y = Y') : c1' • E' = c2' • Y' := by
  subst h1 h2 hE hY
  rw [← hs, ← hs, hX]

private lemma scaleAbs {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (d : A) {c1 c2 c1' c2' : A} {E Y : H}
    (h1 : c1' = d * c1) (h2 : c2' = d * c2) (h : c1 • E = c2 • Y) : c1' • E = c2' • Y := by
  rw [h1, h2, mul_smul, mul_smul, h]

private lemma phi_iter_l {l : ℕ} [Fact l.Prime] (m : ℕ) : (phiA l)^[m] (l : Acris l) = (l : Acris l) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_natCast]

private lemma phiA_iterate_tA_of_prime {l : ℕ} [Fact l.Prime] (m : ℕ) : (phiA l)^[m] (tA l) = (l : Acris l) ^ m * tA l := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, phiTL]
    ring

private lemma phiH_iter_smul {l : ℕ} [Fact l.Prime] (P : PAlg l ⥤ Type) (n j m : ℕ) (c : Acris l) (x : MH P n j) :
    (phiH P n j)^[m] (c • x) = ((phiA l)^[m] c) • (phiH P n j)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : (phiH P n j)^[m + 1] (c • x) = phiH P n j ((phiH P n j)^[m] (c • x)) := Function.iterate_succ_apply' _ _ _
    have h2 : (phiH P n j)^[m + 1] x = phiH P n j ((phiH P n j)^[m] x) := Function.iterate_succ_apply' _ _ _
    have h3 : (phiA l)^[m + 1] c = phiA l ((phiA l)^[m] c) := Function.iterate_succ_apply' _ _ _
    refine h1.trans ((congrArg (phiH P n j) ih).trans ?_)
    refine (((phiMor P n).pull j).map_smulₛₗ _ _).trans ?_
    exact (congrArg₂ (· • ·) h3 h2).symm

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private lemma phiH_evE {e : E.EtFam l K} (he : e.Good) (M : Model l K) (j lev : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j)
    (c : ι → Acris l) (m : ℕ) :
    (phiH M.P lev j)^[m] (evE e M j lev v c) = evE e M j lev v (fun k => (phiA l)^[m] (c k)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [evE, Function.iterate_succ_apply']
    refine (map_sum ((phiMor M.P lev).pull j) _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
    refine (((phiMor M.P lev).pull j).map_smulₛₗ _ _).trans ?_
    exact congrArg (_ • ·) (he.phi M lev j _)

private lemma eqI {e : E.EtFam l K} (he : e.Good) (M : Model l K) (j lev : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j)
    (c c' : ι → Acris l) (Y : M.MH lev j) (a u r m d M0 : ℕ) (hM : m + d = M0)
    (hc : (fun k => (phiA l)^[m] (c k)) = c')
    (hX : ((l : Acris l) ^ a * tA l ^ u) • evE e M j lev v c = tA l ^ (u + r) • Y) :
    (((l : Acris l) ^ (a + M0 * u) * tA l ^ u) * (l : Acris l) ^ (d * r)) • evE e M j lev v c' =
      ((l : Acris l) ^ (M0 * (u + r)) * tA l ^ (u + r)) • (phiH M.P lev j)^[m] Y := by
  subst hM hc
  have c1 : (phiA l)^[m] ((l : Acris l) ^ a * tA l ^ u) = (l : Acris l) ^ a * ((l : Acris l) ^ m * tA l) ^ u := by
    rw [iterate_map_mul (phiA l), iterate_map_pow (phiA l), iterate_map_pow (phiA l), phi_iter_l, phiA_iterate_tA_of_prime]
  have c2 : (phiA l)^[m] (tA l ^ (u + r)) = ((l : Acris l) ^ m * tA l) ^ (u + r) := by
    rw [iterate_map_pow (phiA l), phiA_iterate_tA_of_prime]
  have q1 : ((l : Acris l) ^ (a + (m + d) * u) * tA l ^ u) * (l : Acris l) ^ (d * r) =
      (l : Acris l) ^ (d * (u + r)) * ((l : Acris l) ^ a * ((l : Acris l) ^ m * tA l) ^ u) := by ring
  have q2 : (l : Acris l) ^ ((m + d) * (u + r)) * tA l ^ (u + r) =
      (l : Acris l) ^ (d * (u + r)) * ((l : Acris l) ^ m * tA l) ^ (u + r) := by ring
  exact scaleAbs (H := MH M.P lev j) _ q1 q2
    (eqAbs (H := MH M.P lev j) _ _ (phiH_iter_smul M.P lev j m) hX c1 c2 (phiH_evE he M j lev v c m) rfl)

private def eLev (e : E.EtFam l K) (M : Model l K) (j lev : ℕ) : M.T j →+ M.MH lev j :=
  AddMonoidHom.mk' (fun x => e M lev j (x.lev lev)) fun x y => map_add (e M lev j) (x.lev lev) (y.lev lev)

private lemma natS {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (n b : ℕ) (x : H) :
    (n ^ b : ℕ) • x = ((n : A) ^ b) • x := by
  rw [← Nat.cast_smul_eq_nsmul A]
  push_cast
  rfl

private lemma h1A {A : Type} [CommRing A] {TW H : Type 1} [AddCommGroup TW] [AddCommGroup H] [Module A H] (Ψ : TW →+ H)
    {d l s b : ℕ} (p : TW) (q : Fin d → TW) (p' : H) (q' : Fin d → H)
    (h : (l ^ b : ℕ) • p = (l ^ (s + b) : ℕ) • ∑ a, q a) (hp : Ψ p = p') (hq : ∀ a, Ψ (q a) = q' a) :
    ((l : A) ^ b) • p' = ((l : A) ^ (s + b)) • ∑ a, q' a := by
  have h' := congrArg Ψ h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_nsmul, map_nsmul, map_sum, hp] at h'
  simp only [hq] at h'
  rw [natS (A := A), natS (A := A)] at h'
  exact h'

private lemma natE {e : E.EtFam l K} (he : e.Good) (W M : Model l K) (u : W.X ⟶ M.X) (hu : u ≫ M.p = W.p) (j lev : ℕ) (y : M.T j) :
    eLev e W j lev (Model.pullT u hu j y) = pullH (pxMap (okToOC l K) u hu) lev j (e M lev j (y.lev lev)) :=
  he.nat W M u hu lev j (y.lev lev)

private lemma h1L {e : E.EtFam l K} (he : e.Good) (W M : Model l K) (π : W.X ⟶ M.X) (hπ : π ≫ M.p = W.p) (j lev s b : ℕ)
    {d : ℕ} (τ : Fin d → (W.X ⟶ M.X)) (hτ : ∀ a, τ a ≫ M.p = W.p) (w y : M.T j)
    (h : (l ^ b : ℕ) • Model.pullT π hπ j w = (l ^ (s + b) : ℕ) • ∑ a, Model.pullT (τ a) (hτ a) j y) :
    ((l : Acris l) ^ b) • pullH (pxMap (okToOC l K) π hπ) lev j (e M lev j (w.lev lev)) =
      ((l : Acris l) ^ (s + b)) • ∑ a, pullH (pxMap (okToOC l K) (τ a) (hτ a)) lev j (e M lev j (y.lev lev)) := by
  exact h1A (A := Acris l) (H := MH W.P lev j) (eLev e W j lev) _ _ _ _ h (natE he W M π hπ j lev w)
    fun a => natE he W M (τ a) (hτ a) j lev y

private lemma finA {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] {Q : Type} [Fintype Q] (C : ℕ)
    (Ev : Q → H) (c : Q → A) (L tt κ : A) (hk : tt * κ = (C : A) * L)
    (h : C • (L • ∑ q, c q • Ev q) = 0) : tt • ∑ q, (κ * c q) • Ev q = 0 := by
  have e1 : ∑ q, (κ * c q) • Ev q = κ • ∑ q, c q • Ev q := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => mul_smul _ _ _
  rw [e1, smul_smul, hk, mul_smul, Nat.cast_smul_eq_nsmul]
  exact h

set_option maxHeartbeats 4000000 in
private lemma levZero {e : E.EtFam l K} (he : e.Good) (M W : Model l K) (π : W.X ⟶ M.X) (hπ : π ≫ M.p = W.p)
    (j n f N0 N1 r s b a u C : ℕ) {d : Fin (n + 1) → ℕ} (τ : ∀ i, Fin (d i) → (W.X ⟶ M.X)) (hτ : ∀ i x, τ i x ≫ M.p = W.p)
    {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (w : Fin (n + 1) → ι → M.T j) (σ : Fin (n + 1) → ℤ)
    (Y : ∀ lev, MH M.P lev j)
    (hAvg : ∀ lev (x : MH M.P lev j), pullH (pxMap (okToOC l K) π hπ) lev j x = 0 → C • x = 0)
    (h3 : ∀ lev, ∑ x : Σ i, Fin (d i), σ x.1 • pullH (pxMap (okToOC l K) (τ x.1 x.2) (hτ x.1 x.2)) lev j
      ((phiH M.P lev j)^[f * (n - x.1 + N0)] (Y lev)) = 0)
    (hX : ∀ lev, ((l : Acris l) ^ a * tA l ^ u) • evE e M j lev v (fun k => (phiA l)^[f * N1] (c k)) = tA l ^ (u + r) • Y lev)
    (hw2 : ∀ i k, (l ^ b : ℕ) • Model.pullT π hπ j (w i k) = (l ^ (s + b) : ℕ) • ∑ x, Model.pullT (τ i x) (hτ i x) j (v k))
    (lev : ℕ) :
    tA l ^ u • evE e M j lev (fun q : Fin (n + 1) × ι => w q.1 q.2)
      (fun q => ((C * l ^ (a + f * (n + N0) * u) * l ^ b : ℕ) : Acris l) *
        (((σ q.1 : ℤ) : Acris l) * (l : Acris l) ^ (f * (q.1 : ℕ) * r) * (phiA l)^[f * (n - q.1 + (N0 + N1))] (c q.2))) = 0 := by
  have h2 : ∀ i : Fin (n + 1), (((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u) * (l : Acris l) ^ (f * (i : ℕ) * r)) •
      evE e M j lev v (fun k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) =
      ((l : Acris l) ^ (f * (n + N0) * (u + r)) * tA l ^ (u + r)) • (phiH M.P lev j)^[f * (n - i + N0)] (Y lev) := by
    intro i
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
    have hM : f * (n - i + N0) + f * i = f * (n + N0) := by
      rw [← mul_add]
      congr 1
      omega
    have hI : (fun k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) = fun k => (phiA l)^[f * (n - i + N0)] ((phiA l)^[f * N1] (c k)) := by
      funext k
      rw [← Function.iterate_add_apply]
      congr 1
      ring
    exact eqI he M j lev v (fun k => (phiA l)^[f * N1] (c k)) _ (Y lev) a u r (f * (n - i + N0)) (f * i) _ hM hI.symm (hX lev)
  have S := UpperTheory.linear_combination_transfer_of_projector_relations (A := Acris l) (H := MH M.P lev j) (H' := MH W.P lev j) (J := Fin (n + 1)) (ι := ι) (I := fun i => Fin (d i))
    (pullH (pxMap (okToOC l K) π hπ) lev j) (fun i x => pullH (pxMap (okToOC l K) (τ i x) (hτ i x)) lev j)
    (fun k => e M lev j ((v k).lev lev)) (fun i k => e M lev j ((w i k).lev lev))
    ((l : Acris l) ^ b) ((l : Acris l) ^ (s + b)) ((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u)
    ((l : Acris l) ^ (f * (n + N0) * (u + r)) * tA l ^ (u + r)) σ (fun i => (l : Acris l) ^ (f * (i : ℕ) * r))
    (fun i k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) (fun i => (phiH M.P lev j)^[f * (n - i + N0)] (Y lev))
    (fun i k => h1L he W M π hπ j lev s b (τ i) (hτ i) (w i k) (v k) (hw2 i k)) h2 (h3 lev)
  rw [← map_smul] at S
  have A1 := hAvg lev _ S
  refine finA (A := Acris l) (H := MH M.P lev j) C (fun q : Fin (n + 1) × ι => e M lev j ((w q.1 q.2).lev lev)) _
    (((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u) * (l : Acris l) ^ b) _ _ ?_ A1
  push_cast
  ring

end UpperTheory.Ru.crystallineComparison

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison in
set_option maxHeartbeats 4000000 in
theorem UpperTheory.Ru.crystallineComparison.top : UpperTheory.Ru.crystallineComparison.Top := by
  intro l _ K _ _ ϖ hϖ e he M hsm hqc haff f n j hf T hr hPt A hA B hInj hAbs
  obtain ⟨m, N1, g, F, ρ, hg0, hgf, hF, hρ, hAI⟩ := hAbs
  obtain ⟨D⟩ := wEx l M.X (Fin (n + 1)) T
  obtain ⟨N0, hZ⟩ := wZero l f n (OK l K) ϖ hϖ UpperTheory.natCast_prime_ne_zero_and_not_isUnit_integers.1 UpperTheory.natCast_prime_ne_zero_and_not_isUnit_integers.2 M.X M.p hsm hqc haff hf T hr hPt (okToOC l K) g hg0 m F ρ hF hρ hgf D
  obtain ⟨gp, hgp⟩ := wTrans l (OK l K) M.X M.p (okToOC l K) (Fin (n + 1)) T D
  refine ⟨N0 + N1, fun x hx => ?_⟩
  obtain ⟨ι, _, v, c, r, rfl⟩ := UpperTheory.exists_crystalline_lattice_expansion B M j x
  obtain ⟨a, u, X, hX⟩ := hAI ι v c r hx
  obtain ⟨s, b, w, hw1, hw2⟩ := UpperTheory.hecke_correspondence_product M ⟨D.W, D.π ≫ M.p⟩ D.π rfl j n T hr A hA D.s D.hs (fun i X y hy => D.gen X y hy i) v
  let σ : Fin (n + 1) → ℤ := fun i => (-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)
  have ha : (fun x : (Σ j : Fin (n + 1), Fin (T j).d) => (-1 : ℤ) ^ (x.1 : ℕ) * (((l ^ f) ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ)) = fun x => σ x.1 := by
    funext x
    simp only [σ]
    push_cast
    rfl
  rw [ha] at hZ
  have hS := siteAnn l (OK l K) M.X M.p g (PX (D.π ≫ M.p) (okToOC l K)) M.P ρ F f (Σ j : Fin (n + 1), Fin (T j).d) (fun x => σ x.1)
    (fun x => pxMap (okToOC l K) (D.s x.1 x.2 ≫ (T x.1).r) (by rw [Category.assoc, hr, ← Category.assoc, D.hs]))
    (fun x => n - x.1 + N0) hZ
  have hV := levZero he M ⟨D.W, D.π ≫ M.p⟩ D.π rfl j n f N0 N1 r s b a u (Fintype.card (∀ i, Equiv.Perm (Fin (T i).d)))
    (d := fun i => (T i).d) (fun i x => D.s i x ≫ (T i).r) (fun i x => by
      change (D.s i x ≫ (T i).r) ≫ M.p = D.π ≫ M.p
      rw [Category.assoc, hr, ← Category.assoc, D.hs]) v c w σ
    (fun lev => pullH ρ lev j (X lev))
    (fun lev y hy => avgMH l _ _ _ _ _ hgp lev j y hy)
    (fun lev => hS lev j (X lev) (hX lev).1) (fun lev => (hX lev).2) hw2
  have h0 := hInj (Fin (n + 1) × ι) (fun q => w q.1 q.2) _ u hV
  have hκ : Fintype.card (∀ i, Equiv.Perm (Fin (T i).d)) * l ^ (a + f * (n + N0) * u) * l ^ b ≠ 0 :=
    mul_ne_zero (mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  exact UpperTheory.crystalline_expansion_relation_of_scaled_endomorphisms B M j f n (N0 + N1) r s _ hκ A v c w σ hw1 h0
end
end

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

private theorem UpperTheory.Ru.crystallineComparison.quasiCompact_of_proj {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f) : QuasiCompact f := by
  refine Exists.elim h fun N hN => Exists.elim hN fun i hi => ?_
  have : IsProper (ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  have : IsClosedImmersion i := hi.1
  rw [← hi.2]
  infer_instance

theorem UpperTheory.Ru.crystallineComparison.final :
    UpperTheory.Ru.crystallineComparison.Final := by
  unfold UpperTheory.Ru.crystallineComparison.Final
  intro l _ K _ _ _ r f hf hx hC ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨Amp, N, F, hFacts, hEt, hLaws, ⟨bm⟩, ⟨pm⟩, hfN, hTeich, hall⟩ := hC
  refine Exists.elim (CrystallineSemistableComparison.E.etMap l K) fun e he => ?_
  refine Exists.elim (UpperTheory.Ru.crystallineComparison.ePin l K Model.Sm Amp e he) fun e' hcomp => ?_
  refine Exists.elim (UpperTheory.Ru.crystallineComparison.pbIota l K B₀) fun ι hι' => ?_
  have hInj : InjE B₀ e M j :=
    UpperTheory.Ru.crystallineComparison.injOf l K B₀ ι hι'.1 hι'.2.1 hι'.2.2.1 Model.Sm Amp hFacts hEt hLaws e e' bm pm hcomp M hM j
  have hAbs : AbsInv B₀ e M j f ϖ :=
    UpperTheory.Ru.crystallineComparison.absInvOf l K r B₀ (UpperTheory.Ru.crystallineComparison.pbInv l K B₀ r) e he M hM f N j hx hfN hTeich F
      (hall M hM j).1 (hall M hM j).2 ϖ hϖ.not_isUnit
  have hP : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.p := hM.1.1
  have hSm : Smooth M.p := hM.2
  have hQC : QuasiCompact M.p := UpperTheory.Ru.crystallineComparison.quasiCompact_of_proj hP
  have hAff : UpperTheory.Gal.crystallineComparison.AffFin M.X := UpperTheory.Gal.crystallineComparison.affFin_of (OK l K) M.X M.p hP
  exact UpperTheory.Ru.crystallineComparison.top l K ϖ hϖ e he M hSm hQC hAff f n j hf T hr hPt A hA B₀ hInj hAbs
end

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.finAll_of :
    (∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (r : Res l K) (f : ℕ), 0 < f → CIn l K r f) → UpperTheory.Gal.crystallineComparison.Br.FinAll := by
  intro h l _ K _ _ _ f hf hc ϖ hϖ M hM n j T hr hPt A hA B₀
  obtain ⟨r⟩ := UpperTheory.Gal.CD.resEx l K
  have hx : ∀ x : r.k, x ^ l ^ f = x := by
    have hker : RingHom.ker r.ρ = IsLocalRing.maximalIdeal (OK l K) := by
      have hm : (RingHom.ker r.ρ).IsMaximal := RingHom.ker_isMaximal_of_surjective r.ρ r.surj
      exact IsLocalRing.eq_maximalIdeal hm
    have e : IsLocalRing.ResidueField (OK l K) ≃+* r.k :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective r.surj)
    have hcard : Nat.card r.k = l ^ f := by
      rw [← Nat.card_congr e.toEquiv]
      exact hc
    have hfin : Finite r.k :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    have := Fintype.ofFinite r.k
    intro x
    rw [← hcard, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  exact UpperTheory.Ru.crystallineComparison.final l K r f hf hx (h l K r f hf) ϖ hϖ M hM n j T hr hPt A hA B₀
end

namespace UpperTheory.Ru.crystallineComparison

theorem finAll : UpperTheory.Gal.crystallineComparison.Br.FinAll := finAll_of fun l _ K _ r f hf => cIn l K r f hf

theorem smoothModel_crystalline : CrystallineSemistableComparison.SmoothModelCrystalline := (CrystallineSemistableComparison.cstSmooth_of_side fun l _ K _ => UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K).1

theorem phiStep : UpperTheory.Gal.Int.Geo.PhiStep := phiStep_of (UpperTheory.Gal.Int.Geo.geoSide_of finAll smoothModel_crystalline)

end UpperTheory.Ru.crystallineComparison
