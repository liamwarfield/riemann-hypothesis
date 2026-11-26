module

public import ReciprocityTheory.DualLattices.HasLenCokerDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CoeffLgPcurveTop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.GeomSumRoot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvalues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
noncomputable section

open WittVector Ideal

namespace GlobalTheory.AinfXi

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem coeff_pow_pow_zero (x : PreTilt O p) (n : ℕ) :
    PreTilt.coeff n x ^ p ^ n = PreTilt.coeff 0 x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, PreTilt.coeff_pow_p, ih]

theorem isUnit_of_coeff_zero {x : PreTilt O p} (h : IsUnit (PreTilt.coeff 0 x)) : IsUnit x := by
  have hn : ∀ n, IsUnit (PreTilt.coeff n x) := fun n =>
    (isUnit_pow_iff (pow_ne_zero n hp.out.ne_zero)).1 (by rw [coeff_pow_pow_zero]; exact h)
  have hu : ∀ n, (hn (n + 1)).unit ^ p = (hn n).unit := fun n =>
    Units.ext (by simp [PreTilt.coeff_pow_p])
  let f : ℕ → ModP O p := fun n => (((hn n).unit⁻¹ : (ModP O p)ˣ) : ModP O p)
  have hf : ∀ n, f (n + 1) ^ p = f n := fun n => by
    simp only [f]
    rw [← Units.val_pow_eq_pow_val, inv_pow, hu]
  let y : PreTilt O p := (⟨f, hf⟩ : Perfection (ModP O p) p)
  refine isUnit_iff_exists_inv.2 ⟨y, ?_⟩
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n (x * y) = PreTilt.coeff n 1
  rw [map_mul, map_one]
  change PreTilt.coeff n x * f n = 1
  exact IsUnit.mul_val_inv (hn n)

end Tilt

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]

theorem witt_isUnit (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have hmem : c * teichmuller p ((u⁻¹ : Rˣ) : R) - 1 ∈ span {(p : WittVector p R)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      constantCoeff_apply (x := teichmuller p _), teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : WittVector p R)}) hmem
  have h1 := (mem_jacobson_bot.1 hj) 1
  rw [mul_one, sub_add_cancel] at h1
  exact isUnit_of_mul_isUnit_left h1

end Witt

section Main

open GlobalTheory.Sandwich

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem isDomain_ainf (hv : v.Integers O) : IsDomain (Ainf p O) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

theorem isLocalRing_preTilt (hv : v.Integers O) : IsLocalRing (PreTilt O p) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  haveI : Nontrivial (ModP O p) := ReciprocityTheory.PGsh.Ainf.quot_nontrivial _ (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (PreTilt.coeff 0 a) with h | h
  · exact Or.inl (isUnit_of_coeff_zero h)
  · exact Or.inr (isUnit_of_coeff_zero (by rwa [map_sub, map_one]))

theorem isLocalRing_ainf (hv : v.Integers O) : IsLocalRing (Ainf p O) := by
  haveI := isDomain_ainf (p := p) hv
  haveI := isLocalRing_preTilt (p := p) hv
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff a) with h | h
  · exact Or.inl (witt_isUnit a h)
  · exact Or.inr (witt_isUnit _ (by rwa [map_sub, map_one]))

variable (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (root ε).untilt p)
include hv hε

theorem ker_theta : RingHom.ker (fontaineTheta O p) = span {xi ε} :=
  ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε

theorem xi_nzd (y : Ainf p O) (hy : y * xi ε = 0) : y = 0 :=
  ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε y hy

theorem dvd_of_dvd_mul_p (N : ℕ) (z : Ainf p O) (h : xi ε ^ N ∣ z * p) : xi ε ^ N ∣ z := by
  induction N generalizing z with
  | zero => simp
  | succ N ih =>
    obtain ⟨w, hw⟩ := h
    have h1 : fontaineTheta O p (z * p) = 0 := by
      rw [hw, map_mul, map_pow,
        show fontaineTheta O p (xi ε) = 0 from ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε,
        zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [map_mul, map_natCast] at h1
    have h0 : fontaineTheta O p z = 0 :=
      ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by rw [pow_one]; exact h1)
    obtain ⟨z1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
    have h2 : (z1 * p - xi ε ^ N * w) * xi ε = 0 := by linear_combination hw
    obtain ⟨w', hw'⟩ := ih z1 ⟨w, sub_eq_zero.1 (xi_nzd hv ε hε _ h2)⟩
    exact ⟨w', by rw [hw']; ring⟩

theorem coeff_zero_eq_zero (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : constantCoeff x = 0 := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -, -⟩ := ReciprocityTheory.PGsh.a0 p C v O hv
  obtain ⟨u, hu⟩ := ((hX ε hv hε).2.2.2 pf hpf).2
  have hu' : xi ε = u * ((p : Ainf p O) - teichmuller p pf) := hu
  have hxi : constantCoeff (xi ε) = constantCoeff (u : Ainf p O) * (-pf) := by
    rw [hu', map_mul, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub,
      constantCoeff_apply (x := teichmuller p pf), teichmuller_coeff_zero]
  refine Perfection.ext fun n => ?_
  obtain ⟨w, hw⟩ := hx (p ^ n)
  change PreTilt.coeff n (constantCoeff x) = PreTilt.coeff n 0
  have h0 : PreTilt.coeff n (-pf) ^ p ^ n = 0 := by
    rw [coeff_pow_pow_zero, map_neg, ← PreTilt.mk_untilt_eq_coeff_zero, hpf, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  simp only [hw, hxi, map_mul, map_pow, mul_pow]
  rw [h0, mul_zero, zero_mul, map_zero]

theorem eq_zero_of_forall_dvd (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : x = 0 := by
  have key : ∀ k, ∀ x : Ainf p O, (∀ N, xi ε ^ N ∣ x) → (p : Ainf p O) ^ k ∣ x := by
    intro k
    induction k with
    | zero => intro x _; rw [pow_zero]; exact one_dvd _
    | succ k ih =>
      intro x hx
      have h0 := coeff_zero_eq_zero hv ε hε x hx
      rw [constantCoeff_apply] at h0
      obtain ⟨z, rfl⟩ := mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero x).2 h0)
      obtain ⟨w, hw⟩ := ih z fun N => dvd_of_dvd_mul_p hv ε hε N z (hx N)
      exact ⟨w, by rw [hw]; ring⟩
  ext n
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero x (n + 1)).1
    (mem_span_singleton.2 (key (n + 1) x hx)) n (Nat.lt_succ_self n)
  simpa using h

theorem exists_order (x : Ainf p O) (hx : x ≠ 0) :
    ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ fontaineTheta O p y ≠ 0 := by
  classical
  have hex : ∃ N, ¬ xi ε ^ N ∣ x := by
    by_contra h
    exact hx (eq_zero_of_forall_dvd hv ε hε x fun N => by_contra fun h' => h ⟨N, h'⟩)
  have hM := Nat.find_spec hex
  have hM0 : Nat.find hex ≠ 0 := fun h => hM (by rw [h, pow_zero]; exact one_dvd _)
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  obtain ⟨y, hy⟩ : xi ε ^ N ∣ x := not_not.1 (Nat.find_min hex (by omega))
  refine ⟨N, y, hy, fun h0 => hM ?_⟩
  obtain ⟨y1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
  rw [hN, Nat.succ_eq_add_one]
  exact ⟨y1, by rw [hy]; ring⟩

end Main

section Statement

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

theorem ainf_local_xi_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → IsDomain (Ainf p O) ∧ IsLocalRing (Ainf p O) ∧ RingHom.ker (WittVector.fontaineTheta O p) = Ideal.span {xi ε} ∧ Function.Surjective (WittVector.fontaineTheta O p) ∧ WittVector.fontaineTheta O p (nu ε) ≠ 0 ∧ xi ε ≠ 0 ∧ (∀ x : Ainf p O, x ≠ 0 → ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ WittVector.fontaineTheta O p y ≠ 0) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε
  haveI := isDomain_ainf (p := p) hv
  refine ⟨inferInstance, isLocalRing_ainf hv, ker_theta hv ε hε,
    ReciprocityTheory.PGsh.Ainf.theta_surj p O hv, ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε, fun h => ?_,
    fun x hx => exists_order hv ε hε x hx⟩
  exact one_ne_zero (xi_nzd hv ε hε 1 (by rw [h, mul_zero]))

end Statement

end GlobalTheory.AinfXi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → IsDomain (Ainf p O) ∧ IsLocalRing (Ainf p O) ∧ RingHom.ker (WittVector.fontaineTheta O p) = Ideal.span {xi ε} ∧ Function.Surjective (WittVector.fontaineTheta O p) ∧ WittVector.fontaineTheta O p (nu ε) ≠ 0 ∧ xi ε ≠ 0 ∧ (∀ x : Ainf p O, x ≠ 0 → ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ WittVector.fontaineTheta O p y ≠ 0) := by
  first | exact @GlobalTheory.AinfXi.ainf_local_xi_order | exact GlobalTheory.AinfXi.ainf_local_xi_order | (intros; apply GlobalTheory.AinfXi.ainf_local_xi_order <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheaf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheaf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.DiscChains

def heExt {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] {K L : ChainComplex C ℕ}
    (h : HomotopyEquiv K L) :
    HomotopyEquiv (K.extend ComplexShape.embeddingDownNat) (L.extend ComplexShape.embeddingDownNat) where
  hom := HomologicalComplex.extendMap h.hom _
  inv := HomologicalComplex.extendMap h.inv _
  homotopyHomInvId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyHomInvId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (HomologicalComplex.extendMap_comp _ _ _).symm).trans
    ((h.homotopyInvHomId.extend _).trans (Homotopy.ofEq (HomologicalComplex.extendMap_id _ _)))

variable (R : Type) [CommRing R]

def heN (P : PSh) :
    HomotopyEquiv ((chainsN R).obj (disc.obj P)) ((ChainComplex.single₀ (Shv R)).obj ((free R).obj P)) :=
  (HomotopyEquiv.ofIso ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).mapIso
      (Functor.constComp _ P (free R)))).trans
    (SimplicialObject.Augmented.ExtraDegeneracy.const ((free R).obj P)).homotopyEquiv

lemma heN_inv_f_zero (P : PSh) :
    (heN R P).inv.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom := by
  dsimp [heN, HomotopyEquiv.trans, HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv]
  erw [HomologicalComplex.comp_f]
  erw [ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  simp
  exact Category.comp_id _

def he (P : PSh) : HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)) :=
  (HomotopyEquiv.ofIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat ((free R).obj P) 0 0
      (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl)).symm).trans
    (heExt (heN R P)).symm

lemma he_hom_f_zero (P : PSh) : sglι _ ≫ (he R P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv := by
  dsimp [he, heExt, HomotopyEquiv.trans, HomotopyEquiv.symm, HomotopyEquiv.ofIso]
  erw [HomologicalComplex.comp_f, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = (0 : ℤ) from rfl), heN_inv_f_zero]
  rw [sglι, chainsXIso]
  erw [Category.assoc, Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.DiscChains

namespace GlobalTheory.EtC

theorem chains_disc_homotopyEquiv : ∀ (R : Type) [CommRing R] , ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)), (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧ ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) = (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom := by
  intro R _
  refine ⟨DiscChains.he R, DiscChains.he_hom_f_zero R, fun {P Q} f => ?_⟩
  obtain ⟨-, hnat, -⟩ := GlobalTheory.EtC.chains_basic R
  apply HomologicalComplex.from_single_hom_ext
  apply (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 ((free R).obj P)) _ _).1
  change sglι _ ≫ _ = sglι _ ≫ _
  have e1 : ((DiscChains.he R P).hom ≫ (chains R).map (disc.map f)).f 0 =
      (DiscChains.he R P).hom.f 0 ≫ ((chains R).map (disc.map f)).f 0 := HomologicalComplex.comp_f _ _ _
  have e2 : ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (DiscChains.he R Q).hom).f 0 =
      ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 ≫ (DiscChains.he R Q).hom.f 0 :=
    HomologicalComplex.comp_f _ _ _
  rw [e1, e2, ← Category.assoc, DiscChains.he_hom_f_zero]
  have h1 : sglι ((free R).obj P) ≫ ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f)).f 0 =
      (free R).map f ≫ sglι ((free R).obj Q) := by
    change _ ≫ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map f)).f 0 = _
    rw [HomologicalComplex.single_map_f_self]
    erw [Iso.inv_hom_id_assoc]
  rw [← Category.assoc, h1, Category.assoc, DiscChains.he_hom_f_zero]
  rw [← cancel_mono (chainsXIso R (disc.obj Q) 0).hom]
  have h2 := hnat (disc.map f) 0
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [h2]
  simp

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf : ∀ (R : Type) [CommRing R] , ∃ e : ∀ P : PSh, HomotopyEquiv (sgl ((free R).obj P)) ((chains R).obj (disc.obj P)), (∀ P, sglι _ ≫ (e P).hom.f 0 = (chainsXIso R (disc.obj P) 0).inv) ∧ ∀ {P Q : PSh} (f : P ⟶ Q), (e P).hom ≫ (chains R).map (disc.map f) = (CochainComplex.singleFunctor (Shv R) 0).map ((free R).map f) ≫ (e Q).hom := by
  first | (exact @GlobalTheory.EtC.chains_disc_homotopyEquiv) | (exact GlobalTheory.EtC.chains_disc_homotopyEquiv) | (intros; apply GlobalTheory.EtC.chains_disc_homotopyEquiv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosureProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosureProperties
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem dDR_ιMulti_D (q : ℕ) (v : Fin q → K) :
    dDR k K (ExteriorAlgebra.ιMulti K q fun j => D k K (v j)) = 0 := by
  induction q with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, ← map_one (algebraMap K (DR k K)), dDR_algebraMap,
      Derivation.map_one_eq_zero, map_zero]
  | succ q ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, dDR_mul]
    have ht : Matrix.vecTail (fun j => D k K (v j)) = fun j => D k K (v j.succ) := rfl
    rw [ht, ih (fun j => v j.succ), mul_zero, zero_add,
      show dDR k K (ExteriorAlgebra.ι K (D k K (v 0))) = 0 from dDR_D (v 0), zero_mul]

variable {k K}

theorem mem_deg_of_mem_omB (B : Subalgebra k K) (q : ℕ) (a : DR k K) (ha : a ∈ omB k K B q) :
    a ∈ ⋀[K]^q Ω[K⁄k] := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, -, v, -, rfl⟩ := hx
    exact Submodule.smul_mem _ c (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact Submodule.smul_of_tower_mem _ r hx

theorem mul_mem_omB (B : Subalgebra k K) (p q : ℕ) (a : DR k K) (ha : a ∈ omB k K B p)
    (b : DR k K) (hb : b ∈ omB k K B q) : a * b ∈ omB k K B (p + q) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, v, hv, rfl⟩ := hx
      obtain ⟨c', hc', w, hw, rfl⟩ := hy
      have happ : Fin.append (fun j => D k K (v j)) (fun j => D k K (w j)) =
          fun j => D k K (Fin.append v w j) := by
        funext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
      refine Submodule.subset_span ⟨c * c', B.mul_mem hc hc', Fin.append v w, fun j => ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · rw [Fin.append_left]; exact hv i
        · rw [Fin.append_right]; exact hw i
      · rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti, happ]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

theorem dDR_mem_omB (B : Subalgebra k K) (p : ℕ) (a : DR k K) (ha : a ∈ omB k K B p) :
    dDR k K a ∈ omB k K B (p + 1) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [dDR_smul, dDR_ιMulti_D, smul_zero, add_zero]
    refine Submodule.subset_span ⟨1, B.one_mem, Fin.cons c v, fun j => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) j
      · rw [Fin.cons_zero]; exact hc
      · rw [Fin.cons_succ]; exact hv i
    · rw [one_smul, ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Matrix.vecTail, Function.comp_def, Fin.cons_succ, Fin.cons_zero]
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

theorem smul_mem_omB (B : Subalgebra k K) (p : ℕ) (c : K) (hc : c ∈ B) (a : DR k K)
    (ha : a ∈ omB k K B p) : c • a ∈ omB k K B p := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hx
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_comm c r x]; exact Submodule.smul_mem _ r hx

theorem omB_mono (B B' : Subalgebra k K) (h : B ≤ B') (p : ℕ) : omB k K B p ≤ omB k K B' p := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

theorem mem_omB_zero (B : Subalgebra k K) (y : DR k K) :
    y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, v, -, rfl⟩ := hx
      exact ⟨b, hb, by rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩
    | zero => exact ⟨0, B.zero_mem, (map_zero _).symm⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hz
      exact ⟨c + c', B.add_mem hc hc', (map_add _ _ _).symm⟩
    | smul r x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨r • c, B.smul_mem hc r, by simp only [Algebra.algebraMap_eq_smul_one, smul_assoc]⟩
  · rintro ⟨c, hc, rfl⟩
    exact Submodule.subset_span ⟨c, hc, Fin.elim0, fun j => j.elim0, by
      rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]⟩

theorem omB_alg : ∀ (k K : Type) [Field k] [Field K] [Algebra k K], ∀ (B : Subalgebra k K) (p q : ℕ),
    (∀ a ∈ omB k K B p, ∀ b ∈ omB k K B q, a * b ∈ omB k K B (p + q)) ∧
    (∀ a ∈ omB k K B p, dDR k K a ∈ omB k K B (p + 1) ∧ sg k K a = (-1 : k) ^ p • a ∧
      a ∈ ⋀[K]^p Ω[K⁄k] ∧ ∀ c ∈ B, c • a ∈ omB k K B p) ∧
    (∀ B' : Subalgebra k K, B ≤ B' → omB k K B p ≤ omB k K B' p) ∧
    ∀ y : DR k K, y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  intro k K _ _ _ B p q
  refine ⟨fun a ha b hb => mul_mem_omB B p q a ha b hb, fun a ha => ?_,
    fun B' h => omB_mono B B' h p, mem_omB_zero B⟩
  have hdeg := mem_deg_of_mem_omB B p a ha
  refine ⟨dDR_mem_omB B p a ha, ?_, hdeg, fun c hc => smul_mem_omB B p c hc a ha⟩
  change sgn a = _
  rw [sgn_of_mem hdeg, Algebra.smul_def, map_pow, map_neg, map_one]

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties : ∀ (k K : Type) [Field k] [Field K] [Algebra k K], ∀ (B : Subalgebra k K) (p q : ℕ), (∀ a ∈ omB k K B p, ∀ b ∈ omB k K B q, a * b ∈ omB k K B (p + q)) ∧ (∀ a ∈ omB k K B p, dDR k K a ∈ omB k K B (p + 1) ∧ sg k K a = (-1 : k) ^ p • a ∧ a ∈ ⋀[K]^p Ω[K⁄k] ∧ ∀ c ∈ B, c • a ∈ omB k K B p) ∧ (∀ B' : Subalgebra k K, B ≤ B' → omB k K B p ≤ omB k K B' p) ∧ ∀ y : DR k K, y ∈ omB k K B 0 ↔ ∃ c ∈ B, y = algebraMap K (DR k K) c := by
  first | (exact @GlobalTheory.PD.omB_alg) | (exact GlobalTheory.PD.omB_alg) | (intros; apply GlobalTheory.PD.omB_alg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocally
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocally
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exactIff_loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem exactIff_map_comp {R : Type} [CommRing R] {F G K : Shv R} (φ : F ⟶ G) (ψ : G ⟶ K) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem exactIff_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have := congrArg (fun m => m.hom x) (φ.hom.naturality g.op)
  simpa using this

theorem exactIff_kernel_sec {R : Type} [CommRing R] {G K : Shv R} (ψ : G ⟶ K) {U : Scheme.{0}}
    (b : Sec G U) (hb : Sec.map ψ b = 0) : ∃ k : Sec (kernel ψ) U, Sec.map (kernel.ι ψ) k = b := by
  let Φ : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
    sheafToPresheaf Scheme.etaleTopology _ ⋙ (evaluation _ _).obj (op U)
  let T : ShortComplex (Shv R) := ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition ψ)
  have hT : T.Exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel ψ)
  have hTm : Mono T.f := inferInstanceAs (Mono (kernel.ι ψ))
  have hP : PreservesLimit (parallelPair T.g 0) Φ := inferInstanceAs (PreservesLimit (parallelPair ψ 0) Φ)
  have h2 := (ShortComplex.moduleCat_exact_iff _).1 (hT.map_of_mono_of_preservesKernel Φ hTm hP) b hb
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, hk⟩

theorem exactIff : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  intro R _ S
  have hME : ∀ {F G : Shv R} (φ : F ⟶ G), _ := fun {F G} φ => GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R φ
  rw [ShortComplex.exact_iff_epi_kernel_lift, (hME (kernel.lift S.g S.f S.zero)).2.2.1]
  have hinj : ∀ U, Function.Injective (Sec.map (kernel.ι S.g) (U := U)) :=
    ((hME (kernel.ι S.g)).1).1 inferInstance
  have hfac : ∀ {V : Scheme.{0}} (a : Sec S.X₁ V),
      Sec.map (kernel.ι S.g) (Sec.map (kernel.lift S.g S.f S.zero) a) = Sec.map S.f a := fun a => by
    rw [← exactIff_map_comp, kernel.lift_ι]
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := exactIff_kernel_sec S.g b hb
    refine exactIff_loc_mono (h U k) fun V g ⟨a, ha⟩ => ⟨a, ?_⟩
    rw [← hfac, ha, exactIff_map_res]
  · intro h U k
    have hk : Sec.map S.g (Sec.map (kernel.ι S.g) k) = 0 := by
      rw [← exactIff_map_comp, kernel.condition]; rfl
    refine exactIff_loc_mono (h U _ hk) fun V g ⟨a, ha⟩ => ⟨a, hinj V ?_⟩
    rw [hfac, ha, exactIff_map_res]

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafShortComplexExactIffLocallyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 → Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  first | (exact @GlobalTheory.EtC.exactIff) | (exact GlobalTheory.EtC.exactIff) | (intros; apply GlobalTheory.EtC.exactIff  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  AddMonoidAlgebra.mapRingHom ℤ f

namespace GmPhiNat

theorem laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (laurentMap f).comp (LaurentPolynomial.C : A →+* LaurentPolynomial A) = (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f := by
  refine RingHom.ext fun a => ?_
  change AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a)
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingHom_single]; rfl

theorem laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    laurentMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single n (1 : A)) = AddMonoidAlgebra.single n (1 : B)
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

theorem laurentMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    laurentMap (g.comp f) = (laurentMap g).comp (laurentMap f) :=
  AddMonoidAlgebra.mapRingHom_comp _ _

theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem pull_spMap_comp (q : ℕ) {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) (n i : ℤ)
    (x : Ht q (sp A) n i) : pull _ (spMap (g.comp f)) _ n x = pull _ (spMap g) _ n (pull _ (spMap f) _ n x) := by
  rw [spMap_comp, pull_comp]

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f (tw q i) n x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar A) = laurentVar B := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f))
  have h2 := congrArg (fun φ => φ.hom (LaurentPolynomial.T 1)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [laurentVar, laurentVarUnit, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← h2, laurentMap_T]

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
  have h := (hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)).map
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom
  simpa using h

end GmPhiNat


open GmPhiNat in
theorem gmPhi_nat (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hq : IsUnit (q : A))
    (i : ℤ) (a : Ht q (sp A) 0 (i - 1)) :
    pull _ (spMap (laurentMap f)) _ 1 (gmPhi q A i a) = gmPhi q B i (pull _ (spMap f) _ 0 a) := by
  obtain ⟨hcup, -, -, hkum⟩ := h6 q
  simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [pull_cast, hcup, ← pull_spMap_comp, ← pull_spMap_comp, laurentMap_C]
  congr 2
  rw [spMap, hkum _ _ (isUnit_gamma q A hq), laurentVar_map]

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.KInjPull

variable {C : Type*} [Category C] [Abelian C]

theorem cls_eq_zero_of_acyclic {A I : CochainComplex C ℤ} (hA : A.Acyclic) [I.IsKInjective] {n : ℤ}
    (z : Cocycle A I n) : CohomologyClass.mk z = 0 := by
  let g : A ⟶ I⟦n⟧ := Cocycle.homOf (z.rightShift n 0 (zero_add n))
  let H := IsKInjective.homotopyZero g hA
  have h1 : δ (-1) 0 (Cochain.ofHomotopy H) = (z.1.rightShift n 0 (zero_add n)) := by
    rw [δ_ofHomotopy, Cochain.ofHom_zero, sub_zero]
    have := Cocycle.ofHom_homOf_eq_self (z.rightShift n 0 (zero_add n))
    exact congrArg Subtype.val this
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (Cochain.ofHomotopy H).rightUnshift (n - 1) (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift _ (n - 1) (by omega) n 0 (by omega), h1]
  simp [smul_smul]

end GlobalTheory.EtC.KInjPull

theorem GlobalTheory.EtC.cpull_bijective_of_quasiIso : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (I : Cx R) [I.IsKInjective] (n : ℤ), Function.Bijective (cpull f I n) := by
  intro R _ K L f _ I _ n
  have hA := GlobalTheory.EtC.mappingCone_acyclic R f
  have hz : ∀ m (x : CohomologyClass (mappingCone f) I m), x = 0 := by
    intro m x
    obtain ⟨z, rfl⟩ := x.mk_surjective
    exact KInjPull.cls_eq_zero_of_acyclic hA z
  obtain ⟨e1, e2, -⟩ := GlobalTheory.EtC.coneSeq_exact R f I n
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := (e1 x).1 hx
    rw [hz n w, map_zero]
  · exact (e2 y).1 (hz (n + 1) _)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfQuasiIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [QuasiIso f] (I : Cx R) [I.IsKInjective] (n : ℤ), Function.Bijective (cpull f I n) := by
  first | (exact @GlobalTheory.EtC.cpull_bijective_of_quasiIso) | (exact GlobalTheory.EtC.cpull_bijective_of_quasiIso) | (intros; apply GlobalTheory.EtC.cpull_bijective_of_quasiIso  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquiv
section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IsFracOfAdjoinEqTop
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD.Model

open GlobalTheory.PD

variable (k : Type) [Field k] (d : ℕ)

section Bundle

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

end Bundle

section Cover

variable (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)

def yc (i : Fin (d + 1)) : Fin d → F := fun j => x (i.succAbove j) / x i

theorem isFrac_of_adjoin_eq_top (S : Set F) (h : IntermediateField.adjoin k S = ⊤) :
    IsFractionRing (Algebra.adjoin k S) F := by
  refine IsFractionRing.of_field (Algebra.adjoin k S) F fun z => ?_
  have hz : z ∈ IntermediateField.adjoin k S := h ▸ IntermediateField.mem_top
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
  exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩

theorem ratio_mem_field (hx : ∀ i, x i ≠ 0) (i a : Fin (d + 1)) :
    x a / x i ∈ IntermediateField.adjoin k (Set.range (yc x i)) := by
  rcases eq_or_ne a i with rfl | h
  · rw [div_self (hx a)]
    exact IntermediateField.one_mem _
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
    exact IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩

theorem adjoin_yc_eq_top (hP : IsPd k x) (i : Fin (d + 1)) :
    IntermediateField.adjoin k (Set.range (yc x i)) = ⊤ := by
  rw [eq_top_iff, ← hP.gen, IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  show x j.succ / x 0 ∈ IntermediateField.adjoin k (Set.range (yc x i))

  have e : x j.succ / x 0 = (x j.succ / x i) / (x 0 / x i) := by
    rw [div_div_div_cancel_right₀ (hP.ne i)]
  rw [e]
  exact div_mem (ratio_mem_field k x hP.ne i _) (ratio_mem_field k x hP.ne i _)

theorem trdeg_eq (hP : IsPd k x) : Cardinal.mk (Fin d) ≤ Algebra.trdeg k F := by
  exact hP.indep.cardinalMk_le_trdeg

theorem indep_yc (hP : IsPd k x) (i : Fin (d + 1)) : AlgebraicIndependent k (yc x i) := by

  have : IsFractionRing (Algebra.adjoin k (Set.range (yc x i))) F :=
    isFrac_of_adjoin_eq_top k _ (adjoin_yc_eq_top k x hP i)
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range (yc x i))) F :=
    IsLocalization.isAlgebraic F (nonZeroDivisors (Algebra.adjoin k (Set.range (yc x i))))
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k (yc x i) (trdeg_eq k x hP)).1

theorem rA_single_eq (hx : ∀ i, x i ≠ 0) (i : Fin (d + 1)) :
    rA k x {i} = Algebra.adjoin k (Set.range (yc x i)) := by
  unfold rA
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨i', hi', j, rfl⟩
    rw [Finset.mem_singleton] at hi'
    subst hi'
    rcases eq_or_ne j i' with rfl | h
    · rw [div_self (hx j)]
      exact Subalgebra.one_mem _
    · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq h
      exact Algebra.subset_adjoin ⟨l, rfl⟩
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, i.succAbove j, rfl⟩

def chartEquiv (hP : IsPd k x) (i : Fin (d + 1)) : MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i} :=
  (indep_yc k x hP i).aevalEquiv.trans (Subalgebra.equivOfEq _ _ (rA_single_eq k x hP.ne i).symm)

end Cover

section Extra

end Extra

end GlobalTheory.PD.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquiv
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD


set_option autoImplicit false in
open KaehlerDifferential in
theorem _root_.GlobalTheory.PD.rA_single_polyEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F]
    [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x →
    ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] _root_.GlobalTheory.PD.rA k x {i},
      ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  intro k _ F _ _ d x hP i
  refine ⟨_root_.GlobalTheory.PD.Model.chartEquiv k x hP i, fun j => ?_⟩
  simp [_root_.GlobalTheory.PD.Model.chartEquiv, _root_.GlobalTheory.PD.Model.yc,
    AlgebraicIndependent.aevalEquiv_apply_coe]

end GlobalTheory.PD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ i : Fin (d + 1), ∃ e : MvPolynomial (Fin d) k ≃ₐ[k] rA k x {i}, ∀ j, (e (MvPolynomial.X j) : F) = x (i.succAbove j) / x i := by
  first | (exact @GlobalTheory.PD.rA_single_polyEquiv) | (exact GlobalTheory.PD.rA_single_polyEquiv) | (intros; apply GlobalTheory.PD.rA_single_polyEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUnique
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem expOf_twoSided_unique : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ))
    (d : ℕ) (G : LogFGL v d), IsExp G (expOf G) ∧ (∀ a, subst G.lg (expOf G a) = X a) ∧
      ∀ ex, IsExp G ex → ex = expOf G := by
  intro C _ _ v d G
  obtain ⟨h1, h2, h3⟩ := expOf_spec G
  exact ⟨h1, h3, h2⟩

end GlobalTheory.FGDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupExpTwoSidedInverseUniqueStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupExp_twoSided_inverse_unique : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d), IsExp G (expOf G) ∧ (∀ a, subst G.lg (expOf G a) = X a) ∧ ∀ ex, IsExp G ex → ex = expOf G := by
  first | exact @GlobalTheory.FGDepth.expOf_twoSided_unique | exact GlobalTheory.FGDepth.expOf_twoSided_unique | (intros; apply GlobalTheory.FGDepth.expOf_twoSided_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopForms
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem isTop_exists_and_eq (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) :
    IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧
      ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  intro h
  refine ⟨h.exists_isTop, fun τ hτ y hy => ?_⟩
  obtain ⟨b, hb⟩ := h.exists_basis
  set u : Fin d → K := fun j => (algebraMap F K (x j.succ / x 0))⁻¹
  have hu : ∀ j, u j ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  have hp : (∏ j, u j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hu j
  have hv : vol0 k K x = (∏ j, u j) • ExteriorAlgebra.ιMulti K d b := by
    rw [← AlternatingMap.map_smul_univ]
    simp only [vol0, hb, u]

  have key : ∀ c : K, c • vol0 k K x = τ (c • vol0 k K x) • vol0 k K x := by
    intro c
    rw [map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have e : ExteriorAlgebra.ιMulti K d m = (b.det m * (∏ j, u j)⁻¹) • vol0 k K x := by
      rw [hv, smul_smul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
      intro φ
      have h2 := congrArg (fun g => g m)
        (AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)))
      simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h2
      rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_self]
    rw [e]
    exact key _
  | zero => simp
  | add a c _ _ ha hc => rw [map_add (f := _), add_smul, ← ha, ← hc]
  | smul r a _ ha => rw [map_smul, smul_eq_mul, mul_smul, ← ha]

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopFormsStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧ ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  first | (exact @GlobalTheory.PD.isTop_exists_and_eq) | (exact GlobalTheory.PD.isTop_exists_and_eq) | (intros; apply GlobalTheory.PD.isTop_exists_and_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sch_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPullback (sch.map fst) (sch.map snd) (sch.map f) (sch.map g) := by
  have : PreservesLimit (cospan f g) sch := by
    unfold sch; infer_instance
  exact h.map sch

theorem bc_cechAug_iso : ∀ (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W) (U : Over S),
    ∃ (e₁ : cech (pullback.snd f (pullback.fst r U.hom)) ≅ (bc (cechAug f ≫ sch.map r)).obj U)
      (e₂ : sch.obj (pullback r U.hom) ≅ (bc (sch.map r)).obj U),
      e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U = cechAug _ ≫ e₂.hom := by
  intro S W V r f U
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst f (pullback.fst r U.hom))
    (pullback.snd f (pullback.fst r U.hom)) f (pullback.fst r U.hom) (IsPullback.of_hasPullback _ _)
  have hQ := sch_isPullback (IsPullback.of_hasPullback r U.hom)
  have hP := hm.paste_vert hQ
  refine ⟨hP.isoPullback, hQ.isoPullback, ?_⟩
  apply pullback.hom_ext
  · simp only [bc, bcMap, Category.assoc, pullback.lift_fst, pullback.map]
    rw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_fst]
    exact hm.w
  · simp only [bc, bcMap, Category.assoc, pullback.lift_snd, pullback.map, Category.comp_id]
    rw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCechNerveAugmentationIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_cechNerveAugmentation_iso : ∀ (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W) (U : Over S), ∃ (e₁ : cech (pullback.snd f (pullback.fst r U.hom)) ≅ (bc (cechAug f ≫ sch.map r)).obj U) (e₂ : sch.obj (pullback r U.hom) ≅ (bc (sch.map r)).obj U), e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U = cechAug _ ≫ e₂.hom := by
  first | (exact @GlobalTheory.EtC.bc_cechAug_iso) | (exact GlobalTheory.EtC.bc_cechAug_iso) | (intros; apply GlobalTheory.EtC.bc_cechAug_iso  <;> assumption)
end
end
