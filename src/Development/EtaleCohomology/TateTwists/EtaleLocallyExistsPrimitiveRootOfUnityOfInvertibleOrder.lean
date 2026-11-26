module

public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib
public import Development.EtaleCohomology.KummerTheory.InjSlice

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.EtaleFoundations.PrimLocExPf

noncomputable abbrev cyc (A : Type) [CommRing A] (q : ℕ) : A[X] := (cyclotomic q ℤ).map (Int.castRingHom A)

theorem cyc_monic (A : Type) [CommRing A] (q : ℕ) : (cyc A q).Monic :=
  (cyclotomic.monic q ℤ).map _

theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyc A q) * p₁ + cyc A q * p₂ = 1 := by
  obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have hh' : (X ^ q - 1 : A[X]) = cyc A q * h.map (Int.castRingHom A) := by
    have := congrArg (Polynomial.map (Int.castRingHom A)) hh
    simpa [Polynomial.map_mul] using this
  set H := h.map (Int.castRingHom A)
  have hd : (C (q : A)) * X ^ (q - 1) = derivative (cyc A q) * H + cyc A q * derivative H := by
    have := congrArg derivative hh'
    rw [derivative_mul] at this
    rw [← this]; simp [derivative_X_pow]
  obtain ⟨u, hu⟩ := hq
  refine ⟨C (↑u⁻¹ : A) * X * H, C (↑u⁻¹ : A) * (X * derivative H - C (q : A) * H), ?_⟩
  have hX : X * X ^ (q - 1) = (X ^ q : A[X]) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_neZero q)]
  have key : C (q : A) * X ^ q = X * (derivative (cyc A q) * H + cyc A q * derivative H) := by
    rw [← hd, ← hX]; ring
  have hXq : (X ^ q : A[X]) = cyc A q * H + 1 := by rw [← hh']; ring
  have hCu : C (↑u⁻¹ : A) * C (q : A) = 1 := by rw [← C_mul, ← hu, Units.inv_mul, C_1]
  calc derivative (cyc A q) * (C (↑u⁻¹ : A) * X * H) + cyc A q * (C (↑u⁻¹ : A) * (X * derivative H - C (q : A) * H))
      = C (↑u⁻¹ : A) * (X * (derivative (cyc A q) * H + cyc A q * derivative H) - C (q : A) * (cyc A q * H)) := by ring
    _ = C (↑u⁻¹ : A) * (C (q : A) * X ^ q - C (q : A) * (cyc A q * H)) := by rw [key]
    _ = C (↑u⁻¹ : A) * C (q : A) := by rw [hXq]; ring
    _ = 1 := hCu

noncomputable def pair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    StandardEtalePair A where
  f := cyc A q
  monic_f := cyc_monic A q
  g := 1
  cond := by obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq; exact ⟨p₁, p₂, 0, by simpa using h⟩

theorem hasMap_root (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    (pair A q hq).HasMap (AdjoinRoot.root (cyc A q)) := by
  refine ⟨?_, ?_⟩
  · have : (pair A q hq).f = cyc A q := rfl
    rw [this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · have : (pair A q hq).g = 1 := rfl
    rw [this, map_one]; exact isUnit_one

noncomputable def equivB (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    (pair A q hq).Ring ≃ₐ[A] AdjoinRoot (cyc A q) := by
  refine AlgEquiv.ofAlgHom ((pair A q hq).lift (AdjoinRoot.root (cyc A q)) (hasMap_root A q hq))
    (AdjoinRoot.liftAlgHom (cyc A q) (Algebra.ofId A _) (pair A q hq).X
      (pair A q hq).hasMap_X.1) ?_ ?_
  · apply AdjoinRoot.algHom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    exact (congrArg ((pair A q hq).lift _ (hasMap_root A q hq)) (AdjoinRoot.liftAlgHom_root _ _ _ _)).trans
      (StandardEtalePair.lift_X _ _ _)
  · apply StandardEtalePair.hom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    exact (congrArg (AdjoinRoot.liftAlgHom (cyc A q) (Algebra.ofId A _) (pair A q hq).X
      (pair A q hq).hasMap_X.1) (StandardEtalePair.lift_X _ _ _)).trans (AdjoinRoot.liftAlgHom_root _ _ _ _)

theorem etaleB (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyc A q)) := by
  haveI : Algebra.IsStandardEtale A (AdjoinRoot (cyc A q)) :=
    Algebra.IsStandardEtale.of_equiv (equivB A q hq)
  infer_instance

theorem surjB (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyc A q)))) := by
  intro p
  haveI : Nontrivial A := ⟨⟨0, 1, fun h => p.2.ne_top (by rw [Ideal.eq_top_iff_one, ← h]; exact p.1.zero_mem)⟩⟩
  have hm := cyc_monic A q
  have hdeg : 0 < (cyc A q).natDegree := by
    show 0 < ((cyclotomic q ℤ).map (Int.castRingHom A)).natDegree
    rw [(cyclotomic.monic q ℤ).natDegree_map, natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_neZero q)
  haveI : Module.Free A (AdjoinRoot (cyc A q)) := .of_basis (AdjoinRoot.powerBasis' hm).basis
  haveI : Nontrivial (AdjoinRoot (cyc A q)) := by
    have hne : (AdjoinRoot.powerBasis' hm).basis ⟨0, hdeg⟩ ≠ 0 := (AdjoinRoot.powerBasis' hm).basis.ne_zero _
    exact nontrivial_of_ne _ _ hne
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat p

end LateralTheory.EtaleFoundations.PrimLocExPf

namespace LateralTheory.EtaleFoundations.PrimLocExPf

def primMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (q : ℕ) (ζ : Prim q R) : Prim q S :=
  ⟨φ ζ.1, by simpa using ζ.2.1.map φ, by
    have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h
    simpa using h⟩

theorem root_prim (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    IsUnit (q : AdjoinRoot (cyc A q)) ∧
      aeval (AdjoinRoot.root (cyc A q)) (cyclotomic q ℤ) = 0 := by
  refine ⟨by simpa using hq.map (algebraMap A (AdjoinRoot (cyc A q))), ?_⟩
  have : cyc A q = (cyclotomic q ℤ).map (algebraMap ℤ A) := by rw [algebraMap_int_eq]
  rw [← Polynomial.aeval_map_algebraMap A, ← this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem mono_prim (q : ℕ) {U : Scheme.{0}} : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    Nonempty (Prim q Γ(V, ⊤)) → Nonempty (Prim q Γ(W, ⊤)) := by
  rintro V W g k ⟨ζ⟩
  exact ⟨primMap k.appTop.hom q ζ⟩

end LateralTheory.EtaleFoundations.PrimLocExPf

namespace LateralTheory.EtaleFoundations

open PrimLocExPf in
theorem etale_locally_exists_primitive_root_of_unity_of_invertible_order : EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  intro q _ U hq
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U (fun V _ => Nonempty (Prim q Γ(V, ⊤))) (mono_prim q)]
  intro y
  obtain ⟨W, hWa, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (show y ∈ (⊤ : U.Opens) from trivial)
  have hqA : IsUnit (q : Γ(U, W)) := by
    simpa using hq.map (U.presheaf.map (homOfLE le_top).op).hom
  have hE := etaleB Γ(U, W) q hqA
  let φ : Γ(U, W) ⟶ CommRingCat.of (AdjoinRoot (cyc Γ(U, W) q)) := CommRingCat.ofHom (algebraMap _ _)
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr
      ((RingHom.etale_algebraMap (R := Γ(U, W)) (S := AdjoinRoot (cyc Γ(U, W) q))).mpr hE)
  refine ⟨_, Spec.map φ ≫ hWa.fromSpec, inferInstance, inferInstance, ?_, ?_⟩
  · have hy : y ∈ Set.range hWa.fromSpec := by rw [hWa.range_fromSpec]; exact hyW
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, hr⟩ := surjB Γ(U, W) q p
    exact ⟨r, congrArg hWa.fromSpec hr⟩
  · have h := root_prim Γ(U, W) q hqA
    exact ⟨primMap (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyc Γ(U, W) q)))).inv.hom q
      ⟨AdjoinRoot.root _, h.1, h.2⟩⟩

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleLocallyKummerRootsOfUnitsOfInvertibleOrder
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.EtaleFoundations.PrimLocKumPf

noncomputable abbrev kpol {A : Type} [CommRing A] (q : ℕ) (u : A) : A[X] := X ^ q - C u

theorem kpol_monic {A : Type} [CommRing A] (q : ℕ) [NeZero q] (u : A) : (kpol q u).Monic :=
  monic_X_pow_sub_C u (NeZero.ne q)

theorem kpol_natDegree {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] (u : A) :
    (kpol q u).natDegree = q :=
  natDegree_X_pow_sub_C _

theorem root_pow {A : Type} [CommRing A] (q : ℕ) (u : A) :
    AdjoinRoot.root (kpol q u) ^ q = algebraMap A (AdjoinRoot (kpol q u)) u := by
  have h := AdjoinRoot.eval₂_root (kpol q u)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact sub_eq_zero.mp h

theorem root_isUnit {A : Type} [CommRing A] (q : ℕ) [NeZero q] (u : Aˣ) :
    IsUnit (AdjoinRoot.root (kpol q (u : A))) := by
  have h : IsUnit (AdjoinRoot.root (kpol q (u : A)) ^ q) := by
    rw [root_pow]; exact u.isUnit.map _
  exact (isUnit_pow_iff (NeZero.ne q)).mp h

theorem deriv_isUnit {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (u : Aˣ) :
    IsUnit (AdjoinRoot.mk (kpol q (u : A)) (derivative (kpol q (u : A)))) := by
  have hd : derivative (kpol q (u : A)) = C (q : A) * X ^ (q - 1) := by
    simp [kpol, derivative_X_pow]
  rw [hd, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  refine IsUnit.mul (hq.map _) ?_
  exact (root_isUnit q u).pow _

theorem etale_kum {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (u : Aˣ) :
    Algebra.Etale A (AdjoinRoot (kpol q (u : A))) :=
  let P : StandardEtalePair A := ⟨kpol q (u : A), kpol_monic q _, derivative (kpol q (u : A)), 1, 0, 1, by simp⟩
  .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk P.f (derivative (kpol q (u : A))))) _
      (deriv_isUnit q hq u)).symm.restrictScalars A))

theorem ff_kum {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] (u : A) :
    Module.FaithfullyFlat A (AdjoinRoot (kpol q u)) := by
  have hf := kpol_monic q u
  have : Module.Free A (AdjoinRoot (kpol q u)) := hf.free_adjoinRoot
  have : Module.Finite A (AdjoinRoot (kpol q u)) := hf.finite_adjoinRoot
  have hr : Module.finrank A (AdjoinRoot (kpol q u)) = q := by
    rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hf).basis, Fintype.card_fin]
    exact kpol_natDegree q u
  have : Nontrivial (AdjoinRoot (kpol q u)) :=
    Module.nontrivial_of_finrank_pos (R := A) (by rw [hr]; exact Nat.pos_of_neZero q)
  infer_instance

theorem mono_kum (q : ℕ) {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) :
    ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    (∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) →
    ∃ v : (Γ(W, ⊤))ˣ, v ^ q = Units.map (k ≫ g).appTop.hom.toMonoidHom u := by
  rintro V W g k ⟨v, hv⟩
  refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
  rw [← map_pow, hv]
  ext
  simp <;> rfl

theorem pt (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ)
    (y : U) : ∃ (V : Scheme.{0}) (g : V ⟶ U), IsAffine V ∧ Etale g ∧ y ∈ Set.range g ∧
      ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  obtain ⟨W, hW, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (Set.mem_univ y)
  obtain ⟨z, hz⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
  let A : CommRingCat.{0} := Γ(U, W)
  have : Nontrivial A := by
    have := z.asIdeal.ne_top_iff_one.mp z.isPrime.ne_top
    exact ⟨⟨1, 0, fun h => this (h ▸ z.asIdeal.zero_mem)⟩⟩
  let ρ : Γ(U, ⊤) →+* A := (Scheme.ΓSpecIso A).hom.hom.comp hW.fromSpec.appTop.hom
  let u₁ : Aˣ := Units.map ρ.toMonoidHom u
  have hqA : IsUnit (q : A) := by simpa using hq.map ρ
  let B : CommRingCat.{0} := CommRingCat.of (AdjoinRoot (kpol q (u₁ : A)))
  let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (AdjoinRoot (kpol q (u₁ : A))))
  have he : Algebra.Etale A (AdjoinRoot (kpol q (u₁ : A))) := etale_kum q hqA u₁
  have hff : Module.FaithfullyFlat A (AdjoinRoot (kpol q (u₁ : A))) := ff_kum q _
  have hE : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr he
  have hS : Surjective (Spec.map φ) :=
    ((flat_and_surjective_SpecMap_iff φ).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2
  refine ⟨Spec B, Spec.map φ ≫ hW.fromSpec, inferInstance, inferInstance, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hS.surj z
    exact ⟨w, by simp [hw, hz]⟩
  · obtain ⟨r, hr⟩ := root_isUnit q u₁
    refine ⟨Units.map (Scheme.ΓSpecIso B).inv.hom.toMonoidHom r, ?_⟩
    ext
    set w : Γ(Spec A, ⊤) := hW.fromSpec.appTop.hom (u : Γ(U, ⊤)) with hw
    have hnat : (Scheme.ΓSpecIso B).hom.hom ((Spec.map φ).appTop.hom w) =
        φ.hom ((Scheme.ΓSpecIso A).hom.hom w) := by
      rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    show ((Scheme.ΓSpecIso B).inv.hom (r : AdjoinRoot (kpol q (u₁ : A)))) ^ q =
      (Spec.map φ).appTop.hom w
    rw [← map_pow, hr, root_pow]
    change (Scheme.ΓSpecIso B).inv.hom (φ.hom ((Scheme.ΓSpecIso A).hom.hom w)) = _
    rw [← hnat, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

end LateralTheory.EtaleFoundations.PrimLocKumPf

theorem LateralTheory.EtaleFoundations.etale_locally_kummer_roots_of_units_of_invertible_order : LateralTheory.EtaleFoundations.EtaleLocallyKummerRootsOfUnits := by
  intro q _ U hq u
  rw [LateralTheory.EtaleFoundations.etale_sheaf_section_locally_iff_of_presheaf_facts U _ (LateralTheory.EtaleFoundations.PrimLocKumPf.mono_kum q u)]
  exact LateralTheory.EtaleFoundations.PrimLocKumPf.pt q U hq u
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTorsionCohomologyLocalizationBasic
namespace LateralTheory.Fin.EtaleLocalPropertyBasicClosure
theorem etale_torsion_cohomology_localization_basic : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure := by
  apply LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure := etale_torsion_cohomology_localization_basic
end LateralTheory.Fin.EtaleLocalPropertyBasicClosure
end

section -- merged from Development.EtaleCohomology.TateTwists.PpEvDeltaPf
theorem LateralTheory.EtaleFoundations.pp_ev_delta_of : LateralTheory.EtaleFoundations.pp_ev_delta :=
  LateralTheory.EtaleFoundations.etale_chain_cochain_eval_differential_formula_holds
end

section -- merged from Development.EtaleCohomology.TateTwists.TtTensExPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations

structure TensPre {R : Type} [CommRing R] (I J : Cx R) where
  P : CochainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℤ
  e : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w ≃ₗ[ULift.{1} R] (P.X w).obj (op U)
  nat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
    e V w (Tens.res g w x) = ((P.X w).map g.op).hom (e U w x)
  leibniz : ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    ((P.d w (w + 1)).app (op U)).hom (e U w (DirectSum.of _ ⟨(s, t), h⟩ (a ⊗ₜ b))) =
      e U (w + 1) (DirectSum.of _ ⟨(s + 1, t), by omega⟩ (Sec.map (I.d s (s + 1)) a ⊗ₜ b)) +
      s.negOnePow • e U (w + 1) (DirectSum.of _ ⟨(s, t + 1), by omega⟩ (a ⊗ₜ Sec.map (J.d t (t + 1)) b))

def tt_tens_pre : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), Nonempty (TensPre I J)

def tt_tens_sheafify : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), TensPre I J → ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

theorem tt_tens_ex_of (hpre : tt_tens_pre) (hsh : tt_tens_sheafify) : tt_tens_ex := by
  intro R _ I J
  obtain ⟨T⟩ := hpre R I J
  exact hsh R I J T

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.PpEvBasicPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvBasicPf
variable {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
open LateralTheory.KummerTheory.AW

theorem ev_sub (α β : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [ev_eq, Cochain.sub_v, Preadditive.comp_sub]
  exact map_sub (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl)) _ _

theorem ev_zero (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  rw [ev_eq, Cochain.zero_v, comp_zero]
  exact map_zero (AddMonoidHom.mk' (fun φ : _ ⟶ I.X s => Sec.map φ (freeGen R _ U x)) (fun _ _ => rfl))

theorem ev_zsmul (c : ℤ) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) : ev (c • α) p s h U x = c • ev α p s h U x := by
  exact map_zsmul (AddMonoidHom.mk' (fun β : Cochain ((chains R).obj E) I n => ev β p s h U x)
    (fun a b => ev_add a b p s h U x)) c α

theorem ev_post {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  rw [ev_eq, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ev_eq]; rfl

theorem chainsXIso_nat {E' : Spc} (f : E' ⟶ E) (p : ℕ) :
    (chainsXIso R E' p).inv ≫ ((chains R).map f).f (-(p : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E p).inv := by
  rw [Iso.inv_comp_eq]
  unfold chains chainsXIso
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(p : ℤ)) = _
  exact HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl

theorem ev_pre {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    (U : Scheme.{0}) (x : Sx E' p U) :
    ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f) := by
  rw [ev_eq, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, reassoc_of% (chainsXIso_nat (R := R) f p), ev_eq]
  change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ h) (Sec.map ((free R).map (f.app (op (SimplexCategory.mk p))))
    (freeGen R _ U x)) = _
  rw [map_freeGen]; rfl

end LateralTheory.EtaleFoundations.EvBasicPf

open LateralTheory.EtaleFoundations.EvBasicPf LateralTheory.KummerTheory.AW in
theorem LateralTheory.EtaleFoundations.pp_ev_basic_of : LateralTheory.EtaleFoundations.pp_ev_basic := fun _ _ =>
  ⟨fun α β p s h U x => ⟨ev_add α β p s h U x, ev_sub α β p s h U x, ev_zero p s h U x, fun c => ev_zsmul c α p s h U x⟩,
   fun α p s h _ _ g x => ev_res α p s h g x,
   fun α β hh => ev_ext α β hh,
   fun f α p s h U x => ev_pre f α p s h U x,
   fun m α p s h U x => ev_post m α p s h U x⟩
end
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSheafRestrictScalarsResolutionHomExistsOfEx
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma restr_ex_hom_ext_of_qis {C : Type*} [Category C] [Abelian C] {K K' L : CochainComplex C ℤ}
    [L.IsKInjective] (s : K ⟶ K') [QuasiIso s] (f : K ⟶ L) :
    ∃ g : K' ⟶ L, Nonempty (Homotopy (s ≫ g) f) := by
  have hL := CochainComplex.IsKInjective.rightOrthogonal L
  rw [← ObjectProperty.isLocal_trW] at hL
  have hs : (HomotopyCategory.subcategoryAcyclic C).trW ((HomotopyCategory.quotient C _).map s) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  obtain ⟨g', hg'⟩ := (hL _ hs).2 ((HomotopyCategory.quotient C _).map f)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g'
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa using hg'

def EtaleSheafRestrictScalarsFunctorExact : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S),
    PreservesFiniteLimits (restr φ) ∧ PreservesFiniteColimits (restr φ)

theorem etaleSheaf_restrictScalars_resolution_hom_exists_of_exact (hE : EtaleSheafRestrictScalarsFunctorExact) : EtaleSheafRestrictScalarsInjectiveResolutionHomExists := by
  intro R S _ _ φ F
  obtain ⟨h1, h2⟩ := hE R S φ
  let G := restr φ
  have : G.Additive := G.additive_of_preserves_binary_products
  let IS := injectiveResolution F
  let IR := injectiveResolution (G.obj F)
  have : (res R (G.obj F)).IsKInjective := inferInstanceAs IR.cochainComplex.IsKInjective
  have : (res R (G.obj F)).IsStrictlyGE 0 := inferInstanceAs (IR.cochainComplex.IsStrictlyGE 0)
  let s := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map IS.ι'
  have : QuasiIso s := inferInstance
  let f0 := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F ≫ IR.ι'
  obtain ⟨g, ⟨h⟩⟩ := restr_ex_hom_ext_of_qis (L := res R (G.obj F)) s f0
  refine ⟨fun n => g.f n, fun i j => (g.comm i j).symm, ?_⟩
  have hz1 : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X 1) :=
    G.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by decide))
  have key : (s ≫ g).f 0 = f0.f 0 := by
    rw [h.comm 0]
    have e1 : dNext 0 h.hom = 0 := by
      have e : h.hom 1 0 = 0 := hz1.eq_of_src _ _
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl), e, comp_zero]
    have e2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
        ((res R (G.obj F)).isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_of_tgt (h.hom 0 (-1)) 0, zero_comp]
    rw [e1, e2, zero_add, zero_add]
  have key2 := congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) key
  simp only [s, f0, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp] at key2
  have key3 : G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ G.map (IS.ι'.f 0) ≫ g.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv ≫ IR.ι'.f 0 := by
    refine key2.trans ?_
    have c2 : ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F).f 0 =
        G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv :=
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self _ _ _ _
    calc _ = G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ ((G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv) ≫ IR.ι'.f 0) := by
          exact congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) (congrArg (fun y => y ≫ IR.ι'.f 0) c2)
      _ = _ := by
          have aux : ∀ {A B : Shv S} {Y Z : Shv R} (e : A ≅ B) (u : G.obj B ⟶ Y) (v : Y ⟶ Z),
              G.map e.inv ≫ (G.map e.hom ≫ u) ≫ v = u ≫ v := by
            intro A B Y Z e u v
            rw [← Category.assoc, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
          exact aux _ _ _
  simp only [resι]
  erw [Functor.map_comp, Category.assoc]
  exact key3

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.PpEvMkPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EvMkPf

variable {R : Type} [CommRing R] {E : Spc} {I : Cx R}

theorem sq {X Y : Type 1} (h : X ⟶ Y) {M N : ModuleCat.{1} (ULift.{1} R)} (a : Y ⟶ M) (b : X ⟶ N) (φ : N ⟶ M)
    (H : ∀ x, a (h x) = φ (b x)) :
    (ModuleCat.free (ULift.{1} R)).map h ≫ ModuleCat.freeDesc a = ModuleCat.freeDesc b ≫ φ := by
  apply ModuleCat.free_hom_ext
  intro x
  simp [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, H]

noncomputable def eta (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (freeP R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (I.X s).obj where
  app U := ModuleCat.freeDesc (X := ULift.{1} (Sx E k U.unop)) (↾fun x => F U.unop (ULift.down x))
  naturality U V g := sq _ _ _ _ (fun x => (hF V.unop U.unop g.unop x.down).symm)

noncomputable def phi (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).symm (eta k s F hF)

theorem phi_unit (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g)) :
    toSheafify Scheme.etaleTopology.{0} ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) ≫ (phi k s F hF).hom =
      eta k s F hF := by
  have := ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (E.obj (op (SimplexCategory.mk k)))) (I.X s)).apply_symm_apply (eta k s F hF)
  rw [Adjunction.homEquiv_unit] at this
  exact this

theorem phi_freeGen (k : ℕ) (s : ℤ) (F : ∀ U : Scheme.{0}, Sx E k U → Sec (I.X s) U)
    (hF : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E k U), Sec.res g (F U x) = F V (x.res g))
    (U : Scheme.{0}) (x : Sx E k U) :
    ((phi k s F hF).hom.app (op U)).hom (freeGen R _ U x) = F U x := by
  have h2 := congrArg (fun f => (f.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))) (phi_unit k s F hF)
  exact h2.trans (ModuleCat.freeDesc_apply _ _)

variable {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
  (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))

noncomputable def comp (p q : ℤ) (hpq : p + n = q) : ((chains R).obj E).X p ⟶ I.X q :=
  if hp : p ≤ 0 then
    (HomologicalComplex.XIsoOfEq _ (by omega : p = -((p.natAbs : ℕ) : ℤ))).hom ≫ (chainsXIso R E p.natAbs).hom ≫
      phi p.natAbs q (fun U x => a p.natAbs q (by omega) U x) (fun V U g x => ha _ _ _ V U g x)
  else 0

theorem aux {s : ℤ} (j k : ℕ) (e : j = k) (hjk : -(k : ℤ) = -(j : ℤ)) (hj : -(j : ℤ) + n = s) (hk : -(k : ℤ) + n = s) :
    (HomologicalComplex.XIsoOfEq ((chains R).obj E) hjk).hom ≫ (chainsXIso R E j).hom ≫
      phi j s (fun U x => a j s hj U x) (fun V U g x => ha _ _ _ V U g x) =
    (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s hk U x) (fun V U g x => ha _ _ _ V U g x) := by
  subst e
  simp

theorem comp_neg (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) :
    comp a ha (-(k : ℤ)) s h = (chainsXIso R E k).hom ≫ phi k s (fun U x => a k s h U x) (fun V U g x => ha _ _ _ V U g x) := by
  unfold comp
  rw [dite_eq_left (by omega)]
  exact aux a ha _ _ (by omega) _ _ _

end LateralTheory.EtaleFoundations.EvMkPf

open LateralTheory.EtaleFoundations.EvMkPf in
theorem LateralTheory.EtaleFoundations.pp_ev_mk_of : LateralTheory.EtaleFoundations.pp_ev_mk := by
  intro R _ E I n a ha
  refine ⟨Cochain.mk (comp a ha), fun p s h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, comp_neg a ha p s h, Iso.inv_hom_id_assoc]
  exact phi_freeGen _ _ _ _ U x
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSectionsGlueOverCoverOfComponents
namespace LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
theorem etale_sections_glue_over_cover_of_components : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := by
  apply LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleSheafSectionsSeparatedAndGlue := etale_sections_glue_over_cover_of_components
end LateralTheory.Fin.EtaleSheafSectionsSeparatedAndGlue
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleSingleSheafHomotopicMapsEqualHolds
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_single_sheaf_homotopic_maps_equal_holds : LateralTheory.EtaleFoundations.EtaleSingleSheafHomotopicMapsToNonnegComplexEqual := by
  intro R _ F I _ a b ⟨h⟩
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst hi
    rw [h.comm 0]
    have h1 : dNext 0 h.hom = 0 := by
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
      rw [show (sgl F).d 0 1 = 0 from
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by omega)).eq_of_tgt _ _]
      simp
    have h2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)]
      rw [show h.hom 0 (-1) = 0 from (CochainComplex.isZero_of_isStrictlyGE I 0 (-1) (by omega)).eq_of_tgt _ _]
      simp
    rw [h1, h2]; simp
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi).eq_of_src _ _
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleKInjectiveHomLiftAlongQuasiIsoHolds
open CategoryTheory Limits GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_kInjective_hom_lift_along_quasiIso_holds : LateralTheory.EtaleFoundations.EtaleKInjectiveHomLiftAlongQuasiIsoUpToHomotopy := by
  intro R _ K L I _ f _
  have hI := CochainComplex.IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hI
  have hf : (HomotopyCategory.subcategoryAcyclic (Shv R)).trW
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).mpr inferInstance
  have hb := hI _ hf
  refine ⟨fun a => ?_, fun m m' h => ?_⟩
  · obtain ⟨m', hm'⟩ := hb.2 ((HomotopyCategory.quotient _ _).map a)
    obtain ⟨m, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective m'
    refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    rw [Functor.map_comp]; exact hm'
  · obtain ⟨h⟩ := h
    have e := HomotopyCategory.eq_of_homotopy _ _ h
    rw [Functor.map_comp, Functor.map_comp] at e
    exact ⟨HomotopyCategory.homotopyOfEq _ _ (hb.1 e)⟩
end

section -- merged from Development.EtaleCohomology.TateTwists.TtResSidePf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tensor_universal_property : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def tensor_quasi_isomorphism : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

theorem tt_res_side_of (huniv : tensor_universal_property) (hqis : tensor_quasi_isomorphism) : tt_res_side := by
  intro q _ i I J M T e hI hJ hflat σ τ hσ hτ
  obtain ⟨hIge, ε, hε, hgen⟩ := hI
  obtain ⟨u, hu, -⟩ := (huniv (ZMod q) σ hσ).1 τ ε (𝟙 J)
  have := hIge
  have := hJ
  refine ⟨u, hqis (ZMod q) σ τ hσ hτ hflat ε u hu, fun U ζ b => ?_⟩
  rw [hu U 0 0 0 (add_zero 0), hgen U ζ]
  simp only [HomologicalComplex.id_f]
  rfl

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.acycIffPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.acycIffPf

variable {R : Type} [CommRing R]

abbrev ev (U : Scheme.{0}) : Shv R ⥤ ModuleCat.{1} (ULift.{1} R) :=
  sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙ (evaluation _ _).obj (op U)

theorem app_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) (U : Scheme.{0}) (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun f => f.hom x) (φ.hom.naturality g.op)

theorem iCycles_inj (S : ShortComplex (Shv R)) (U : Scheme.{0}) :
    Function.Injective (Sec.map S.iCycles (U := U)) := by
  have : Mono ((ev U).map S.iCycles) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem iCycles_surj (S : ShortComplex (Shv R)) (U : Scheme.{0}) (z : Sec S.X₂ U) (hz : Sec.map S.g z = 0) :
    ∃ c : Sec S.cycles U, Sec.map S.iCycles c = z := by
  let S' : ShortComplex (Shv R) := ShortComplex.mk S.iCycles S.g S.iCycles_g
  have hS' : S'.Exact := S'.exact_of_f_is_kernel S.cyclesIsKernel
  have hE : (S'.map (ev U)).Exact := hS'.map_of_mono_of_preservesKernel (ev U) (inferInstanceAs (Mono S.iCycles)) inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).1 hE z hz

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔
    ∀ (U : Scheme.{0}) (z : Sec S.X₂ U), Sec.map S.g z = 0 →
      Loc U fun V g => ∃ y : Sec S.X₁ V, Sec.map S.f y = Sec.res g z := by
  rw [S.exact_iff_epi_toCycles, ← Sheaf.isLocallySurjective_iff_epi' _ S.toCycles]
  constructor
  · intro h U z hz
    obtain ⟨c, rfl⟩ := iCycles_surj S U z hz
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} S.toCycles.hom (U := op U) c, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h1 : Sec.map S.f t = Sec.map S.iCycles (Sec.map S.toCycles t) := by
      rw [← app_comp, S.toCycles_i]
    rw [h1, ← map_res]
    exact congrArg _ ht
  · intro h
    constructor
    intro U c
    obtain ⟨Sv, hSv, hP⟩ := h U (Sec.map S.iCycles c) (by rw [← app_comp, S.iCycles_g]; rfl)
    refine Scheme.etaleTopology.{0}.superset_covering ?_ hSv
    intro V g hg
    obtain ⟨y, hy⟩ := hP V g hg
    refine ⟨y, iCycles_inj S V ?_⟩
    change Sec.map S.iCycles (Sec.map S.toCycles y) = Sec.map S.iCycles (Sec.res g c)
    rw [← app_comp, S.toCycles_i, hy, map_res]

end LateralTheory.EtaleFoundations.acycIffPf

open LateralTheory.EtaleFoundations.acycIffPf in
theorem LateralTheory.EtaleFoundations.acyc.acycIff_of : LateralTheory.EtaleFoundations.acyc.acycIff := by
  intro R _ C
  unfold LateralTheory.EtaleFoundations.acyc.LocAcyc
  constructor
  · intro h U n z hz
    have := (HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)).1 (h n)
    exact (exact_iff _).1 this U z hz
  · intro h n
    rw [HomologicalComplex.exactAt_iff' C (n - 1) n (n + 1) (by simp) (by simp)]
    exact (exact_iff _).2 fun U z hz => h U n z hz
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductLeibnizOfSeparated
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

def SecSep : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U),
    (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b

lemma res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  exact congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op).symm

lemma res_add {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ x y

lemma res_usmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (x : Sec F U) :
    Sec.res g (u • x) = u • Sec.res g x := by
  simp only [Units.smul_def]; exact map_zsmul _ _ x

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hP V g hg)⟩

lemma leib_lift {R : Type} [CommRing R] {I J K T M L : Cx R} (τ : Pair I J T) (μ' : Pair J K M) (ν' : Pair I M L)
    (m : ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w → Sec (T.X s) U →ₗ[ULift.{1} R] Sec (K.X t) U →ₗ[ULift.{1} R] Sec (L.X w) U)
    (heq : ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
        m U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c))
    (V : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (x : Tens I J V s) (b : Sec (K.X t) V) :
    Sec.map (L.d w (w + 1)) (m V s t w h (τ.lift V s x) b) = m V (s + 1) t (w + 1) (by omega) (Sec.map (T.d s (s + 1)) (τ.lift V s x)) b +
          s.negOnePow • m V s (t + 1) (w + 1) (by omega) (τ.lift V s x) (Sec.map (K.d t (t + 1)) b) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
    rw [hx, hy]; abel
  | of p z =>
    obtain ⟨⟨s1, t1⟩, hp⟩ := p
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add (f := _), LinearMap.add_apply, smul_add, Sec.map] at hx hy ⊢
      rw [hx, hy]; abel
    | tmul a1 b1 =>
      have hl : τ.lift V s (DirectSum.of _ ⟨(s1, t1), hp⟩ (a1 ⊗ₜ b1)) = τ.mul V s1 t1 s hp a1 b1 := by
        unfold Pair.lift
        rw [← DirectSum.lof_eq_of (ULift.{1} R), DirectSum.toModule_lof, TensorProduct.lift.tmul]
      simp only at hp
      rw [hl, τ.leibniz V s1 t1 s hp a1 b1]
      rw [heq V s1 t1 t s (t1 + t) w hp h (by omega) (by omega)]
      rw [ν'.leibniz V s1 (t1 + t) w (by omega), μ'.leibniz V t1 t (t1 + t) rfl]
      simp only [map_add (f := _), LinearMap.add_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]
      rw [heq V (s1 + 1) t1 t (s + 1) (t1 + t) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 (t1 + 1) t (s + 1) (t1 + t + 1) (w + 1) (by omega) (by omega) (by omega) (by omega),
        heq V s1 t1 (t + 1) s (t1 + t + 1) (w + 1) hp (by omega) (by omega) (by omega)]
      have hs : ((s.negOnePow : ℤˣ) : ℤ) = (s1.negOnePow : ℤ) * (t1.negOnePow : ℤ) := by
        rw [← Units.val_mul, ← Int.negOnePow_add, hp]
      rw [hs, mul_smul, smul_add]
      abel

end LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated

open LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated in
theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_leibniz_of_separated (hsep : LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibnizSeparated.SecSep) :
    LateralTheory.EtaleFoundations.EtaleTensorTripleProductLeibniz := by
  intro R _ I J K T τ hτ M L μ' ν' m hnat heq U s t w h a b
  apply hsep R (L.X (w + 1)) U
  refine loc_mono (hτ.1 U s a) ?_
  rintro V g ⟨x, hx⟩
  rw [res_map, hnat, res_add, res_usmul, hnat, hnat, res_map, res_map, ← hx, leib_lift τ μ' ν' m heq]
end

section -- merged from Development.EtaleCohomology.TateTwists.TtTensGePf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tens_univ_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor →
    (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0)

theorem tt_tens_ge_of (h : tens_univ_ge) : tt_tens_ge := by
  intro R _ I J K μ hI hJ hμ
  exact h R μ hμ hI hJ

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.TPaCpushIdPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_id_of : t_pa_cpush_id := by
  intro R _ E I n x
  obtain ⟨a, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp a (Cocycle.ofHom (𝟙 I)) (add_zero n)) = CohomologyClass.mk a
  congr 1
  apply Cocycle.ext
  simp [zcomp]

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.TPaCpushHtpyPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_htpy_of : t_pa_cpush_htpy := by
  intro R _ E I J u u' H n x
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)) =
    CohomologyClass.mk (zcomp α (Cocycle.ofHom u') (add_zero n))
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy H) (show n + -1 = n - 1 by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  simp [zcomp, Cochain.comp_sub]

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.TPaPrecompPf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem pa_sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)
  simpa using this.symm

theorem pa_sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem t_pa_precomp_of : t_pa_precomp := by
  intro R _ I I' J K u μ
  refine ⟨⟨fun U s t w h => (μ.mul U s t w h).comp ((u.f s).hom.app (op U)).hom, ?_, ?_⟩, ?_⟩
  · intro V U g s t w h a b
    simp only [LinearMap.comp_apply]
    exact (μ.nat g s t w h _ b).trans (by rw [pa_sec_res_map])
  · intro U s t w h a b
    simp only [LinearMap.comp_apply]
    rw [μ.leibniz]
    congr 2
    rw [← pa_sec_map_comp, u.comm]; rfl
  · intro U s t w h a b
    rfl

end LateralTheory.EtaleFoundations
end
