module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedLineBundleTrivialOfTorsionGeometricFib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsLinearSimilitudeMemKernelPolarisatiStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsLinearSimilitudeMemKernelPolarization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.Hecke.KerPol
open GlobalTheory.UPel.HT.Hecke

theorem hecke_sections_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h hh
  have hfib := GlobalTheory.T.hecke_bundle_trivial_geometric_fibre p D R b g c k N hc hk hN hNp hEF hg hck S s o h hh
  obtain ⟨x, rfl⟩ := hh
  have hP := o.isLB
  have clsPow : ∀ {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h' : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB),
      GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h' = n • GlobalTheory.CechPic.cls L hL := by
    intro X L hL n h'
    unfold GlobalTheory.UPel.HT.Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb hP _ _
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = (k ^ 2 / c) • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow hP _ hQ, map_nsmul]
  have hpow : ∀ (a : o.A ⟶ o.A) (n : ℕ),
      GlobalTheory.AbDual.evc hP (a ^ n) (𝟙 o.A) = n • GlobalTheory.AbDual.evc hP a (𝟙 o.A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
    | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hP).1 hadd, ih, succ_nsmul]
  have etaPow : ∀ (n : ℕ) (z : D.La), (o.eta z) ^ n = o.eta (n • z) := by
    intro n z
    induction n with
    | zero => rw [pow_zero, zero_smul, eta_zero]
    | succ n ih => rw [pow_succ, ih, succ_nsmul, o.eta_add]
  set th : o.A ⟶ o.A := toUnit o.A ≫ o.eta (N • g x) with hth
  have hk1 : th ^ k = 1 := by
    rw [hth, ← MonObj.comp_pow, etaPow, smul_smul, show k * N = N * k from mul_comm _ _, o.eta_ker, MonObj.comp_one]
  have htors : k • GlobalTheory.AbDual.evc hP th (𝟙 o.A) = 0 := by
    rw [← hpow, hk1]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hQth : GlobalTheory.AbDual.evc hQ th (𝟙 o.A) = 0 := by
    have hM : (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).IsLB := pull_isLB hQ _
    have hunit : IsUnit ((k : Γ(S, ⊤))) := by
      have hR := b.unit k hk
      have e := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      have e2 := e.map (s.appTop.hom)
      simpa using e2
    have hrig : ∃ t : ((GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).pull
        (1 : 𝟙_ (Over S) ⟶ o.A).left).Gen, t.IsGen := by
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM, GlobalTheory.AbDual.cls_ev hQ,
        GlobalTheory.AbDual.pull_evc, evcQ, Category.comp_id, GlobalTheory.AbDual.evc_one_right hP o.rig₂, smul_zero]
    have hpowM : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).Gen, t.IsGen := by
      have hMk : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).IsLB :=
        LB.isLB_linComb hM _ _
      refine (GlobalTheory.CechPic.cls_eq_zero_iff hMk).1 ?_
      rw [clsPow hM k hMk, GlobalTheory.AbDual.cls_ev hQ, evcQ,
        smul_comm, htors, smul_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres S o.A o.ab _ hM hrig k hunit hpowM hfib
    exact (GlobalTheory.AbDual.triv_ev_iff hQ _ _).1 ⟨t, ht⟩
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

end GlobalTheory.UPel.HT.Hecke.KerPol
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ h)).left).Gen, t.IsGen) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv) | (exact GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv) | (intros; apply GlobalTheory.UPel.HT.Hecke.KerPol.hecke_sections_triv <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTrace
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem linTrace_eq_neg_nextCoeff {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (g : Module.End F W) :
    LinearMap.trace F W g = -g.charpoly.nextCoeff := by
  classical
  let b := Module.finBasis F W
  rw [LinearMap.trace_eq_matrix_trace F b, Matrix.trace_eq_neg_charpoly_nextCoeff,
    LinearMap.charpoly_toMatrix]

theorem charpoly_map_vmap {K : Type} [Field K] (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (A : AbVar K)
    [Module.Finite ℚ_[l] (Vl l A)] (f : End A) :
    (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l f.asHom).charpoly := by
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  have key := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate K l hl A f ((charpoly f).map (algebraMap ℤ ℚ)) (hm.map _)
    (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
    (fun n => by
      rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
      simp)
  rw [← key, Polynomial.map_map]
  congr 1

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem charpoly_tate_det_trace :
    ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A),
      (∀ [Module.Finite ℚ_[l] (Vl l A)],
        (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l f.asHom).charpoly) ∧
      (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)],
        (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧
      LinearMap.det (vmap l f.asHom) = (deg f.asHom : ℚ_[l]) ∧
      LinearMap.trace ℚ_[l] _ (vmap l f.asHom) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  refine ⟨fun {_} => charpoly_map_vmap l hl A f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange]
    have hc : (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) = algebraMap ℤ ℚ_[l] := Subsingleton.elim _ _
    rw [hc]
    exact charpoly_map_vmap l hl A f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
      have h : (-f).asHom = -f.asHom := map_neg (End.addEquiv (X := A)) f
      simp only [h, vmap, map_neg, LinearMap.baseChange_neg, neg_one_smul, neg_neg]
    have hev := (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [Int.cast_zero, zero_sub, neg_neg] at hev
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← charpoly_map_vmap l hl A (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← charpoly_map_vmap l hl A f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTraceStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endCharpoly_tate_det_degree_trace : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), (∀ [Module.Finite ℚ_[l] (Vl l A)], (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f.asHom).charpoly) ∧ (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)], (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧ LinearMap.det (vmap l (A := A) (B := A) f.asHom) = (deg (A := A) (B := A) f.asHom : ℚ_[l]) ∧ LinearMap.trace ℚ_[l] _ (vmap l (A := A) (B := A) f.asHom) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  have hcharpoly [Module.Finite ℚ_[l] (Vl l A)] (g : End A) :
      (charpoly g).map (algebraMap ℤ ℚ_[l]) = (vmap l g.asHom).charpoly := by
    obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A g
    have h := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate
      K l hl A g ((charpoly g).map (algebraMap ℤ ℚ)) (hm.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
      (fun n => by simpa using congrArg (algebraMap ℤ ℚ) (hev n))
    rw [← h, Polynomial.map_map, show (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) =
      algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
  refine ⟨fun {_} => hcharpoly f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange,
      show (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) =
        algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
    exact hcharpoly f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
      simp [vmap, LinearMap.baseChange_neg]
    have hev : (charpoly (-f)).eval 0 = (deg f.asHom : ℤ) := by
      simpa using (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← hcharpoly (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← hcharpoly f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open GlobalTheory.ZM GlobalTheory.SiegelTor
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open IsLocalRing
open GlobalTheory.AbDual GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.CrysRed


open GlobalTheory.Published.GrothendieckMessing in
theorem exists_crysRed : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] (a : GlobalTheory.UPel.HT.OActN O A₀), ∃ red : Crys (divided₂ hsq) (spMap π) A₀ →ₛₗ[π] HdR A₀, Module.Finite C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Module.Projective C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Function.Surjective red ∧ (∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))) ∧ (∀ d y, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl A₀).Corr d y ↔ red d = y) ∧ (∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)) ∧ ∃ E' M : Submodule C (Crys (divided₂ hsq) (spMap π) A₀), IsCompl E' M ∧ ∀ y, y ∈ Fil A₀ ↔ ∃ d ∈ E', red d = y := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ hA₀ O _ a
  have hI2 : RingHom.ker π ^ 2 = ⊥ := hsq
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hI2] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  haveI : IsLocalRing C₀ := IsLocalRing.of_surjective' π hπ
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  obtain ⟨A', _, i', h', hA'⟩ := GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A' hA'
  have HC := (GD C (RingHom.ker π) κ hκ C₀ π hπ rfl).1
  obtain ⟨bij, ⟨N0, hN0⟩, hAdm⟩ := HC g A₀ A' i' h' hA' hg
  let e := LinearEquiv.ofBijective (crysToDR κ h') (HC.crysToDR_bijective h' hA' hg)
  have ee : ∀ xA, crysToDR κ h' (e.symm xA) = xA := e.apply_symm_apply
  letI : Algebra C C₀ := π.toAlgebra
  have hBC := (ADR.2.2.1 C A' g hA' hg C₀ A₀ i' h').1
  obtain ⟨hfinA, hprojA, -⟩ := ADR.1.prim hA' hg
  haveI := hfinA
  haveI := hprojA
  have hfin : Module.Finite C (Crys κ (spMap π) A₀) := Module.Finite.equiv e.symm
  have hproj : Module.Projective C (Crys κ (spMap π) A₀) := Module.Projective.of_equiv e.symm
  let red : Crys κ (spMap π) A₀ →ₛₗ[π] HdR A₀ := hBC.bcMap.comp (crysToDR κ h')
  have hm : ∀ x, (crysRedMor κ rfl A₀).Corr x (red x) := fun x ↦
    (corr_crysToDR_iff rfl h' bij.2 x (red x)).1 (by exact hBC.corr_iff.2 rfl)
  have hcorr : ∀ d y, (crysRedMor κ rfl A₀).Corr d y ↔ red d = y := fun d y ↦
    ⟨fun H ↦ by exact hBC.corr_iff.1 ((corr_crysToDR_iff rfl h' bij.2 d y).2 H), fun H ↦ H ▸ hm d⟩
  have hred : Function.Surjective red := by
    intro y
    let l : primDR A' →ₗ[C] C₀ :=
      { toFun c := y ((redMor h').pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨xA, hx⟩ := Module.projective_lifting_property (Algebra.linearMap C C₀) l hπ
    refine ⟨e.symm xA, ?_⟩
    show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
    rw [ee]
    exact hBC.corr_iff.1 fun c ↦ (LinearMap.congr_fun hx c).symm
  have hker : ∀ x, red x = 0 → x ∈ (RingHom.ker π) • (⊤ : Submodule C (Crys κ (spMap π) A₀)) := by
    intro x hx
    have hc := hBC.corr_iff.2 hx
    have hmem := GlobalTheory.BirigLift.mem_smul_top_of_forall_mem (RingHom.ker π) (crysToDR κ h' x) fun c ↦
      RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))
    have := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) hmem
    rw [Submodule.map_smul''] at this
    have ex : e.symm.toLinearMap (crysToDR κ h' x) = x := e.symm_apply_apply x
    rw [ex] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hact : ∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct κ (spMap π) a c d) =
      GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d) := by
    intro c d
    haveI := a.hom c
    refine (hcorr _ _).1 ?_
    rw [GlobalTheory.HTSummand.crysAct_apply, GlobalTheory.HTSummand.crysAct_apply]
    exact GrpMor.Corr.push (m := crysRedMor κ rfl A₀) (crysRedMor κ rfl A₀) (a.act c) (a.act c) (by simp) (hm d)
  have hFN : IsCompl (liftFil κ h') (N0.comap (crysToDR κ h')) :=
    (Submodule.orderIsoMapComap e).symm.isCompl hN0
  refine ⟨red, hfin, hproj, hred, hker, hcorr, hact, liftFil κ h', N0.comap (crysToDR κ h'), hFN, fun y ↦ ⟨?_, ?_⟩⟩
  · intro hy
    obtain ⟨xA, hxA, hc⟩ := (hAdm y).1 hy
    refine ⟨e.symm xA, ?_, ?_⟩
    · show crysToDR κ h' (e.symm xA) ∈ Fil A'
      rw [ee]; exact hxA
    · show hBC.bcMap (crysToDR κ h' (e.symm xA)) = y
      rw [ee]; exact hBC.corr_iff.1 hc
  · rintro ⟨d, hd, rfl⟩
    exact (hAdm (red d)).2 ⟨crysToDR κ h' d, hd, by exact hBC.corr_iff.2 rfl⟩

end GlobalTheory.CrysRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystalReductionSquareZeroArtinianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystal_reduction_squareZero_artinian : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ (O : Type) [Ring O] (a : GlobalTheory.UPel.HT.OActN O A₀), ∃ red : Crys (divided₂ hsq) (spMap π) A₀ →ₛₗ[π] HdR A₀, Module.Finite C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Module.Projective C (Crys (divided₂ hsq) (spMap π) A₀) ∧ Function.Surjective red ∧ (∀ x, red x = 0 → x ∈ RingHom.ker π • (⊤ : Submodule C (Crys (divided₂ hsq) (spMap π) A₀))) ∧ (∀ d y, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl A₀).Corr d y ↔ red d = y) ∧ (∀ (c : O) d, red (GlobalTheory.HTSummand.crysAct (divided₂ hsq) (spMap π) a c d) = GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) a c (red d)) ∧ ∃ E' M : Submodule C (Crys (divided₂ hsq) (spMap π) A₀), IsCompl E' M ∧ ∀ y, y ∈ Fil A₀ ↔ ∃ d ∈ E', red d = y := by
  first | exact @GlobalTheory.CrysRed.exists_crysRed | exact GlobalTheory.CrysRed.exists_crysRed | (intros; apply GlobalTheory.CrysRed.exists_crysRed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitOfClassicalPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitOfClassicalPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UTraitPt

theorem spMap_comp_eq {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem exists_embed_padicAlgCl (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (f : integralClosure ℤ_[p] K →+* W) (fK : FractionRing (integralClosure ℤ_[p] K) →+* FractionRing W)
    (hfin : f.Finite) (hfK : ∀ a, fK (algebraMap _ _ a) = algebraMap W (FractionRing W) (f a)) :
    ∃ (ι : FractionRing W →+* PadicAlgCl p) (j : W →+* OO p),
      (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W))) ∧
      (∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v)) ∧ IsLocalHom j ∧
      ∀ a, (j (f a) : PadicAlgCl p) = ((a : K) : PadicAlgCl p) := by
  let V₀ := integralClosure ℤ_[p] K
  letI : Algebra V₀ W := f.toAlgebra
  haveI : Module.Finite V₀ W := hfin
  haveI : IsFractionRing V₀ K := integralClosure.isFractionRing_of_finite_extension ℚ_[p] K
  let eK : K ≃ₐ[V₀] FractionRing V₀ := IsLocalization.algEquiv (nonZeroDivisors V₀) K (FractionRing V₀)
  letI : Algebra K (FractionRing W) := (fK.comp eK.toRingHom).toAlgebra
  have e : (algebraMap W (FractionRing W)).comp (algebraMap V₀ W) =
      (algebraMap K (FractionRing W)).comp (algebraMap V₀ K) := by
    refine RingHom.ext fun a => ?_
    show algebraMap W (FractionRing W) (f a) = fK (eK (algebraMap V₀ K a))
    rw [AlgEquiv.commutes, hfK]
  obtain ⟨K', hKK', hK', τ, f', hτK, hτW⟩ :=
    GlobalTheory.SS.exists_ringHom_integralClosure p K W (FractionRing W) e
  let ι : FractionRing W →+* PadicAlgCl p := K'.val.toRingHom.comp τ
  let j : W →+* OO p := (integralClosureToPadicAlgClIntegers K').comp f'
  have hj : ∀ v, (j v : PadicAlgCl p) = ι (algebraMap W (FractionRing W) v) := fun v => by
    dsimp [j, ι, integralClosureToPadicAlgClIntegers, RingHom.comp_apply]
    rw [← RingHom.comp_apply τ, hτW]; rfl
  have hball : ∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
    intro x
    constructor
    · intro hx
      have hint : IsIntegral ℤ_[p] (τ x) := (mem_integralClosure_padicInt_iff K' (τ x)).2 hx
      let ρ : ℤ_[p] →+* W := f.comp (algebraMap ℤ_[p] V₀)
      letI : Algebra ℤ_[p] W := ρ.toAlgebra
      have hτc : ∀ r : ℤ_[p], τ (algebraMap ℤ_[p] (FractionRing W) r) = algebraMap ℤ_[p] K' r := by
        intro r
        have h1 : algebraMap ℤ_[p] (FractionRing W) r =
            (algebraMap K (FractionRing W)) (algebraMap V₀ K (algebraMap ℤ_[p] V₀ r)) := by
          rw [IsScalarTower.algebraMap_apply ℤ_[p] W (FractionRing W)]
          exact congrArg (fun φ : V₀ →+* FractionRing W => φ (algebraMap ℤ_[p] V₀ r)) e
        rw [h1, ← RingHom.comp_apply τ, hτK]
        rfl
      let τa : FractionRing W →ₐ[ℤ_[p]] K' := { τ with commutes' := hτc }
      have hx' : IsIntegral ℤ_[p] x := (isIntegral_algHom_iff τa τ.injective).1 hint
      have hxW : IsIntegral W x := hx'.tower_top
      obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hxW
      exact ⟨w, hw⟩
    · rintro ⟨w, rfl⟩
      rw [← hj]
      exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 (j w).2
  refine ⟨ι, j, hball, hj, ⟨fun v hv => ?_⟩, fun a => ?_⟩
  · obtain ⟨u, hu⟩ := hv.exists_right_inv
    have hu' : ι (algebraMap W (FractionRing W) v) * (u : PadicAlgCl p) = 1 := by
      rw [← hj]; exact congrArg (fun z : OO p => (z : PadicAlgCl p)) hu
    have h0 : algebraMap W (FractionRing W) v ≠ 0 := by
      intro h0; rw [h0, map_zero, zero_mul] at hu'; exact zero_ne_one hu'
    have hinv : (algebraMap W (FractionRing W) v)⁻¹ ∈ Set.range (algebraMap W (FractionRing W)) := by
      rw [← hball, map_inv₀, ← eq_inv_of_mul_eq_one_right hu']
      exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 u.2
    obtain ⟨w, hw⟩ := hinv
    refine IsUnit.of_mul_eq_one (b := w) (IsFractionRing.injective W (FractionRing W) ?_)
    rw [map_mul, hw, map_one, mul_inv_cancel₀ h0]
  · rw [hj]
    have h1 : algebraMap W (FractionRing W) (f a) = algebraMap K (FractionRing W) (algebraMap V₀ K a) :=
      congrArg (fun φ : V₀ →+* FractionRing W => φ a) e
    show ((τ (algebraMap W (FractionRing W) (f a)) : K') : PadicAlgCl p) = _
    rw [h1, ← RingHom.comp_apply τ, hτK]
    rfl

end GlobalTheory.UTraitPt

namespace GlobalTheory.UTraitPt

theorem exists_lift_i {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (C : UCompact Xo c) (F : Type) [Field F]
    (g : Sp F ⟶ C.Z) (hg : Set.range g ⊆ Set.range C.i) : ∃ g' : Sp F ⟶ Xo.XF c, g' ≫ C.i = g := by
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  haveI := C.iF_open
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  haveI : IsPreimmersion (pullback.fst C.z (spMap C.b)) := inferInstance
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) :=
    (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  let pt : Sp F := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨x, hx⟩ := hg ⟨pt, rfl⟩
  let φ : C.o →+* F := (Spec.preimage (g ≫ C.z)).hom
  have hφ : spMap φ = g ≫ C.z := Spec.map_preimage _
  have hφi : Function.Injective φ := by
    have e : (spMap φ) pt = (spMap C.b) ((C.iF ≫ pullback.snd C.z (spMap C.b)) x) := by
      rw [hφ, Scheme.Hom.comp_apply, ← hx]
      show C.z ((C.iF ≫ pullback.fst C.z (spMap C.b)) x) = _
      rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.condition, ← Category.assoc]
      rfl
    have e2 : RingHom.ker φ = ⊥ := by
      have := congrArg PrimeSpectrum.asIdeal e
      have h1 : ((spMap φ) pt).asIdeal = RingHom.ker φ := by
        show Ideal.comap φ ⊥ = _
        rfl
      rw [h1] at this
      rw [this]
      haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) x).isPrime
      show Ideal.comap C.b _ = ⊥
      rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) x).asIdeal), Ideal.comap_bot_of_injective _ C.inj]
    exact (RingHom.injective_iff_ker_eq_bot φ).2 e2
  let ψ : c.F →+* F := IsFractionRing.lift hφi
  have hψ : ψ.comp C.b = φ := RingHom.ext fun a => IsFractionRing.lift_algebraMap hφi a
  have hsq : g ≫ C.z = spMap ψ ≫ spMap C.b := by
    rw [← hφ, ← hψ]; exact spMap_comp_eq _ _
  let g₁ : Sp F ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap ψ) hsq
  have hr : Set.range g₁ ⊆ Set.range C.iF := by
    rintro _ ⟨w, rfl⟩
    have hw : w = pt := Subsingleton.elim _ _
    subst hw
    refine ⟨x, hinj ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hx
  refine ⟨IsOpenImmersion.lift C.iF g₁ hr, ?_⟩
  show _ ≫ C.iF ≫ pullback.fst C.z (spMap C.b) = g
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

end GlobalTheory.UTraitPt

namespace GlobalTheory.UTraitPt

theorem exists_uTrait_of_classicalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i → ∃ (T : UTrait Xo c) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i := by
  intro E _ _ _ H Dw l Xo c C X₁ Y πY p _ y hy
  haveI : Algebra.FiniteType ℤ X₁.o₁ := X₁.ar.ft
  haveI := Y.lft
  haveI hSpecZ : LocallyOfFiniteType (spMap (algebraMap ℤ X₁.o₁)) := by
    show LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ X₁.o₁)))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨K, hK, hKall⟩ := padicAlgCl_integral_points.2 Y.Z (Y.s ≫ spMap (algebraMap ℤ X₁.o₁)) p y
  haveI : FiniteDimensional ℚ_[p] K := hK
  obtain ⟨j₀, y₀, hj₀, -, hy₀⟩ := hKall K le_rfl
  let V₀ := integralClosure ℤ_[p] K
  haveI hdvr : IsDiscreteValuationRing V₀ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] K
  haveI : Module.Finite ℤ_[p] V₀ := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsAdicComplete (maximalIdeal V₀) V₀ := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] _
  haveI : CharZero V₀ := inferInstance
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

  have hj₀i : Function.Injective ((OO p).subtype.comp j₀) := by
    intro a b h
    have h' : ((a : K) : PadicAlgCl p) = ((b : K) : PadicAlgCl p) := by
      rw [← hj₀, ← hj₀]; exact h
    exact Subtype.ext (Subtype.ext h')
  obtain ⟨e₀, he₀'⟩ : ∃ e₀ : FractionRing V₀ →+* PadicAlgCl p,
      ∀ a, e₀ (algebraMap V₀ (FractionRing V₀) a) = ((OO p).subtype.comp j₀) a :=
    ⟨IsFractionRing.lift hj₀i, fun a => IsFractionRing.lift_algebraMap hj₀i a⟩
  have he₀ : e₀.comp (algebraMap V₀ (FractionRing V₀)) = (OO p).subtype.comp j₀ := RingHom.ext he₀'
  have hgy : gPt p ≫ y = spMap e₀ ≫ jK V₀ ≫ y₀ := by
    rw [← hy₀, ← Category.assoc, ← Category.assoc]
    congr 1
    show spMap (OO p).subtype ≫ spMap j₀ = spMap e₀ ≫ spMap (algebraMap V₀ (FractionRing V₀))
    rw [← spMap_comp_eq, ← spMap_comp_eq, he₀]
  let gen₀ : Sp (FractionRing V₀) ⟶ C.Z := jK V₀ ≫ y₀ ≫ πY ≫ X₁.π
  have hgen : Set.range gen₀ ⊆ Set.range C.i := by
    rintro _ ⟨w, rfl⟩
    let q : Sp (PadicAlgCl p) := ⟨⊥, Ideal.isPrime_bot⟩
    have hw : w = (spMap e₀) q := Subsingleton.elim _ _
    apply hy
    refine ⟨q, ?_⟩
    rw [hw, ← Scheme.Hom.comp_apply]
    congr 1
    rw [← Category.assoc, hgy]
    simp only [gen₀, Category.assoc]
  obtain ⟨yK, hyK⟩ := exists_lift_i C (FractionRing V₀) gen₀ hgen
  obtain ⟨T, f, fK, -, -, hfin, hfK, hTy⟩ := GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V₀ hB hdvr yK
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  obtain ⟨ι, j, hball, hj, hloc, hjf⟩ := exists_embed_padicAlgCl p K T.V f fK hfin hfK
  refine ⟨T, ι, j, spMap f ≫ y₀, hball, hj, hloc, ?_, ?_⟩
  · have hjf' : j.comp f = j₀ := RingHom.ext fun a => Subtype.ext ((hjf a).trans (hj₀ a).symm)
    rw [← Category.assoc, ← spMap_comp_eq, hjf', hy₀]
  · have hc : jK T.V ≫ spMap f = spMap fK ≫ jK V₀ := by
      show spMap (algebraMap T.V (FractionRing T.V)) ≫ spMap f = spMap fK ≫ spMap (algebraMap V₀ (FractionRing V₀))
      rw [← spMap_comp_eq, ← spMap_comp_eq]
      congr 1
      exact RingHom.ext fun a => (hfK a).symm
    rw [hTy, Category.assoc (spMap fK), hyK]
    simp only [gen₀, ← Category.assoc]
    rw [hc]

end GlobalTheory.UTraitPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitOfClassicalPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryTrait_of_classicalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i → ∃ (T : UTrait Xo c) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ C.i := by
  first | exact @GlobalTheory.UTraitPt.exists_uTrait_of_classicalPoint | exact GlobalTheory.UTraitPt.exists_uTrait_of_classicalPoint | (intros; apply GlobalTheory.UTraitPt.exists_uTrait_of_classicalPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionAtBoundaryPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionAtBoundary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdLocalExt

theorem exists_extension_of_smooth {A : CommRingCat.{0}} [IsRegularRing A] {X Y : Scheme.{0}} (p : X ⟶ Spec A) [Smooth p]
    [QuasiCompact p] (u : Y ⟶ X) [IsOpenImmersion u] (L : LB Y) (hL : L.IsLB) :
    ∃ M : LB X, M.IsLB ∧ LBIso (M.pull u) L := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI : Smooth (show X ⟶ Spec (CommRingCat.of A) from p) := ‹Smooth p›
    haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth A p x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) := IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩
  exact GlobalTheory.exists_lineBundle_extension_of_isDomain X Y u inferInstance (fun x => (h x).1) (fun x => (h x).2) L hL

theorem exists_extension_stalk {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ M : LB (pullback g (S.fromSpecStalk x)), M.IsLB ∧
      LBIso (M.pull (pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp)))
        (L.pull (pullback.fst (e ≫ g) (S.fromSpecStalk x))) := by
  haveI : IsRegularRing (S.presheaf.stalk x) := GlobalTheory.isRegularRing_of_isRegularLocalRing _
  exact exists_extension_of_smooth (pullback.snd g (S.fromSpecStalk x)) _ _ (pull_isLB hL _)

end GlobalTheory.BdLocalExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionAtBoundaryPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdStalkExt

theorem exists_extension_test {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ N : LB (pullback g (S.fromSpecStalk x)), N.IsLB ∧
      ∀ (T : Scheme.{0}) (a : T ⟶ pullback g (S.fromSpecStalk x)) (b : T ⟶ Y),
        a ≫ pullback.fst g (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (L.pull b) := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.BdLocalExt.exists_extension_stalk g e x L hL
  refine ⟨N, hN, fun T a b hab => ?_⟩
  let t : T ⟶ pullback (e ≫ g) (S.fromSpecStalk x) :=
    pullback.lift b (a ≫ pullback.snd g (S.fromSpecStalk x)) (by
      rw [← Category.assoc, ← hab, Category.assoc, Category.assoc, pullback.condition])
  have ha : a = t ≫ pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · rw [hab, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hb : b = t ≫ pullback.fst (e ≫ g) (S.fromSpecStalk x) := (pullback.lift_fst _ _ _).symm
  exact LBIso.chartPull (chartPullSame N _ _ _ t fun _ => ha) (chartPullSame L _ _ _ t fun _ => hb) h

theorem exists_extension_at_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ x : S, x ∉ Set.range j → ∃ N : LB (pullback G.hom (S.fromSpecStalk x)), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ pullback G.hom (S.fromSpecStalk x)) (b : T ⟶ tF.G.left), a ≫ pullback.fst G.hom (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (tF.PP.L.pull b) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU hpre tF _ G _ _ e hsa he _ x hx
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := hU
  haveI := hsa.smooth
  haveI := hsa.quasiCompact
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨k, _, m, n, C, ξ, a, -, -, rfl, het, -⟩ := hpre x hx
  haveI : IsRegularLocalRing (ChartRing k m n) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
  haveI : IsRegularLocalRing (S.presheaf.stalk (ξ (closedPoint _))) :=
    (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ het).1
  haveI : IsOpenImmersion e := MorphismProperty.of_isPullback (P := @IsOpenImmersion) he.1.flip inferInstance
  exact exists_extension_test G.hom e _ tF.PP.L tF.PP.isLB

end GlobalTheory.BdStalkExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionAtBoundaryPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_extension_at_boundaryPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ x : S, x ∉ Set.range j → ∃ N : LB (pullback G.hom (S.fromSpecStalk x)), N.IsLB ∧ ∀ (T : Scheme.{0}) (a : T ⟶ pullback G.hom (S.fromSpecStalk x)) (b : T ⟶ tF.G.left), a ≫ pullback.fst G.hom (S.fromSpecStalk x) = b ≫ e → LBIso (N.pull a) (tF.PP.L.pull b) := by
  first | exact @GlobalTheory.BdStalkExt.exists_extension_at_boundary | exact GlobalTheory.BdStalkExt.exists_extension_at_boundary | (intros; apply GlobalTheory.BdStalkExt.exists_extension_at_boundary <;> assumption)
end
end
