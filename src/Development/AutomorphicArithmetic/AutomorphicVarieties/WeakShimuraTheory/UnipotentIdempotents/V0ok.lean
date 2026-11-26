module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.CbFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.V0ok
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.v0ok :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (Y : SetD T) (V : Y.s.Lev), D.Good → ∀ r : W.Resid V.frame c'.O 4, (∀ i (g : G T.L Ω), r.chib i (V.pr g) = X.cb i g) → r.V0ok := by
  intro Ω _ _ _ l _ c D T c' h X Y V hD r hr
  haveI : IsLocalHom (inc h) := (UpperTheory.V.Ws.P1.coefRes c).2.2.1 c' h
  have hres : ∀ x : c.O, residue c'.O (inc h x) = ResidueField.map (inc h) (residue c.O x) := fun x =>
    (ResidueField.map_residue _ x).symm
  refine ⟨?_, ?_, ?_⟩
  · rintro i _ ⟨g, hg, rfl⟩
    exact MonoidHom.mem_ker.2 ((hr i g).trans (MonoidHom.mem_ker.1 ((cbFacts X hD).2.1 i _ Y.away0 hg)))
  · rintro _ ⟨g, hg, rfl⟩ i j
    refine (hr i g).trans (Eq.trans (Units.ext ?_) (hr j g).symm)
    rw [X.cb_val, X.cb_val, map_mul, map_mul, hres, hres]
    exact congrArg (fun x => residue c'.O (X.κ g) * ResidueField.map (inc h) x) (Y.eq0 g hg i j)
  · obtain ⟨g, hg, hne⟩ := Y.om0
    refine ⟨V.pr g, ⟨g, hg, rfl⟩, fun h' => hne ?_⟩
    have h1 := (prFacts l T.L Ω Y.s V).2.2.1 c'.O (ResidueField c'.O) g
    rw [h', Units.val_one] at h1
    have h2 : (chiO T.L Ω l c'.O g : c'.O) = inc h (chiO ℚ Ω l c.O (resQ T.L g)) := rfl
    rw [hD.om_bar]
    apply (ResidueField.map (inc h)).injective
    rw [map_one, Raw.bar, ← hres, ← h2]
    exact h1.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.ResidEx
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Descend
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.descend :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (M : Type) [Group M] (χ : G L Ω →* M), IsOpen (χ.ker : Set (G L Ω)) → (∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ V.S' → Ine (F := L) A ≤ χ.ker) → ∃ χ' : V.frame.G₀ →* M, IsOpen (χ'.ker : Set V.frame.G₀) ∧ ∀ g, χ' (V.pr g) = χ g := by
  intro l _ L Ω _ _ _ _ _ _ s V M _ χ hopen hine
  obtain ⟨hsurj, hquot, hker⟩ := phiKer V
  have hle : V.pr.ker ≤ χ.ker := hker χ.ker (Subgroup.isClosed_of_isOpen _ hopen) hine
  let χ₀ : ↥V.η.ker →* M :=
    (QuotientGroup.lift V.pr.ker χ hle).comp
      (QuotientGroup.quotientKerEquivOfSurjective V.pr hsurj).symm.toMonoidHom
  have hcomp : ∀ g, χ₀ (V.pr g) = χ g := by
    intro g
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective V.pr hsurj).symm (V.pr g) =
        (QuotientGroup.mk g : G L Ω ⧸ V.pr.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [χ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, QuotientGroup.lift_mk]
  have hpre : (V.pr : G L Ω → ↥V.η.ker) ⁻¹' (χ₀.ker : Set ↥V.η.ker) = (χ.ker : Set (G L Ω)) := by
    ext g
    simp [MonoidHom.mem_ker, hcomp]
  have hop : IsOpen (χ₀.ker : Set ↥V.η.ker) := hquot.isOpen_preimage.mp (hpre ▸ hopen)
  exact ⟨χ₀, hop, hcomp⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.WtRoot
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem wt_root : ∀ i j : Fin 4, i ≠ j → wt i j ∈ roots := by
  decide

private theorem rt_wt' {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = (Φ.χ 0 g)⁻¹ * (Φ.χ 1 g * Φ.χ 2 g) := eq_inv_mul_of_mul_eq h
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    apply Additive.ofMul.injective <;> simp <;> abel

theorem UpperTheory.V.Ws.Lk.cbInj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h), T.Ok → Function.Injective X.cb := by
  intro Ω _ _ _ l _ c D T c' h X hT i j hij
  by_contra hne
  obtain ⟨g, hgL, hg⟩ := hT.g3 _ (wt_root i j hne)
  obtain ⟨g', rfl⟩ := ((galEq T).2.2 g).1 hgL
  have hrel : (T.fr ∅).χ 0 (resLe T.F_le g') * (T.fr ∅).χ 3 (resLe T.F_le g') =
      (T.fr ∅).χ 1 (resLe T.F_le g') * (T.fr ∅).χ 2 (resLe T.F_le g') := by
    simp only [Tower.fr, MonoidHom.coe_comp, Function.comp_apply, chi]
    cases T.pr <;> simp [lab, Raw.ps, Raw.th, mul_comm]
  have key := rt_wt' (T.fr ∅) (resLe T.F_le g') hrel i j
  have hcb := congrArg (fun φ => ((φ g' : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hij
  simp only [OCh.cb_val] at hcb
  simp only [Tower.rb] at hg
  set r := (T.fr ∅).rt (wt i j) (resLe T.F_le g') with hr_def
  have key' : ((r : c.O) * (chi D T.pr j (resQ T.L g') : c.O)) = (chi D T.pr i (resQ T.L g') : c.O) := by
    rw [← Units.val_mul]
    exact congrArg Units.val key
  rw [← key'] at hcb
  simp only [map_mul] at hcb
  have hu1 : residue c'.O (X.κ g' : c'.O) ≠ 0 := ((X.κ g').isUnit.map (residue c'.O)).ne_zero
  have hu2 : residue c'.O (inc h (chi D T.pr j (resQ T.L g') : c.O)) ≠ 0 :=
    (((chi D T.pr j (resQ T.L g')).isUnit.map (inc h)).map (residue c'.O)).ne_zero
  have hr : residue c'.O (inc h (r : c.O)) = 1 := by
    have h1 := mul_left_cancel₀ hu1 hcb
    exact mul_right_cancel₀ hu2 (h1.trans (one_mul _).symm)
  apply hg
  by_contra hne1
  have hmem : (r : c.O) - 1 ∉ maximalIdeal c.O := by
    intro hm
    apply hne1
    rw [← sub_eq_zero, ← map_one (residue c.O), ← map_sub]
    exact (residue_eq_zero_iff _).2 hm
  have hunit : IsUnit ((r : c.O) - 1) := by
    by_contra hn
    exact hmem ((mem_maximalIdeal _).2 hn)
  have hu := (hunit.map (inc h)).map (residue c'.O)
  rw [map_sub, map_sub, map_one, map_one, hr, sub_self] at hu
  exact not_isUnit_zero hu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.StarOp
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.polar :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (χ : Fin n → F.G₀ →* Rˣ) (π : Equiv.Perm (Fin n)), (∀ i g, χ i (F.conj g) * χ (π i) g * F.eps O R g ^ ((n : ℤ) - 1) = 1) → F.IsPolar O (W.GDet.ofRep (W.diagRep χ)) := by
  intro l _ F O _ _ R _ _ n χ π hχ B _ _ _ _ y
  let Ψ : Fin n → MonoidAlgebra B F.G₀ →ₐ[B] B := fun i =>
    MonoidAlgebra.lift B B F.G₀ ((Units.coeHom B).comp (W.pushCh (algebraMap R B) (χ i)))
  have hrep : ∀ z, W.GDet.repAlg (W.diagRep χ) B z = Matrix.diagonal (fun i => Ψ i z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), ha, hb, Matrix.diagonal_add]
      congr 1
      funext i
      rw [map_add (f := _)]
    | single g b =>
      simp only [W.GDet.repAlg, MonoidAlgebra.lift_single, Ψ]
      ext i j
      simp [W.diagRep, W.pushCh, Matrix.diagonal_apply]
  have hst : ∀ i z, Ψ i (F.star O B n z) = Ψ (π i) z := by
    intro i z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp [W.GFrame.star]
    | add a b ha hb =>
      simp only [W.GFrame.star, map_add (f := _), MulOpposite.unop_add] at ha hb ⊢
      rw [ha, hb]
    | single g b =>
      simp only [W.GFrame.star, W.GFrame.starOp, MonoidAlgebra.lift_single, Ψ]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op, map_smul,
        MonoidAlgebra.lift_single, MonoidHom.comp_apply, Units.coeHom_apply, W.pushCh, Units.coe_map,
        smul_eq_mul]
      congr 1
      have he : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
        ext
        simp [W.GFrame.eps, W.pushCh, IsScalarTower.algebraMap_apply O R B]
      have key : F.eps O R g ^ (1 - (n : ℤ)) * χ i (F.conj g)⁻¹ = χ (π i) g := by
        have h := hχ i g
        have hb : χ (π i) g = ((χ i) (F.conj g) * F.eps O R g ^ ((n : ℤ) - 1))⁻¹ := by
          rw [eq_inv_iff_mul_eq_one, mul_left_comm, ← mul_assoc]
          exact h
        rw [hb, mul_inv, show (1 : ℤ) - n = -((n : ℤ) - 1) by ring, zpow_neg, map_inv, mul_comm]
      rw [he, ← map_zpow, Units.coe_map, ← key, Units.val_mul]
      simp
  show Matrix.det (W.GDet.repAlg (W.diagRep χ) B (F.star O B n y)) =
    Matrix.det (W.GDet.repAlg (W.diagRep χ) B y)
  rw [hrep, hrep, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [hst]
  exact Equiv.prod_comp π (fun i => Ψ i y)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.residEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (Y : SetD T) (V : Y.s.Lev), D.Good → T.Ok → V.S' = Y.s.S → ∃ r : W.Resid V.frame c'.O 4, (∀ i (g : G T.L Ω), r.chib i (V.pr g) = X.cb i g) ∧ (∀ (v : W.Vl l T.L) i (g : Dec (F := T.L) (Y.s.A v)), r.psib v i g = r.chib i (V.pr g)) ∧ (∀ v i, r.th v i = 1) := by
  intro Ω _ _ _ l _ c D T c' h X Y V hG hT hS
  have hcb := cbFacts X hG
  have hpr := prFacts l T.L Ω Y.s V
  have hd : ∀ i, ∃ χ : V.η.ker →* (ResidueField c'.O)ˣ, IsOpen (χ.ker : Set V.η.ker) ∧
      ∀ g, χ (V.pr g) = X.cb i g := fun i =>
    descend l T.L Ω Y.s V _ (X.cb i) (hcb.1 i)
      (fun A v hA hv => hcb.2.1 i A (Y.away A v hA (by rwa [hS] at hv)))
  choose χ hχo hχ using hd
  have hinj : Function.Injective χ := by
    intro i j hij
    apply cbInj X hT
    exact MonoidHom.ext fun g => by rw [← hχ, ← hχ, hij]
  have hpol : V.frame.IsPolar c'.O (W.GDet.ofRep (W.diagRep χ)) := by
    apply polar V.frame c'.O (ResidueField c'.O) 4 χ Fin.revPerm
    intro i g
    obtain ⟨g1, rfl⟩ := hpr.1 g
    obtain ⟨g', hg', hconj⟩ := hpr.2.1 g1
    obtain ⟨σ, hσ, hσc⟩ := Y.cc
    have key := hcb.2.2 σ hσ g1 g' (hσc g1 g' hg') i
    have heps := hpr.2.2.1 c'.O (ResidueField c'.O) g1
    rw [hconj]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Fin.revPerm_apply]
    erw [hχ i g', hχ i.rev g1, heps, IsLocalRing.ResidueField.algebraMap_eq]
    have e3 : ((4 : ℕ) : ℤ) - 1 = ((3 : ℕ) : ℤ) := by norm_num
    rw [e3, zpow_natCast]
    exact key
  refine ⟨W.Resid.mk χ hχo hinj hpol (fun v i => (χ i).comp (V.frame.φ v)) ?_ (fun _ _ => 1)
    (fun _ _ _ _ => rfl), fun i g => hχ i g, fun v i g => rfl, fun v i => rfl⟩
  intro v i
  exact (hχo i).preimage (V.frame.φ_cont v)
end
