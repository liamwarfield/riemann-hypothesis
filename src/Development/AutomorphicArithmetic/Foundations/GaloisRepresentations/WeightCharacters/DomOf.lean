module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.NeatOfPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DomOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.dom_of :
    UpperTheory.Gal.Wt.Dom := by
  classical
  intro a κ f hf
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ a a κ.natW := hf
  clear hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ a a κ.natW] at hf'
  induction hf' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hx
    intro m hm k
    have h := (Formalism.GradedWeylDivisibility.bidetDominance ℂ a a K sz hsz I m hm).1 k
    rw [hshape] at h
    exact h
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm k
    rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
    · exact hx m h k
    · exact hy m h k
  | smul c x _ hx =>
    intro m hm k
    exact hx m (MvPolynomial.support_smul hm) k
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EvLemOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.evLem_of :
    UpperTheory.Gal.Wt.EvLem := by
  intro M X Z _ _ _ ev hsep T Φ hT L
  let W : Submodule ℂ (Module.Dual ℂ M) := Submodule.span ℂ (Set.range ev)
  have hbot : W.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    rw [Submodule.mem_dualCoannihilator] at hm
    exact (Submodule.mem_bot ℂ).2 (hsep m fun x => hm _ (Submodule.subset_span ⟨x, rfl⟩))
  have htop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hbot, Submodule.dualAnnihilator_bot]
  let φ : Module.Dual ℂ M →ₗ[ℂ] (Z → ℂ) :=
    { toFun := fun l z => l (Φ z)
      map_add' := fun a b => by
        ext z
        simp
      map_smul' := fun c a => by
        ext z
        simp }
  have hle : W ≤ T.comap φ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact hT x
  have hL : L ∈ W := by
    rw [htop]
    exact Submodule.mem_top
  exact hle hL
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EllCOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.ellC_of :
    UpperTheory.Gal.Wt.EllC := by
  intro E _ _ _ a C hC hneat
  set D : Subgroup (UA E a) := C ⊔ infU E a with hDdef
  have hDC : D ≤ C.comap GlobalTheory.EllU.finPart := sup_le (fun c hc => by
      change GlobalTheory.EllU.finPart c ∈ C
      rw [GlobalTheory.EllU.finPart_of_finU (hC hc)]; exact hc)
    (fun x hx => by
      change GlobalTheory.EllU.finPart x ∈ C
      rw [GlobalTheory.EllU.finPart_of_infU hx]; exact C.one_mem)
  let f : D →* C := (GlobalTheory.EllU.finPart.comp D.subtype).codRestrict C (fun d => hDC d.2)
  have hyp : ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ d : D, γ * g = g * d → f d = 1 := by
    intro g γ hγ d h
    have hfd : GlobalTheory.EllU.finPart (d : UA E a) ∈ C := hDC d.2
    have e : γ * g = g * GlobalTheory.EllU.finPart (d : UA E a) * ((GlobalTheory.EllU.finPart (d : UA E a))⁻¹ * (d : UA E a)) := by
      rw [h]; group
    have h1 := hneat g γ hγ _ hfd _ (GlobalTheory.EllU.inv_finPart_mul_mem (d : UA E a)) e
    exact Subtype.ext h1
  obtain ⟨ℓ, h1, h2⟩ := UpperTheory.Gal.Gen.ellGrp_holds (UA E a) C (ratU E a) D f hyp
  have hinf : ∀ x ∈ infU E a, ∀ g, ℓ (g * x) = ℓ g := by
    intro x hx g
    have e : f ⟨x, le_sup_right (a := C) hx⟩ = 1 := Subtype.ext (GlobalTheory.EllU.finPart_of_infU hx)
    have := h2 g ⟨x, le_sup_right (a := C) hx⟩
    simp only [e, mul_one] at this
    exact this
  have hC' : ∀ (c : C) g, ℓ (g * c) = ℓ g * c := by
    intro c g
    have e : f ⟨c, le_sup_left (b := infU E a) c.2⟩ = c := Subtype.ext (GlobalTheory.EllU.finPart_of_finU (hC c.2))
    have := h2 g ⟨c, le_sup_left (b := infU E a) c.2⟩
    simp only [e] at this
    exact this
  exact ⟨ℓ, ⟨h1, hC', hinf⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutMul
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem RU_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (x : UA E a) (φ ψ : UA E a → ℂ) :
    RU E a x (fun g => φ g * ψ g) = RU E a x φ * RU E a x ψ := by
  ext g
  rfl

theorem UpperTheory.Gal.Wt.autMul_of :
    UpperTheory.Gal.Wt.AutMul := by
  intro E _ _ _ a φ ψ hφ hψ
  refine ⟨hφ.cont.mul hψ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change φ (γ * g) * ψ (γ * g) = φ g * ψ g
    rw [hφ.left γ hγ, hψ.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E a).comp (finU (E := E) (n := a)).subtype) (fun g => φ g * ψ g) ?_
    refine Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E a 1 φ = φ
      simp
    · change RU E a 1 ψ = ψ
      simp
    · have h1 : RU E a k φ = φ := hk.1
      have h2 : RU E a k ψ = ψ := hk.2
      change RU E a k (fun g => φ g * ψ g) = fun g => φ g * ψ g
      rw [RU_mul', h1, h2]
      rfl
  · haveI := hφ.kfin
    haveI := hψ.kfin
    have f1 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    have f2 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) :=
      Submodule.fg_iff_finiteDimensional _ |>.1 (f1.mul f2)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E a k (fun g => φ g * ψ g) ∈ _
    rw [RU_mul']
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NeatLev
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.neatLev_of :
    UpperTheory.Gal.Wt.NeatLev := by
  intro E _ _ _ l hl a ha w₀ hmem hs v' hv' hap K hK hint Kv hKv W f hf
  obtain ⟨N, hN, hNf⟩ := UpperTheory.Gal.Gen.smoothAt_holds E a w₀ hs W f
  obtain ⟨J, hJ, hJN, hJt, -⟩ := UpperTheory.Gal.Gen.tower_holds E w₀ a l hl hmem ha N hN
  obtain ⟨hLev, hmemC, hcJ, -, -, -⟩ :=
    UpperTheory.Gal.Gen.levFacts_holds E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hKC : K ≤ UpperTheory.Gal.Gen.lev K w₀ (J 0) := le_sup_left
  refine ⟨UpperTheory.Gal.Gen.lev K w₀ (J 0), hLev, hKC, ?_, ?_, ?_⟩
  · intro g γ hγ c hc x hx h
    have hT : UpperTheory.Gal.CharacterCongruences.TorsFreeAt (UpperTheory.Gal.Gen.lev K w₀ (J 0)) w₀ :=
      fun k hk ho => hJt _ (hcJ k hk) ho
    exact UpperTheory.Gal.CharacterCongruences.neatOfPlace_holds E a _ ⟨hLev.fin, hLev.compact, hLev.isOpen⟩ w₀ hT
      g γ hγ c hc x hx h
  · have hKGL : GlobalTheory.LFun.KGL v' (n := a) ≤ (UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v') := by
      intro y hy
      obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a v' hv'
      have hy' : cLoc v' (e.symm y : UA E a) = y := by rw [← he]; simp
      exact ⟨(e.symm y : UA E a), hKC (hint _ (e.symm y).2 (hy'.symm ▸ hy)), hy'⟩
    have hmax := UpperTheory.Gal.Gen.maxCpt_holds E v' a ((UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v'))
      (cLoc v' '' (UpperTheory.Gal.Gen.lev K w₀ (J 0) : Set (UA E a)))
      (hLev.compact.image (GlobalTheory.BCT.GlobLev.continuous_cLoc v'))
      (fun _ h => h) hKGL
    intro c hc
    exact hmax ⟨c, hc, rfl⟩
  · intro c hc v g
    obtain ⟨hcC, hcv⟩ := hc
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (hmemC _).1 hcC
    have hx1 : cLoc v' x = 1 :=
      MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v') hap)
    have hkv : k ∈ K ⊓ Kv.comap (cLoc v') := by
      refine ⟨hk, ?_⟩
      have h2 : cLoc v' (k * x) ∈ Kv := hcv
      rw [map_mul, hx1, mul_one] at h2
      exact h2
    rw [← mul_assoc, hNf x hx (hJN hxJ) v (g * k)]
    exact hf k hkv v g
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.twist_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.Twist := by
  intro hA E _ _ _ a C hC ℓ hℓ W f c
  let e : UA E a → UA E a := fun g => (((ℓ g)⁻¹ * c : C) : UA E a)
  have he : ∀ g, e g ∈ finU (E := E) (n := a) := fun g => hC.fin ((ℓ g)⁻¹ * c).2
  let F : W.Sp →ₗ[ℂ] (UA E a → ℂ) :=
    { toFun := fun v g => f.1 v (g * e g)
      map_add' := fun v w => by funext g; simp
      map_smul' := fun r v => by funext g; simp }
  have hF : ∀ v g, F v g = f.1 v (g * e g) := fun _ _ => rfl
  have hleft : ∀ γ ∈ ratU E a, ∀ v g, F v (γ * g) = F v g := by
    intro γ hγ v g
    have h : e (γ * g) = e g := by simp only [e, hℓ.left γ hγ g]
    rw [hF, hF, h, mul_assoc]
    exact (f.2.1 v).left γ hγ _
  have hlev : ∀ k ∈ C, ∀ v g, F v (g * k) = F v g := by
    intro k hk v g
    have h : g * k * e (g * k) = g * e g := by
      simp only [e, hℓ.lev ⟨k, hk⟩ g, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hF, hF, h]
  have hinf : ∀ x ∈ infU E a, ∀ v g, F v (g * x) = f.1 v (g * x * e g) := by
    intro x hx v g
    have h : e (g * x) = e g := by simp only [e, hℓ.inf x hx g]
    rw [hF, h]
  have heqv : ∀ (x : infU E a) v, F (W.rep x v) = RU E a x (F v) := by
    intro x v
    funext g
    rw [RU_apply, hinf x x.2, hF, f.2.2 x v, RU_apply, mul_assoc g, mul_assoc g, fin_mul_inf (he g) x.2]
  have haut : ∀ v, IsAutFormU (F v) := by
    intro v
    refine hA E a C hC (F v) (fun γ hγ g => hleft γ hγ v g) (fun k hk g => hlev k hk v g) ?_
      (LinearMap.range F) inferInstance fun x hx => ⟨W.rep ⟨x, hx⟩ v, heqv ⟨x, hx⟩ v⟩
    intro g
    have h : (fun x : infU E a => F v (g * x)) = fun x : infU E a => f.1 v (g * x * e g) :=
      funext fun x => hinf x x.2 v g
    rw [h]
    exact (f.2.1 v).cont.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  exact ⟨⟨F, haut, heqv⟩, UpperTheory.Gal.Gen.mem_fixedBy.2 fun k hk v g => hlev k hk v g, fun _ _ => rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopUpOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.topUp_of :
    UpperTheory.Gal.Wt.TopUp := by
  intro a κ b hb
  have hbt : (b : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := fun i j h => hb i j h
  have hdiag : ∀ i, (b : Matrix (Fin a) (Fin a) ℂ) i i ≠ 0 := by
    have hdet : (b : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
    rw [Matrix.det_of_upperTriangular hbt] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  let t : Fin a → ℂˣ := fun i => Units.mk0 _ (hdiag i)
  set D := diagGL ℂ a t with hD
  set u := D⁻¹ * b with hu
  have hbu : b = D * u := by rw [hu, mul_inv_cancel_left]
  have hDinv : ((D⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal fun i => (((t i)⁻¹ : ℂˣ) : ℂ) := rfl
  have hucoe : (u : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal (fun i => (((t i)⁻¹ : ℂˣ) : ℂ)) * (b : Matrix (Fin a) (Fin a) ℂ) := by
    rw [hu, Units.val_mul, hDinv]
  have hut : (u : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := by
    rw [hucoe]
    exact (Matrix.blockTriangular_diagonal _).mul hbt
  have hu1 : ∀ i, (u : Matrix (Fin a) (Fin a) ℂ) i i = 1 := by
    intro i
    rw [hucoe, Matrix.diagonal_mul]
    simp [t, hdiag i]
  have hfix : (sqRep ℂ a κ u) (top κ) = top κ := by
    apply Subtype.ext
    exact (factSqHighestWeight ℂ a κ).2 u hut hu1
  have hscal : (sqRep ℂ a κ D) (top κ) = chi κ b • top κ := by
    apply Subtype.ext
    have h := (factSqHighestWeight ℂ a κ).1 t
    have hc : (((∏ i, t i ^ κ.w i : ℂˣ)) : ℂ) = chi κ b := by
      rw [Units.coe_prod]
      simp only [Units.val_zpow_eq_zpow_val, chi, t, Units.val_mk0]
    rw [hc] at h
    exact h
  calc (sqRep ℂ a κ b) (top κ) = (sqRep ℂ a κ D) ((sqRep ℂ a κ u) (top κ)) := by
        rw [hbu, map_mul, Module.End.mul_apply]
    _ = chi κ b • top κ := by rw [hfix, hscal]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SumRep
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.sumRep_of :
    UpperTheory.Gal.Wt.SumRep := by
  intro E _ _ _ a S hfin hS
  classical
  obtain ⟨B₀, -, -, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E a
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (autU E a).subtype (autU E a).ker_subtype
  have hpv : ∀ (φ : UA E a → ℂ) (h : IsAutFormU φ), p φ = ⟨φ, h⟩ := fun φ h =>
    LinearMap.congr_fun hp (⟨φ, h⟩ : autU E a)
  let B : (UA E a → ℂ) →ₗ⋆[ℂ] (UA E a → ℂ) →ₗ[ℂ] ℂ := (B₀.compl₂ p).comp p
  have hB : ∀ φ φ', B φ φ' = B₀ (p φ) (p φ') := fun _ _ => rfl
  have hsum : ∀ φ : UA E a → ℂ, IsAutFormU φ → φ ∈ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U} := by
    intro φ hφ
    have h := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E a B (fun f hf h0 => by
        rw [hB, hpv f hf] at h0
        exact congrArg Subtype.val (hd _ h0))
      (fun x f g hf hg => by
        rw [hB, hB, hpv f hf, hpv g hg, hpv _ (RU_mem_autU x f hf), hpv _ (RU_mem_autU x g hg)]
        exact hi x ⟨f, hf⟩ ⟨g, hg⟩) φ hφ
    exact (iSup_le fun σ => le_sSup σ.2 : _ ≤ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) h
  let b := Module.finBasis ℂ S
  have hex : ∀ i, ∃ s : Finset (Submodule ℂ (UA E a → ℂ)), (↑s ⊆ {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) ∧
      (b i : UA E a → ℂ) ∈ ⨆ U ∈ s, U :=
    fun i => Submodule.mem_sSup_iff_exists_finset.1 (hsum _ (hS _ (b i).2))
  choose s hsA hsm using hex
  let s0 := Finset.univ.biUnion s
  have hs0A : ∀ U ∈ s0, IsAutRepU U := by
    intro U hU
    obtain ⟨i, -, hi'⟩ := Finset.mem_biUnion.1 hU
    exact hsA i hi'
  obtain ⟨t, hts, hti, htS⟩ := GlobalTheory.EigenDecomp.exists_indep s0 hs0A
  refine ⟨t, fun U hU => hs0A U (hts hU), hti, ?_⟩
  intro φ hφ
  rw [htS]
  have e : φ = ∑ i, (b.repr ⟨φ, hφ⟩ i) • (b i : UA E a → ℂ) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine (iSup₂_le fun U hU => le_sSup ?_ : (⨆ U ∈ s i, U) ≤ sSup (s0 : Set (Submodule ℂ (UA E a → ℂ)))) (hsm i)
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hU⟩)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.WExpH
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.wExp_h : ExpBasic → SqExp → TorFacts → WExp := by
  intro hB hS hT E _ _ _ a τ W
  classical
  obtain ⟨-, -, hmono, -, -, hinv⟩ := hB
  set v₀ := InfinitePlace.mk τ with hv₀
  let d : ℕ := ∑ i, ((W v₀).w i).natAbs + a * (W v₀).detShift.natAbs
  have hps : ∀ k, psum (W v₀) k ≤ d := fun k => by
    have h1 : psum (W v₀) k ≤ ∑ i, (((W v₀).w i).natAbs : ℤ) :=
      (Finset.sum_le_sum fun i _ => Int.le_natAbs).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _)
    have h2 : (0 : ℤ) ≤ ((a * (W v₀).detShift.natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
    simp only [d, Nat.cast_add, Nat.cast_sum]
    omega
  have h1 : ∀ k w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ), (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpGe (-d) := fun k w L =>
    ⟨(hmono _ _ (hps k)).1 (hS a k _ w L).1, (hmono _ _ (neg_le_neg (by exact_mod_cast Nat.le_add_left _ _))).2 (hS a k _ w L).2⟩
  refine ⟨d, fun k x hx v L => ?_⟩
  have h2 : (∀ z, (x z).1 ∈ embU a v₀.embedding) ∧ ∀ w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ),
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpGe (-d) := by
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · rw [hv₀, e]
      refine ⟨fun z => (hx z).1, fun w L => ?_⟩
      simp only [(hx _).2]
      exact h1 k w L
    · rw [hv₀, e]
      refine ⟨fun z => by rw [GlobalTheory.DefiniteBC.embU_conjugate]; exact (hx z).1, fun w L => ?_⟩
      have e2 : ∀ z, cEmb (ComplexEmbedding.conjugate τ) (x z).1 = tor a k z⁻¹ := fun z => by
        rw [← (hT a k z).2.2.2, ← (hx z).2]
        ext i j
        simp [cEmb, GlobalTheory.DefiniteBC.coord_conjugate]
      simp only [e2]
      have h3 := (hinv _ _).2 (h1 k w L).2
      rw [neg_neg] at h3
      exact ⟨h3, (hinv _ _).1 (h1 k w L).1⟩
  let Φ : W.Sp →ₗ[ℂ] (Circle → ℂ) := LinearMap.pi fun z => L ∘ₗ W.rep (x z)
  let N : Submodule ℂ W.Sp := (ExpLe d ⊓ ExpGe (-d)).comap Φ
  have hN : ∀ e, GlobalTheory.CoefIrred.tenMul W e ∈ N := fun e => by
    have h := h2.2 (e v₀) (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
    have e3 : Φ (GlobalTheory.CoefIrred.tenMul W e) = fun z => (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
        (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) (e v₀)) := by
      funext z
      have := rep_tenMul_update W v₀ (x z) (h2.1 z) e (e v₀)
      rw [Function.update_eq_self] at this
      exact congrArg L this
    change Φ _ ∈ ExpLe d ⊓ ExpGe (-d)
    rw [e3]
    exact h
  have h0 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) a W (W.Sp ⧸ N) 0).unique (y₁ := N.mkQ) (y₂ := 0)
    (fun u => (Submodule.Quotient.mk_eq_zero N).2 (hN u)) (fun u => rfl)
  exact (Submodule.Quotient.mk_eq_zero N).1 (LinearMap.congr_fun h0 v)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.Wt.famOf_of : ExpBasic → PevExp → SqExp → TopUp → WExp → FamOfA → FamOf := by
  intro hB hP hS hT hW hA E _ _ _ a τ C hC n hn W Q _ f hf P
  obtain ⟨hLe, hGe, hmono, -, hconst, -⟩ := hB
  obtain ⟨d₀, hd₀⟩ := hW E a τ W
  refine ⟨Finset.univ.sup (fun q => (P q).totalDegree) + d₀, fun ν X => ?_⟩
  have hsum : ∀ (T : Submodule ℂ (Circle → ℂ)) (F : Q → Circle → ℂ), (∀ q, F q ∈ T) → (fun z => ∑ q, F q z) ∈ T := by
    intro T F h
    have : (fun z => ∑ q, F q z) = ∑ q, F q := by funext z; simp [Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun q _ => h q
  refine ⟨(hA E a τ C hC n hn W ν Q f P X).1, ?_, ?_, ?_, ?_, ?_, (hA E a τ C hC n hn W ν Q f P X).2⟩
  · intro k hk y₁ y₂ v
    funext g
    rw [RU_apply, famOf_apply, famOf_apply, hn.lev k hk]
    exact Finset.sum_congr rfl fun q _ => by rw [hf q k hk]
  · intro x y₁ y₂ v
    funext g
    rw [RU_apply, famOf_apply, famOf_apply, hn.inf x x.2]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [(f q).2.2 x v, RU_apply, mul_assoc (n g), mul_assoc (n g)]
  · intro b hb y₁ y₂ v
    funext g
    rw [Pi.smul_apply, famOf_apply, famOf_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : delta ν (X q * (n g * (y₁ * b))) = chi ν b * delta ν (X q * (n g * y₁)) := by
      have e : X q * (n g * (y₁ * b)) = X q * (n g * y₁) * b := by simp only [mul_assoc]
      unfold delta
      rw [e, map_mul, Module.End.mul_apply, hT a ν b hb, map_smul, map_smul, smul_eq_mul]
    rw [this]; ring
  · intro k x hx y₁ y₂ v g
    simp only [famOf_apply]
    refine hsum _ _ fun q => ?_
    have h1 := (hP a k (P q) (n g) y₂).1
    have h2 : (fun z => delta ν (X q * (n g * (tor a k z * y₁)))) ∈ ExpLe (psum ν k) := by
      have := (hS a k ν (sqRep ℂ a ν y₁ (top ν)) ((ev1 ν) ∘ₗ (sqRep ℂ a ν (X q * n g)))).1
      refine (congrArg (· ∈ ExpLe (psum ν k)) (funext fun z => ?_)).mpr this
      rw [delta, LinearMap.comp_apply, ← mul_assoc (X q), map_mul (sqRep ℂ a ν) (X q * n g), map_mul (sqRep ℂ a ν) (tor a k z),
        Module.End.mul_apply, Module.End.mul_apply]
    have h3 := (hd₀ k x hx v ((LinearMap.proj g) ∘ₗ (f q).1)).1
    refine (hmono _ _ ?_).1 (hLe _ _ _ _ (hLe _ _ _ _ h1 h2) h3)
    have : (P q).totalDegree ≤ Finset.univ.sup (fun q => (P q).totalDegree) :=
      Finset.le_sup (f := fun q => (P q).totalDegree) (Finset.mem_univ q)
    push_cast
    omega
  · intro k x hx y₂ v g
    simp only [famOf_apply]
    refine hsum _ _ fun q => ?_
    have h1 := (hP a k (P q) (n g) y₂).2
    have h2 := (hconst (delta ν (X q * (n g * 1)))).2
    have h3 := (hd₀ k x hx v ((LinearMap.proj g) ∘ₗ (f q).1)).2
    refine (hmono _ _ ?_).2 (hGe _ _ _ _ (hGe _ _ _ _ h1 h2) h3)
    push_cast
    omega
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpDisj
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private noncomputable def chiZ (m : ℤ) : Circle →* ℂ where
  toFun z := (z : ℂ) ^ m
  map_one' := by simp
  map_mul' x y := by simp [mul_zpow]

private theorem chiZ_injective : Function.Injective chiZ := by
  intro m n h
  by_contra hmn
  have hk : m - n ≠ 0 := sub_ne_zero.mpr hmn
  set z : Circle := Circle.exp (Real.pi / (m - n : ℤ)) with hz
  have hpow : (z : ℂ) ^ (m - n) = -1 := by
    rw [hz, Circle.coe_exp, ← Complex.exp_int_mul]
    have : ((m - n : ℤ) : ℂ) * (((Real.pi / ((m - n : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      have hk' : ((m - n : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hk
      push_cast
      push_cast at hk'
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have h1 : (z : ℂ) ^ m = (z : ℂ) ^ n := DFunLike.congr_fun h z
  have hz0 : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  have h2 : (z : ℂ) ^ (m - n) = 1 := by
    rw [zpow_sub₀ hz0, h1, div_self (zpow_ne_zero _ hz0)]
  rw [h2] at hpow
  norm_num at hpow

theorem UpperTheory.Gal.Wt.expDisj_of :
    UpperTheory.Gal.Wt.ExpDisj := by
  intro s t f hst hle hge
  let v : ℤ → (Circle → ℂ) := fun m z => (z : ℂ) ^ m
  have hli : LinearIndependent ℂ v :=
    (linearIndependent_monoidHom Circle ℂ).comp chiZ chiZ_injective
  have hd : Disjoint (Set.Iic s) (Set.Ici t) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (lt_of_le_of_lt (Set.mem_Iic.mp hx) hst) (not_lt.mpr (Set.mem_Ici.mp hx'))
  have hdisj := hli.disjoint_span_image hd
  have e1 : ExpLe s = Submodule.span ℂ (v '' Set.Iic s) := by
    unfold ExpLe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  have e2 : ExpGe t = Submodule.span ℂ (v '' Set.Ici t) := by
    unfold ExpGe
    congr 1
    ext g
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, rfl⟩
  rw [e1] at hle
  rw [e2] at hge
  exact Submodule.disjoint_def.mp hdisj f hle hge
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOffHolds
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famOff_holds : FamOff := by
  intro E _ _ _ a τ W K ν d B hB U hU hBU hne τ' hτ'
  classical
  obtain ⟨y₁, y₂, v₀, hv₀⟩ := hne
  set v := InfinitePlace.mk τ' with hv
  obtain ⟨e, he⟩ : ∃ e, B y₁ y₂ (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h1 : B y₁ y₂ = 0 := by
      apply (Formalism.L2.DIV.bVV ℂ W).ext
      intro i
      have hi : Formalism.L2.DIV.bVV ℂ W i = GlobalTheory.CoefIrred.tenMul W
          (fun τ => GlobalTheory.CoefIrred.ssBasis ℂ (W τ) (i τ)) := by
        apply Subtype.ext
        rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe,
          Formalism.L2.DIV.bVVfun]
        simp only [GlobalTheory.CoefIrred.ssBasis_coe]
      rw [hi]
      exact hc _
    exact hv₀ (by rw [h1]; rfl)
  have h : (AU.mk ⟨U, hU⟩).HasWt v.embedding (W v) := by
    refine ⟨isIrreducible_sqRep a (W v), B y₁ y₂ ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun x => hBU _ _ _,
      fun x u => ?_⟩
    · have := LinearMap.congr_fun h0 (e v)
      simpa [MultilinearMap.toLinearMap] using this
    · have hx : x.1 ∈ infU E a := embU_le_infU _ x.2
      have h1 : cEmb τ x.1 = 1 :=
        Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 x.2).2 τ) (by rw [InfinitePlace.mk_embedding]; exact hτ'.symm)
      have h2 := hB.inf ⟨x.1, hx⟩ y₁ y₂ (GlobalTheory.CoefIrred.tenMul W (Function.update e v u))
      rw [rep_tenMul_update W v ⟨x.1, hx⟩ x.2, h1, one_mul, one_mul] at h2
      exact h2.symm
  rcases InfinitePlace.embedding_mk_eq τ' with e | e
  · have h' := h
    rw [← Wt.at_embedding W v, e] at h'
    exact h'
  · have h2 := h.conjugate
    rw [← Wt.at_embedding W v, ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ'] at h2
    exact h2

theorem psum_succ {a : ℕ} (κ : DomWeight a) (i : Fin a) : psum κ (i + 1) = psum κ i + κ.w i := by
  have e : (Finset.univ.filter fun j : Fin a => j.val < i + 1) = insert i (Finset.univ.filter fun j : Fin a => j.val < i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [psum, e, Finset.sum_insert (by simp), add_comm, psum]

theorem famWt_of : FamOff → FamSum → FamWt := by
  intro hOff hSum E _ _ _ a τ W K ν d B hB U hU hBU hne
  obtain ⟨mu, hmu⟩ := GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep E a U hU
  refine ⟨mu, ⟨hU, hmu, ?_⟩, fun τ' h => hasWeightAt_unique ⟨U, hU⟩ τ' (hmu τ') (hOff E a τ W K ν d B hB U hU hBU hne τ' h),
    fun i => ?_⟩
  · obtain ⟨y₁, y₂, v, hv⟩ := hne
    exact ⟨_, hBU y₁ y₂ v, hv, fun x hx => hB.fix x hx _ _ _⟩
  · have h1 := hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) i
    have h2 := hSum E a τ W K ν d B hB U hU hBU hne _ (hmu τ) (i + 1)
    rw [psum_succ, psum_succ] at h2
    rw [abs_le]
    push_cast
    omega

end UpperTheory.Gal.Wt

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NearSub
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem entry_mul_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    {A B : Matrix (Fin a) (Fin a) ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖ι.symm (A i j)‖ ≤ r) (hB : ∀ i j, ‖ι.symm (B i j)‖ ≤ s) (i j : Fin a) :
    ‖ι.symm ((A * B) i j)‖ ≤ r * s := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hr

theorem UpperTheory.Gal.Wt.nearSub_of :
    UpperTheory.Gal.Wt.NearSub := by
  intro l _ ι a Γ _ _ _ φ hc hI ε hε
  refine ⟨{ carrier := {g | NearOne ι ε (φ g)}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, fun g => Iff.rfl⟩
  · intro g h hg hh
    have hg' : NearOne ι ε (φ g) := hg
    have hh' : NearOne ι ε (φ h) := hh
    show NearOne ι ε (φ (g * h))
    intro i j
    have key : ((φ (g * h) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) * ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
          + (((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) := by
      rw [map_mul, Units.val_mul]
      noncomm_ring
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.add_apply, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · have := entry_mul_le ι hε.le zero_le_one
        (A := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
        (B := ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
        (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) (fun i j => (hI h i j).1) i j
      exact this.trans_eq (mul_one ε)
    · rw [Matrix.sub_apply]
      exact hh' i j
  · show NearOne ι ε (φ 1)
    intro i j
    rw [map_one, Units.val_one, sub_self, map_zero, norm_zero]
    exact hε.le
  · intro g hg
    have hg' : NearOne ι ε (φ g) := hg
    show NearOne ι ε (φ g⁻¹)
    intro i j
    have key : ((φ g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = -((((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
            * (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)) := by
      rw [map_inv, mul_sub, Units.inv_mul, mul_one, neg_sub]
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.neg_apply, map_neg, norm_neg]
    have := entry_mul_le ι zero_le_one hε.le
      (A := (((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
      (B := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
      (fun i j => (hI g i j).2) (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) i j
    exact this.trans_eq (one_mul ε)
  · have hset : ({g | NearOne ι ε (φ g)} : Set Γ)
        = ⋂ i, ⋂ j, (fun g => ι.symm (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)) ⁻¹'
            Metric.closedBall (ι.symm ((1 : Matrix (Fin a) (Fin a) ℂ) i j)) ε := by
      ext g
      simp only [Set.mem_setOf_eq, NearOne, map_sub, Set.mem_iInter, Set.mem_preimage,
        Metric.mem_closedBall, dist_eq_norm]
    show IsOpen ({g | NearOne ι ε (φ g)} : Set Γ)
    rw [hset]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hc i j).isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hε.ne')
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamExOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem cEmb_fin {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (τ : E →+* ℂ) {c : UA E n}
    (hc : c ∈ finU (E := E) (n := n)) : cEmb τ c = 1 := by
  have : cInf c = 1 := hc
  simp [cEmb, this]

theorem UpperTheory.Gal.Wt.famEx_of : NeatLev → EllC → Twist → TwistBd → Kap0 → Pieces → DeltaNear → FamOf → FamEx := by
  intro hN hE hT hTB hK hP hD hF E _ _ _ l _ ι a ha w₀ hl hs v' hs' hap K hKl hKv Kv hKo W f hf τ hτ X b hb ε hε
  classical
  obtain ⟨C, hC, hKC, hneat, hint, hfC⟩ := hN E l Fact.out a ha w₀ hl hs v' hs' hap K hKl hKv Kv hKo W f hf
  obtain ⟨ℓ, hℓ⟩ := hE E a C hC.fin hneat
  obtain ⟨R, hR0, hR⟩ := hTB E l ι a C hC ℓ hℓ W f X b hb
  obtain ⟨κ, hκr, hκi, hκ1, hκc, hκI⟩ := hK E l ι a v' τ hτ
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  let φ : C →* GL (Fin a) ℂ := κ.comp C.subtype
  have hφI : ∀ c : C, IntGL ι (φ c) := fun c => hκI _ (hint _ c.2)
  obtain ⟨Q, _, c, P, hQ⟩ := hP l ι a C φ (fun i j => (hκc i j).comp continuous_subtype_val) hφI
    ((Kv.comap (cLoc v')).subgroupOf C)
    (hKo.preimage ((GlobalTheory.BCT.GlobLev.continuous_cLoc v').comp continuous_subtype_val))
    (fun x hx => by
      have h1 : cLoc v' x.1 = 1 := (hκ1 _).1 hx
      change cLoc v' x.1 ∈ Kv
      rw [h1]; exact Kv.one_mem) (ε / R) (div_pos hε hR0)
  choose F hFC hFv using fun q => hT E a C hC ℓ hℓ W f (c q)
  let M : UA E a → GL (Fin a) ℂ := fun g => (cEmb τ g)⁻¹ * κ g
  let n : UA E a → GL (Fin a) ℂ := fun g => φ (ℓ g) * (M g)⁻¹
  have hn : IsNrm τ C n := by
    refine ⟨fun γ hγ g => ?_, fun k hk g => ?_, fun x hx g => ?_⟩
    · simp only [n, M, hℓ.left γ hγ, map_mul, hκr γ hγ]
      group
    · have := hℓ.lev ⟨k, hk⟩ g
      have e : φ ⟨k, hk⟩ = κ k := rfl
      simp only [n, M] at this ⊢
      rw [this]
      simp only [map_mul, cEmb_fin τ (hC.fin hk), e]
      group
    · simp only [n, M, hℓ.inf x hx, map_mul, hκi x hx]
      group
  obtain ⟨d, hd⟩ := hF E a τ C hC n hn W Q F hFC P
  refine ⟨d, M, fun g h hh h1 => ?_, fun ν => ?_⟩
  · simp only [M, map_mul, cEmb_fin τ hh, (hκ1 h).2 h1, mul_one]
  have hfam := hd ν fun q => (φ (c q))⁻¹
  refine ⟨_, ⟨hfam.aut, fun k hk => hfam.fix k (hKC hk), hfam.inf, hfam.up, hfam.le, hfam.ge, hfam.fin⟩, fun g i => ?_⟩
  obtain ⟨q₀, h0, h1, h2, h3⟩ := hQ (ℓ g)
  have hnM : n g * M g = φ (ℓ g) := by simp only [n]; group
  have hε' : 0 ≤ ε / R := (div_pos hε hR0).le
  have hv : f.1 (b g i) g = (F q₀).1 (b g i) g := by
    rw [hFv, ← hfC ((c q₀)⁻¹ * ℓ g : C) ⟨Subtype.prop _, h0⟩ (b g i) (g * ((ℓ g)⁻¹ * c q₀ : C))]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hδ : ∀ q, (φ (c q))⁻¹ * φ (ℓ g) = φ ((c q)⁻¹ * ℓ g) := fun q => by rw [map_mul, map_inv]
  rw [famOf_apply, hv, hnM]
  have e : (F q₀).1 (b g i) g - ∑ q, pev (P q) (φ (ℓ g)) * delta ν ((φ (c q))⁻¹ * φ (ℓ g)) * (F q).1 (b g i) g =
      ∑ q, ((if q = q₀ then 1 else 0) - pev (P q) (φ (ℓ g)) * delta ν (φ ((c q)⁻¹ * ℓ g))) * (F q).1 (b g i) g := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, hδ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε.le fun q _ => ?_
  rw [map_mul, norm_mul, hFv, ← div_mul_cancel₀ ε hR0.ne']
  refine mul_le_mul ?_ (hR _ _ _) (norm_nonneg _) hε'
  obtain ⟨hb1, hb2⟩ := hD l ι a ν _ (hφI ((c q)⁻¹ * ℓ g))
  by_cases hq : q = q₀
  · subst hq
    have hb3 := hb2 _ hε' h1
    rw [if_pos rfl]
    have e2 : 1 - pev (P q) (φ (ℓ g)) * delta ν (φ ((c q)⁻¹ * ℓ g)) =
        -((pev (P q) (φ (ℓ g)) - 1) * delta ν (φ ((c q)⁻¹ * ℓ g)) + (delta ν (φ ((c q)⁻¹ * ℓ g)) - 1)) := by ring
    rw [e2, map_neg, norm_neg, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hb3)
    rw [map_mul, norm_mul]
    exact (mul_le_mul h2 hb1 (norm_nonneg _) hε').trans_eq (mul_one _)
  · rw [if_neg hq, zero_sub, map_neg, norm_neg, map_mul, norm_mul]
    exact (mul_le_mul (h3 q hq) hb1 (norm_nonneg _) hε').trans_eq (mul_one _)
end
