module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.LacunaryBaseWeightAntitone
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.RFinEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DomOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EmbProjHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NrmAut
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.nrmAut_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.NrmAut := by
  intro hC E _ _ _ a τ C hCl n hn p hp
  obtain ⟨hpc, A, hAf, hA⟩ := hp
  let S : Submodule ℂ (UA E a → ℂ) := A.map (LinearMap.funLeft ℂ ℂ n)
  have hSf : FiniteDimensional ℂ S := inferInstance
  have hS : ∀ y, (fun g => p (n g * y)) ∈ S := fun y => ⟨_, hA y, rfl⟩
  refine ⟨fun y => ?_, S, hSf, hS⟩
  refine hC E a C hCl _ (fun γ hγ g => by simp only [hn.left γ hγ g])
    (fun c hc g => by simp only [hn.lev c hc g]) (fun g => ?_) S hSf (fun x hx => ?_)
  · have he : (fun x : infU E a => p (n (g * x.1) * y)) =
        fun x : infU E a => p (n g * (cEmb τ x.1 * y)) := by
      funext x
      rw [hn.inf x.1 x.2 g, mul_assoc]
    rw [he]
    exact hpc.comp (continuous_const.mul
      (((GlobalTheory.AutRec.continuous_cEmb_emb τ).comp continuous_subtype_val).mul continuous_const))
  · have he : RU E a x (fun g => p (n g * y)) = fun g => p (n g * (cEmb τ x * y)) := by
      funext g
      change p (n (g * x) * y) = _
      rw [hn.inf x hx g, mul_assoc]
    rw [he]
    exact hS _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistBd
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)

namespace UpperTheory.Gal.Wt

private theorem isOpen_subgroupOf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    {C C₀ : Subgroup (UA E a)} (hC : IsLevel C) (hC₀ : IsLevel C₀) :
    IsOpen ((C₀.subgroupOf C : Subgroup C) : Set C) := by
  obtain ⟨N, hNo, h1N, hNC⟩ := hC₀.isOpen
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  refine Filter.mem_of_superset
    ((hNo.preimage continuous_subtype_val).mem_nhds (show ((1 : C) : UA E a) ∈ N from h1N)) ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, hC.fin x.2⟩)

theorem twistBd_of : Twist → TwistBd := by
  intro hT E _ _ _ l _ ι a C hC ℓ hℓ W f X b hb
  classical
  obtain ⟨C₀, hC₀, hf⟩ := UpperTheory.Gal.Gen.levelEx_holds E a W f
  have hHo := isOpen_subgroupOf hC hC₀
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  haveI : Finite (C ⧸ C₀.subgroupOf C) := Subgroup.quotient_finite_of_isOpen _ hHo
  letI := Fintype.ofFinite (C ⧸ C₀.subgroupOf C)
  have hq : ∀ q : C ⧸ C₀.subgroupOf C, ∃ R : ℝ, ∀ g i,
      ‖ι.symm (f.1 (b g i) (g * ((ℓ g)⁻¹ * q.out : C)))‖ ≤ R := by
    intro q
    obtain ⟨F, -, hF⟩ := hT E a C hC ℓ hℓ W f q.out
    obtain ⟨R, hR⟩ := hb F
    exact ⟨R, fun g i => by rw [← hF]; exact hR g i⟩
  choose R hR using hq
  refine ⟨1 + ∑ q, |R q|, by positivity, fun c g i => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (C₀.subgroupOf C) c
  have hhC : ((h : C) : UA E a) ∈ C₀ := Subgroup.mem_subgroupOf.1 h.2
  have e : f.1 (b g i) (g * ((ℓ g)⁻¹ * (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C).out : C)) =
      f.1 (b g i) (g * ((ℓ g)⁻¹ * c : C)) := by
    rw [hh]
    have : (((ℓ g)⁻¹ * (c * (h : C)) : C) : UA E a) = (((ℓ g)⁻¹ * c : C) : UA E a) * ((h : C) : UA E a) := by
      simp [mul_assoc]
    rw [this, ← mul_assoc]
    exact hf _ hhC _ _
  rw [← e]
  refine (hR _ g i).trans ((le_abs_self _).trans ?_)
  have := Finset.single_le_sum (f := fun q => |R q|) (fun q _ => abs_nonneg _)
    (Finset.mem_univ (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C))
  linarith

end UpperTheory.Gal.Wt

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfA
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.famOfA_of :
    UpperTheory.Gal.Wt.AutMul → UpperTheory.Gal.Wt.NrmAut → UpperTheory.Gal.Wt.RFinEx → UpperTheory.Gal.Wt.FamOfA := by
  intro hMul hNrm hR E _ _ _ a τ C hC n hn W ν Q _ f P X
  have hp := fun q => hNrm E a τ C hC n hn (pev (P q)) ((hR a).2 (P q))
  have hd := fun q => hNrm E a τ C hC n hn (fun m => delta ν (X q * m)) ((hR a).1 ν (X q))
  have key : ∀ y₁ y₂ v, famOf n ν f P X y₁ y₂ v =
      ∑ q, ((fun g => pev (P q) (n g * y₂)) * (fun g => delta ν (X q * (n g * y₁)))) * (f q).1 v := by
    intro y₁ y₂ v
    funext g
    rw [famOf_apply, Finset.sum_apply]
    rfl
  refine ⟨fun y₁ y₂ v => ?_, ?_⟩
  · rw [key]
    exact mem_autU.1 (Submodule.sum_mem _ fun q _ => mem_autU.2
      (hMul E a _ _ (hMul E a _ _ ((hp q).1 y₂) ((hd q).1 y₁)) ((f q).2.1 v)))
  · choose S₁ hS₁f hS₁ using fun q => (hp q).2
    choose S₂ hS₂f hS₂ using fun q => (hd q).2
    have hfin : ∀ q, FiniteDimensional ℂ ↥(S₁ q * S₂ q * LinearMap.range (f q).1) := fun q => by
      have h₁ : (S₁ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₁f q)
      have h₂ : (S₂ q).FG := Submodule.fg_iff_finiteDimensional _ |>.2 (hS₂f q)
      have h₃ : (LinearMap.range (f q).1).FG := Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
      exact Submodule.fg_iff_finiteDimensional _ |>.1 ((h₁.mul h₂).mul h₃)
    refine ⟨⨆ q, S₁ q * S₂ q * LinearMap.range (f q).1, Submodule.finiteDimensional_iSup _, ?_⟩
    intro y₁ y₂ v
    rw [key]
    exact Submodule.sum_mem _ fun q _ => Submodule.mem_iSup_of_mem q
      (Submodule.mul_mem_mul (Submodule.mul_mem_mul (hS₁ q y₂) (hS₂ q y₁)) (LinearMap.mem_range_self _ v))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.QROf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.qR_of :
    UpperTheory.Gal.Wt.QR := by
  intro a y
  obtain ⟨k, hk, b, hg, hb⟩ := GlobalTheory.T.iwasawa_unitary_upper_triangular (y : Matrix (Fin a) (Fin a) ℂ) y.isUnit
  let u : Matrix.unitaryGroup (Fin a) ℂ := ⟨k, hk⟩
  have hu : ((unitaryIncl a u : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = k := rfl
  refine ⟨u, (unitaryIncl a u)⁻¹ * y, ?_, (mul_inv_cancel_left _ _).symm⟩
  have hbm : (((unitaryIncl a u)⁻¹ * y : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) = b := by
    rw [Units.val_mul, hg, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  intro i j hij
  rw [hbm]
  exact hb hij
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamSum
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famSum_of : ExpBasic → EvLem → TorFacts → QR → WtBd → EmbProj → FamSum := by
  intro hEB hEv hTor hQR hBd hEP E _ _ _ a τ W K ν d B hB U hU hBU hne κ hκ k
  obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E a τ
  have hx : ∀ u : Matrix.unitaryGroup (Fin a) ℂ, ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = unitaryIncl a u := fun u => by
    have h := he (e.symm u)
    rw [e.apply_symm_apply] at h
    exact ⟨⟨(e.symm u).1, (Subgroup.mem_inf.1 (e.symm u).2).1⟩, (e.symm u).2, h.symm⟩
  choose x hx using fun z : Circle => (show ∃ x : infU E a, x.1 ∈ embU a τ ∧ cEmb τ x.1 = tor a k z by
    obtain ⟨u, hu⟩ := (hTor a k z).2.1
    rw [← hu]
    exact hx u)
  rename_i hxu
  have hc : IsCirc τ k x := hx
  obtain ⟨S, hS, hBS⟩ := hB.fin
  have hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) →
      ∀ L : (UA E a → ℂ) →ₗ[ℂ] ℂ, (fun z => L (Φ z)) ∈ T := fun T Φ h1 h2 L =>
    hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T
      (fun z => ⟨Φ z, h1 z⟩) h2 (L ∘ₗ S.subtype)
  obtain ⟨y₁, y₂, v, hv⟩ := hne
  constructor
  · obtain ⟨p, hp0, hp⟩ := hEP E a τ U hU κ hκ _ (hBU y₁ y₂ v) hv
    refine (hBd a k κ _).1 {w | ∃ y₁ y₂ v, w = p (B y₁ y₂ v)} ⟨_, ⟨y₁, y₂, v, rfl⟩, hp0⟩ ?_ ?_
    · rintro u _ ⟨y₁, y₂, v, rfl⟩
      obtain ⟨x', h1, h2⟩ := hxu u
      exact ⟨_, _, _, by rw [← h2, ← hp _ h1 _ (hBU _ _ _), hB.inf x']⟩
    · rintro _ ⟨y₁, y₂, v, rfl⟩ L
      have := hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hc y₁ y₂ v g) (L ∘ₗ p)
      convert this using 2 with z
      rw [← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z)]
      rfl
  · obtain ⟨y, v', hv'⟩ : ∃ y v', B 1 y v' ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨u, b, hb, rfl⟩ := hQR a y₁
      obtain ⟨x', -, h2⟩ := hxu u
      have e1 := hB.inf x' 1 ((cEmb τ x'.1)⁻¹ * y₂) (W.rep x'⁻¹ v)
      rw [h, map_zero, mul_one, mul_inv_cancel_left, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply, h2] at e1
      rw [hB.up b hb, ← e1, smul_zero] at hv
      exact hv rfl
    obtain ⟨p, hp0, hp⟩ := hEP E a τ U hU κ hκ _ (hBU 1 y v') hv'
    refine (hBd a k κ _).2 _ hp0 fun L => ?_
    have h1 := hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hc y v' g) (L ∘ₗ p)
    have h2 := hEB.2.1 _ _ _ _ (hEB.2.2.2.1 1 (psum ν k)).2 h1
    rw [sub_eq_add_neg]
    convert h2 using 2 with z
    rw [← (hx z).2, ← hp _ (hx z).1 _ (hBU _ _ _), hB.inf (x z), (hx z).2, mul_one, ← one_mul (tor a k z),
      hB.up _ (hTor a k z).1, (hTor a k z).2.2.1, map_smul, map_smul, one_mul, one_mul]
    rfl

end UpperTheory.Gal.Wt

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SepPoly
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem mvEval_aeval_X_sub_C_eq_eval_sub {k : Type} [Field k] {σ : Type} (p : Polynomial k) (i : σ) (c : k)
    (z : σ → k) :
    MvPolynomial.eval z (Polynomial.aeval (MvPolynomial.X i - MvPolynomial.C c) p) =
      Polynomial.eval (z i - c) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

private theorem norm_prod_sub_one_le_of_norm_sub_one_le {k : Type} [NormedField k] [IsUltrametricDist k] {ι : Type}
    [DecidableEq ι] (s : Finset ι) (f : ι → k) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (h : ∀ j ∈ s, ‖f j - 1‖ ≤ c) : ‖∏ j ∈ s, f j - 1‖ ≤ c := by
  induction s using Finset.induction_on with
  | empty => simpa using hc0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih (fun l hl => h l (Finset.mem_insert_of_mem hl))
    have hx : ‖f j‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (f j - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (h1.trans hc) le_rfl)
    have e : f j * ∏ l ∈ s, f l - 1 = f j * (∏ l ∈ s, f l - 1) + (f j - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ h1)
    rw [norm_mul]
    calc ‖f j‖ * ‖∏ l ∈ s, f l - 1‖ ≤ 1 * c := mul_le_mul hx h2 (norm_nonneg _) zero_le_one
      _ = c := one_mul c

private theorem norm_one_sub_le_one_of_norm_le_one {k : Type} [NormedField k] [IsUltrametricDist k] {x : k}
    (h : ‖x‖ ≤ 1) : ‖1 - x‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_one]
  · rw [norm_neg]
    exact h

theorem UpperTheory.Gal.Wt.sepPoly_of :
    UpperTheory.Gal.Wt.Kapl → UpperTheory.Gal.Wt.SepPoly := by
  intro hK k _ _ σ _ Z₁ Z₂ h₁ h₂ hd ε hε
  classical
  obtain ⟨D, hD, hDd⟩ := hd.exists_thickenings h₁ h₂.isClosed
  have he0 : 0 < min ε 1 := lt_min hε one_pos
  have he1 : min ε 1 ≤ 1 := min_le_right _ _
  have heε : min ε 1 ≤ ε := min_le_left _ _
  obtain ⟨T, hTsub, hTfin, hcov⟩ := h₁.finite_cover_balls (mul_pos hD he0)
  obtain ⟨Y, hY, hmemY⟩ : ∃ Y : Set k, IsCompact Y ∧
      ∀ i, ∀ a ∈ hTfin.toFinset, ∀ z ∈ Z₁ ∪ Z₂, z i - a i ∈ Y := by
    refine ⟨⋃ i : σ, ⋃ a ∈ hTfin.toFinset, (fun z : σ → k => z i - a i) '' (Z₁ ∪ Z₂), ?_, ?_⟩
    · exact isCompact_iUnion fun i => hTfin.toFinset.isCompact_biUnion fun a _ =>
        (h₁.union h₂).image (by fun_prop)
    · intro i a ha z hz
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion₂.2 ⟨a, ha, z, hz, rfl⟩⟩
  obtain ⟨p, hp1, hp2, hp3⟩ := hK k Y hY D (min ε 1) hD he0 he1
  obtain ⟨q, hq⟩ : ∃ q : (σ → k) → MvPolynomial σ k,
      ∀ a z, MvPolynomial.eval z (q a) = ∏ i, Polynomial.eval (z i - a i) p :=
    ⟨fun a => ∏ i, Polynomial.aeval (MvPolynomial.X i - MvPolynomial.C (a i)) p,
      fun a z => by simp only [map_prod, mvEval_aeval_X_sub_C_eq_eval_sub]⟩
  have hqle : ∀ a ∈ hTfin.toFinset, ∀ z ∈ Z₁ ∪ Z₂, ‖MvPolynomial.eval z (q a)‖ ≤ 1 := by
    intro a ha z hz
    rw [hq, norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hp1 _ (hmemY i a ha z hz))
  refine ⟨1 - ∏ a ∈ hTfin.toFinset, (1 - q a), ?_, ?_⟩
  · intro z hz
    obtain ⟨a0, ha0T, hza⟩ := Set.mem_iUnion₂.1 (hcov hz)
    have ha0 : a0 ∈ hTfin.toFinset := hTfin.mem_toFinset.2 ha0T
    have hnear : ‖MvPolynomial.eval z (q a0) - 1‖ ≤ min ε 1 := by
      rw [hq]
      apply norm_prod_sub_one_le_of_norm_sub_one_le _ _ he0.le he1
      intro i _
      apply hp3
      have := norm_le_pi_norm (z - a0) i
      rw [Metric.mem_ball, dist_eq_norm] at hza
      simp only [Pi.sub_apply] at this
      linarith
    simp only [map_sub, map_one, map_prod]
    rw [show (1 : k) - ∏ a ∈ hTfin.toFinset, (1 - MvPolynomial.eval z (q a)) - 1 =
        -∏ a ∈ hTfin.toFinset, (1 - MvPolynomial.eval z (q a)) by ring, norm_neg, norm_prod,
      ← Finset.mul_prod_erase _ _ ha0]
    have hrest : ∏ a ∈ hTfin.toFinset.erase a0, ‖1 - MvPolynomial.eval z (q a)‖ ≤ 1 := by
      apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro a ha
      exact norm_one_sub_le_one_of_norm_le_one (hqle a (Finset.mem_of_mem_erase ha) z (Or.inl hz))
    have h0 : ‖1 - MvPolynomial.eval z (q a0)‖ ≤ min ε 1 := by
      rw [norm_sub_rev]
      exact hnear
    calc ‖1 - MvPolynomial.eval z (q a0)‖ *
          ∏ a ∈ hTfin.toFinset.erase a0, ‖1 - MvPolynomial.eval z (q a)‖
        ≤ min ε 1 * 1 := mul_le_mul h0 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) he0.le
      _ ≤ ε := by linarith
  · intro z hz
    have hfar : ∀ a ∈ hTfin.toFinset, ‖MvPolynomial.eval z (q a)‖ ≤ min ε 1 := by
      intro a ha
      have hdist : D ≤ ‖z - a‖ := by
        by_contra hlt
        push_neg at hlt
        apply Set.disjoint_left.1 hDd
          (Metric.self_subset_thickening hD _ (hTsub (hTfin.mem_toFinset.1 ha)))
        exact Metric.mem_thickening_iff.2 ⟨z, hz, by rw [dist_eq_norm, norm_sub_rev]; exact hlt⟩
      obtain ⟨i, hi⟩ : ∃ i, D ≤ ‖z i - a i‖ := by
        by_contra hno
        push_neg at hno
        have := (pi_norm_lt_iff (x := z - a) hD).2 (fun i => by simpa using hno i)
        linarith
      rw [hq, norm_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      have h0 := hp2 _ (hmemY i a ha z (Or.inr hz)) hi
      have hrest : ∏ j ∈ Finset.univ.erase i, ‖Polynomial.eval (z j - a j) p‖ ≤ 1 :=
        Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hp1 _ (hmemY j a ha z (Or.inr hz)))
      calc _ ≤ min ε 1 * 1 :=
            mul_le_mul h0 hrest (Finset.prod_nonneg fun _ _ => norm_nonneg _) he0.le
        _ = min ε 1 := mul_one _
    simp only [map_sub, map_one, map_prod]
    have := norm_prod_sub_one_le_of_norm_sub_one_le hTfin.toFinset (fun a => 1 - MvPolynomial.eval z (q a)) he0.le he1
      (fun a ha => by
        rw [show (1 : k) - MvPolynomial.eval z (q a) - 1 = -MvPolynomial.eval z (q a) by ring,
          norm_neg]
        exact hfar a ha)
    rw [norm_sub_rev]
    linarith
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplOf
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.kapl_of :
    UpperTheory.Gal.Wt.KaplFin → UpperTheory.Gal.Wt.Kapl := by
  intro hfin k _ _ Y hY δ ε hδ hε hε1
  have hY' : IsCompact (Y ∩ {x : k | δ ≤ ‖x‖}) :=
    hY.inter_right (isClosed_le continuous_const continuous_norm)
  have hnhds : ∀ c ∈ Y ∩ {x : k | δ ≤ ‖x‖}, Metric.closedBall c (‖c‖ / 2) ∈ nhds c := by
    intro c hc
    have hc' : δ ≤ ‖c‖ := hc.2
    exact Metric.closedBall_mem_nhds c (by linarith)
  obtain ⟨s, hs, hcov⟩ := hY'.elim_nhds_subcover (fun c => Metric.closedBall c (‖c‖ / 2)) hnhds
  obtain ⟨p, h1, h2, h3⟩ := hfin k s δ ε hδ hε hε1 (fun c hc => (hs c hc).2)
  have hbig : ∀ x ∈ Y, δ ≤ ‖x‖ → ‖p.eval x‖ ≤ ε := by
    intro x hx hxδ
    have hmem := hcov ⟨hx, hxδ⟩
    simp only [Set.mem_iUnion, exists_prop] at hmem
    obtain ⟨c, hc, hxc⟩ := hmem
    exact h2 c hc x (by simpa [dist_eq_norm] using hxc)
  refine ⟨p, fun x hx => ?_, hbig, h3⟩
  rcases le_total ‖x‖ δ with h | h
  · exact h1 x h
  · exact (hbig x hx h).trans hε1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopOf
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

open UpperTheory.Gal.Gen UpperTheory.Gal.Int.Cong in
theorem top_of : FamEx → FamProj → FamWt → UpperTheory.Gal.Int.Cong.WtLacEx := by
  intro hEx hPr hWt E _ _ _ l _ ι a ha w₀ hw₀ hs₀ v' hv' hsv hap K hK hKv Kv hKvo lam Jx t η ht htv hact τ₀ hτ₀ U hU ε hε
  classical
  obtain ⟨W, f, hW, hf0, hfU, hfK, -⟩ := GlobalTheory.T.exists_algebraicForm_weight_level_smooth_at_place E a lam _ U (inf_le_left.trans hK.fin) hU w₀
  obtain rfl : lam = W.at := (funext hW).symm
  obtain ⟨X, b, hbd, hdef, hne⟩ := Loc.frame denomBdd_holds rhoBound_holds latFacts_holds levelEx_holds ι W t fun j => Or.inr (ht j)
  obtain ⟨g₀, i₀, hz⟩ : ∃ g i, f.1 (b g i) g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (hdef f h)
  set z₀ := f.1 (b g₀ i₀) g₀ with hz₀
  let f₁ : algForms W := z₀⁻¹ • f
  have hf₁ : ∀ v g, f₁.1 v g = z₀⁻¹ * f.1 v g := fun v g => rfl
  have hf₁K : f₁ ∈ fixedBy W (K ⊓ Kv.comap (cLoc v')) := fun k hk v g => by rw [hf₁, hf₁, hfK k hk v g]
  have hf₁U : ∀ v, f₁.1 v ∈ U := fun v => U.smul_mem _ (hfU v)
  obtain ⟨d, M, hM, hB⟩ := hEx E l ι a ha w₀ hw₀ hs₀ v' hsv hap K hK hKv Kv hKvo W f₁ hf₁K τ₀ hτ₀ X b hbd ε hε
  let N : ℕ := (a + 1) * (2 * (2 * d) + a) + 1
  let ν : DomWeight a := ⟨fun k => (N : ℤ) * mu0 a k, fun _ _ h => mul_le_mul_of_nonneg_left (lacunaryBaseWeight_antitone a h) (Int.natCast_nonneg N)⟩
  obtain ⟨B, hFam, hnear⟩ := hB ν
  obtain ⟨s₀, F, hF, hsum⟩ := hPr E a τ₀ W K ν d B hFam
  let I := s₀.filter fun V => ∃ y₁ y₂ v, F V y₁ y₂ v ≠ 0
  let Ft : Submodule ℂ (UA E a → ℂ) → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun V =>
    LinearMap.pi fun g => (LinearMap.proj g) ∘ₗ F V (M g) (M g)
  have hFt : ∀ V v g, Ft V v g = F V (M g) (M g) v g := fun _ _ _ => rfl
  let T : Jx → Module.End ℂ (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun j =>
    LinearMap.llcomp ℂ W.Sp (UA E a → ℂ) (UA E a → ℂ) (GlobalTheory.CongSc.opL (t j))
  let ev : UA E a × X → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) →ₗ[ℂ] ℂ := fun x =>
    (LinearMap.proj x.1) ∘ₗ (LinearMap.applyₗ (b x.1 x.2))
  have hT : ∀ j (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v, T j F' v = opOf (RU E a) (t j) (F' v) := fun _ _ _ => rfl
  have hev : ∀ x (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)), ev x F' = F' (b x.1 x.2) x.1 := fun _ _ => rfl
  have hne' : ∀ (F' : W.Sp →ₗ[ℂ] (UA E a → ℂ)) (R' : ℝ), (∀ x, ‖ι.symm (ev x F')‖ ≤ R') →
      ∀ j x, ‖ι.symm (ev x (T j F'))‖ ≤ R' := fun F' R' hR' j x =>
    hne F' R' (fun g i => hR' (g, i)) j x.1 x.2
  have heig0 : ∀ j, T j f₁.1 = η U j • f₁.1 := by
    intro j; apply LinearMap.ext; intro v
    rw [hT, LinearMap.smul_apply]
    exact hact U hU.aut (f₁.1 v) (hf₁U v) (fun x hx => funext fun g => hf₁K x hx v g) j
  have hnorm : ‖ι.symm (ev (g₀, i₀) f₁.1)‖ = 1 := by
    have : ev (g₀, i₀) f₁.1 = 1 := by
      rw [hev]
      show z₀⁻¹ * f.1 (b g₀ i₀) g₀ = 1
      exact inv_mul_cancel₀ hz
    rw [this, map_one, norm_one]
  let vv : ↥I → (W.Sp →ₗ[ℂ] (UA E a → ℂ)) := fun V => -Ft V.1
  have hop : ∀ j (φ : UA E a → ℂ) g, opOf (RU E a) (t j) φ g = ∑ h ∈ (t j).support, t j h * φ (g * h) := fun j φ g => by
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]
  have heig : ∀ (V : ↥I) j, T j (vv V) = η V.1 j • vv V := by
    rintro ⟨V, hV⟩ j
    obtain ⟨h1, h2, h3⟩ := hF V (Finset.mem_filter.1 hV).1
    have h : T j (Ft V) = η V j • Ft V := by
      apply LinearMap.ext; intro v
      funext g
      have e := congrFun (hact V h1 _ (h3 (M g) (M g) v) (fun x hx => h2.fix x hx.1 _ _ _) j) g
      rw [hT, hop, LinearMap.smul_apply, Pi.smul_apply, hFt]
      rw [hop, Pi.smul_apply] at e
      rw [← e]
      refine Finset.sum_congr rfl fun h hh => ?_
      rw [hFt, hM g h (ht j h hh).1 ((htv j h hh).2 v' (not_apart_self v'))]
    show T j (-Ft V) = η V j • -Ft V
    rw [map_neg, h, smul_neg]
  have hbound : ∀ x, ‖ι.symm (ev x (f₁.1 + ∑ V, vv V))‖ ≤ ε := by
    intro x
    have h1 : ev x (f₁.1 + ∑ V, vv V) = f₁.1 (b x.1 x.2) x.1 - B (M x.1) (M x.1) (b x.1 x.2) x.1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, hev, sub_eq_add_neg, ← hsum, Finset.sum_apply, ← Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_coe_sort I (fun V => ev x (-Ft V))]
      refine (Finset.sum_filter_of_ne fun V _ hV => ?_).trans (Finset.sum_congr rfl fun V _ => rfl)
      by_contra h
      push_neg at h
      refine hV ?_
      rw [map_neg, hev, hFt, h, Pi.zero_apply, neg_zero]
    rw [h1]
    exact hnear _ _
  obtain ⟨s, c, hs, hP⟩ := GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality l ι (W.Sp →ₗ[ℂ] (UA E a → ℂ)) (UA E a × X) Jx
    ↥I T ev hne' f₁.1 (η U) (g₀, i₀) heig0 hnorm vv (fun V => η V.1) heig ε hbound
  refine ⟨s, c, ?_, hP⟩
  intro z hz'
  obtain ⟨⟨V, hV⟩, rfl⟩ := hs z hz'
  obtain ⟨hV1, hV2⟩ := Finset.mem_filter.1 hV
  obtain ⟨h1, h2, h3⟩ := hF V hV1
  obtain ⟨mu, g1, g2, g3⟩ := hWt E a τ₀ W K ν d (F V) h2 V h1 h3 hV2
  refine ⟨V, mu, fun τ hτ => ?_, gapJ_of_near (mu τ₀) N (2 * d) g3 (Nat.lt_succ_self _), g1, rfl⟩
  have e : InfinitePlace.mk τ = InfinitePlace.mk τ₀ := by
    by_contra h
    exact hτ (g2 τ h)
  rcases InfinitePlace.mk_eq_iff.1 e with rfl | rfl
  · exact Or.inl hτ₀
  · refine Or.inr fun x hx => ?_
    have := hτ₀ x hx
    rwa [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj] at this

end UpperTheory.Gal.Wt

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TorFacts
noncomputable section

open Formalism.BasicNotions GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem tor_isUp (a k : ℕ) (z : Circle) : IsUp (tor a k z) := by
  intro i j hij
  rw [tor_coe]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

private theorem circ_mul_conj (z : Circle) : (starRingEnd ℂ) (z : ℂ) * (z : ℂ) = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

private theorem tor_unitary (a k : ℕ) (z : Circle) :
    ∃ u : Matrix.unitaryGroup (Fin a) ℂ, unitaryIncl a u = tor a k z := by
  set d : Fin a → ℂ := fun i => if (i : ℕ) < k then (z : ℂ) else 1 with hd
  have hdd : ∀ i, d i * (starRingEnd ℂ) (d i) = 1 := by
    intro i
    simp only [hd]
    split_ifs
    · rw [mul_comm]
      exact circ_mul_conj z
    · simp
  have hmem : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdd i
  refine ⟨⟨Matrix.diagonal d, hmem⟩, ?_⟩
  ext : 1
  rw [unitaryIncl_coe, tor_coe]

private theorem tor_chi {a : ℕ} (k : ℕ) (z : Circle) (κ : DomWeight a) :
    chi κ (tor a k z) = (z : ℂ) ^ psum κ k := by
  have hz : (z : ℂ) ≠ 0 := by simp
  simp only [chi, psum, tor_coe, Matrix.diagonal_apply_eq]
  rw [Finset.sum_filter]
  have key : ∀ s : Finset (Fin a), ∏ i ∈ s, (if (i : ℕ) < k then (z : ℂ) else 1) ^ κ.w i =
      (z : ℂ) ^ ∑ i ∈ s, (if (i : ℕ) < k then κ.w i else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hz]
      split_ifs <;> simp
  exact key _

private theorem tor_conj (a k : ℕ) (z : Circle) :
    Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (tor a k z) = tor a k z⁻¹ := by
  have hinv : (starRingEnd ℂ) (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv]
    exact eq_inv_of_mul_eq_one_left (circ_mul_conj z)
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, tor_coe, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [hinv]

theorem torFacts_of : TorFacts := fun a k z =>
  ⟨tor_isUp a k z, tor_unitary a k z, fun κ => tor_chi k z κ, tor_conj a k z⟩

end UpperTheory.Gal.Wt

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.Pieces
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem pev_map {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (P' : MvPolynomial (Fin a × Fin a) (Qbar l)) (h : GL (Fin a) ℂ) :
    ι.symm (pev (MvPolynomial.map ι.toRingHom P') h) =
      MvPolynomial.eval (fun p : Fin a × Fin a => ι.symm ((h : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)) P' := by
  induction P' using MvPolynomial.induction_on with
  | C c => simp [pev]
  | add p q hp hq =>
    simp only [pev, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [pev, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hp ⊢
    rw [hp]

theorem pieces_of (hS : SepPoly) (hN : NearSub) : Pieces := by
  intro l _ ι a Γ _ _ _ _ φ hcont hint Γ' hΓ' hker ε hε
  obtain ⟨H, hHo, hH⟩ := hN l ι a Γ φ hcont hint ε hε
  set K : Subgroup Γ := H ⊓ Γ' with hK
  have hKo : IsOpen (K : Set Γ) := by
    rw [hK, Subgroup.coe_inf]
    exact hHo.inter hΓ'
  have hkerK : φ.ker ≤ K := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨(hH g).2 ?_, hker hg⟩
    intro i j
    rw [MonoidHom.mem_ker.mp hg]
    simpa using hε.le
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  letI : Fintype (Γ ⧸ K) := Fintype.ofFinite _
  let c : Γ ⧸ K → Γ := fun q => q.out
  let v : Γ → (Fin a × Fin a → Qbar l) := fun g p => ι.symm ((φ g : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)
  have hv : Continuous v := continuous_pi fun p => hcont p.1 p.2
  have hKc : IsClosed (K : Set Γ) := Subgroup.isClosed_of_isOpen K hKo
  have hinj : ∀ g g', v g = v g' → g⁻¹ * g' ∈ K := by
    intro g g' hgg
    apply hkerK
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact ι.symm.injective (congrFun hgg (i, j))
  have hsep : ∀ q : Γ ⧸ K, ∃ P' : MvPolynomial (Fin a × Fin a) (Qbar l),
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∈ K}, ‖MvPolynomial.eval z P' - 1‖ ≤ ε) ∧
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∉ K}, ‖MvPolynomial.eval z P'‖ ≤ ε) := by
    intro q
    have hc1 : IsCompact (v '' {g | (c q)⁻¹ * g ∈ K}) :=
      (hKc.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hc2 : IsCompact (v '' {g | (c q)⁻¹ * g ∉ K}) :=
      (hKo.isClosed_compl.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hd : Disjoint (v '' {g | (c q)⁻¹ * g ∈ K}) (v '' {g | (c q)⁻¹ * g ∉ K}) := by
      rw [Set.disjoint_left]
      rintro z ⟨g, hg, rfl⟩ ⟨g', hg', hgg⟩
      apply hg'
      have hm := K.mul_mem hg (hinj g g' hgg.symm)
      simpa [mul_assoc] using hm
    exact hS (Qbar l) (Fin a × Fin a) _ _ hc1 hc2 hd ε hε
  choose P' hP1 hP2 using hsep
  refine ⟨Γ ⧸ K, inferInstance, c, fun q => MvPolynomial.map ι.toRingHom (P' q), ?_⟩
  intro g
  have hmem : ∀ q : Γ ⧸ K, (c q)⁻¹ * g ∈ K ↔ q = (g : Γ ⧸ K) := by
    intro q
    rw [← QuotientGroup.eq]
    simp [c]
  have h0 : (c (g : Γ ⧸ K))⁻¹ * g ∈ K := (hmem _).2 rfl
  refine ⟨(g : Γ ⧸ K), (Subgroup.mem_inf.mp h0).2, (hH _).1 (Subgroup.mem_inf.mp h0).1, ?_, ?_⟩
  · beta_reduce
    rw [map_sub, map_one, pev_map]
    exact hP1 _ _ ⟨g, h0, rfl⟩
  · intro q hq
    beta_reduce
    rw [pev_map]
    exact hP2 q _ ⟨g, fun h => hq ((hmem q).1 h), rfl⟩

end UpperTheory.Gal.Wt

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamProj
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem famProj_of : EvLem → SumRep → FamProj := by
  intro hEv hSum E _ _ _ a τ W K ν d B hB
  classical
  obtain ⟨S₀, hS₀, hBS₀⟩ := hB.fin
  let S := S₀ ⊓ autU E a
  haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le inf_le_left
  have hBS : ∀ y₁ y₂ v, B y₁ y₂ v ∈ S := fun y₁ y₂ v => ⟨hBS₀ y₁ y₂ v, hB.aut y₁ y₂ v⟩
  obtain ⟨t, ht, hind, hle⟩ := hSum E a S inferInstance fun φ hφ => hφ.2
  have hex : ∀ U : Submodule ℂ (UA E a → ℂ), ∃ p : (UA E a → ℂ) →ₗ[ℂ] (UA E a → ℂ), U ∈ t → (∀ φ, p φ ∈ U) ∧
      (∀ φ ∈ U, p φ = φ) ∧ ∀ V ∈ t, V ≠ U → ∀ φ ∈ V, p φ = 0 := fun U => by
    by_cases hU : U ∈ t
    · obtain ⟨C, hC, hc⟩ := (hind (Finset.mem_coe.2 hU)).symm.exists_isCompl
      refine ⟨U.subtype ∘ₗ Submodule.projectionOnto U C hc.symm, fun _ => ⟨fun φ => Subtype.property _, fun φ hφ =>
        congrArg Subtype.val (Submodule.projectionOnto_apply_left hc.symm ⟨φ, hφ⟩), fun V hV hne φ hφ => ?_⟩⟩
      have h0 : Submodule.projectionOnto U C hc.symm φ = 0 :=
        Submodule.projectionOnto_apply_of_mem_right hc.symm
          (hC (le_sSup (show V ∈ (t : Set (Submodule ℂ (UA E a → ℂ))) \ {U} from ⟨hV, hne⟩) hφ))
      simp [h0]
    · exact ⟨0, fun h => absurd h hU⟩
  choose p hp using hex
  have key : ∀ φ ∈ S, ∑ U ∈ t, p U φ = φ ∧ ∀ U ∈ t, ∀ x, p U (RU E a x φ) = RU E a x (p U φ) := by
    let P : Submodule ℂ (UA E a → ℂ) :=
      { carrier := {φ | ∑ U ∈ t, p U φ = φ ∧ ∀ U ∈ t, ∀ x, p U (RU E a x φ) = RU E a x (p U φ)}
        add_mem' := fun h1 h2 => ⟨by simp only [map_add (f := _), Finset.sum_add_distrib, h1.1, h2.1], fun U hU x => by
          simp only [map_add (f := _), h1.2 U hU x, h2.2 U hU x]⟩
        zero_mem' := ⟨by simp, fun U _ x => by simp⟩
        smul_mem' := fun c φ h => ⟨by simp only [map_smul, ← Finset.smul_sum, h.1], fun U hU x => by
          simp only [map_smul, h.2 U hU x]⟩ }
    refine fun φ hφ => (sSup_le (a := P) fun V hV ψ hψ => ⟨?_, fun U hU x => ?_⟩) (hle hφ)
    · rw [Finset.sum_eq_single_of_mem V hV fun U hU hne => (hp U hU).2.2 V hV hne.symm ψ hψ]
      exact (hp V hV).2.1 ψ hψ
    · have hx := (ht V hV).stable x ψ hψ
      by_cases h : V = U
      · subst h
        rw [(hp V hV).2.1 _ hx, (hp V hV).2.1 _ hψ]
      · rw [(hp U hU).2.2 V hV h _ hx, (hp U hU).2.2 V hV h _ hψ, map_zero]
  have hexp : ∀ (T : Submodule ℂ (Circle → ℂ)) (Φ : Circle → UA E a → ℂ), (∀ z, Φ z ∈ S) → (∀ g, (fun z => Φ z g) ∈ T) →
      ∀ U g, (fun z => p U (Φ z) g) ∈ T := fun T Φ h1 h2 U g =>
    hEv S (UA E a) Circle (fun g => LinearMap.proj g ∘ₗ S.subtype) (fun m hm => Subtype.ext (funext hm)) T
      (fun z => ⟨Φ z, h1 z⟩) h2 (LinearMap.proj g ∘ₗ p U ∘ₗ S.subtype)
  refine ⟨t, fun U y₁ y₂ => p U ∘ₗ B y₁ y₂, fun U hU => ⟨ht U hU, ⟨fun y₁ y₂ v => (ht U hU).aut _ ((hp U hU).1 _),
    fun k hk y₁ y₂ v => ?_, fun x y₁ y₂ v => ?_, fun b hb y₁ y₂ v => ?_, fun k x hx y₁ y₂ v g => ?_, fun k x hx y₂ v g => ?_,
    ⟨S.map (p U), inferInstance, fun y₁ y₂ v => ⟨_, hBS y₁ y₂ v, rfl⟩⟩⟩, fun y₁ y₂ v => (hp U hU).1 _⟩,
    fun y₁ y₂ v => (key _ (hBS y₁ y₂ v)).1⟩
  · show RU E a k (p U (B y₁ y₂ v)) = p U (B y₁ y₂ v)
    rw [← (key _ (hBS y₁ y₂ v)).2 U hU, hB.fix k hk]
  · show RU E a x (p U (B y₁ y₂ v)) = p U (B _ _ _)
    rw [← (key _ (hBS y₁ y₂ v)).2 U hU, hB.inf x]
  · show p U (B _ y₂ v) = chi ν b • p U (B y₁ y₂ v)
    rw [hB.up b hb, map_smul]
  · exact hexp _ _ (fun z => hBS _ _ _) (fun g => hB.le k x hx y₁ y₂ v g) U g
  · exact hexp _ _ (fun z => hBS _ _ _) (fun g => hB.ge k x hx y₂ v g) U g

end UpperTheory.Gal.Wt

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutCrit
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.autCrit_of :
    UpperTheory.Gal.Wt.AutCrit := by
  intro E _ _ _ a C hLev φ hL hC hI S hS hSub
  obtain ⟨N, hNo, hN1, hNC⟩ := hLev.isOpen
  set Wn : Set (UA E a) := GlobalTheory.EllU.finPart ⁻¹' N with hWn
  have hWo : IsOpen Wn := hNo.preimage GlobalTheory.EllU.continuous_finPart
  have hW1 : (1 : UA E a) ∈ Wn := by
    change GlobalTheory.EllU.finPart 1 ∈ N
    rw [map_one]; exact hN1
  have hkey : ∀ g, ∀ w ∈ Wn, φ (g * w) = φ (g * ((GlobalTheory.EllU.finPart w)⁻¹ * w)) := by
    intro g w hw
    have hkC : GlobalTheory.EllU.finPart w ∈ C := hNC ⟨hw, GlobalTheory.EllU.finPart_mem w⟩
    have hx := GlobalTheory.EllU.inv_finPart_mul_mem w
    have hcm := GlobalTheory.DefU.fin_mul_inf (GlobalTheory.EllU.finPart_mem w) hx
    have e : g * w = g * ((GlobalTheory.EllU.finPart w)⁻¹ * w) * GlobalTheory.EllU.finPart w := by
      rw [mul_assoc, ← hcm]; group
    rw [e, hC _ hkC]
  refine ⟨?_, hL, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => ?_
    have hc : Continuous fun y : UA E a => g⁻¹ * y := continuous_const.mul continuous_id
    have hX : Continuous fun y : UA E a => (⟨(GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y),
        GlobalTheory.EllU.inv_finPart_mul_mem _⟩ : infU E a) :=
      Continuous.subtype_mk (((GlobalTheory.EllU.continuous_finPart.comp hc).inv).mul hc) _
    have h0 : ContinuousAt (fun y : UA E a => φ (g * ((GlobalTheory.EllU.finPart (g⁻¹ * y))⁻¹ * (g⁻¹ * y)))) g :=
      ((hI g).comp hX).continuousAt
    refine h0.congr ?_
    have hm : Wn ∈ nhds (g⁻¹ * g) := by
      rw [inv_mul_cancel]; exact hWo.mem_nhds hW1
    filter_upwards [hc.continuousAt.preimage_mem_nhds hm] with y hy
    have := hkey g _ hy
    rw [mul_inv_cancel_left] at this
    exact this.symm
  · refine GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds ((RU E a).comp (finU (E := E) (n := a)).subtype) _ ?_
    have ho : IsOpen ((Subtype.val : finU (E := E) (n := a) → UA E a) ⁻¹' Wn) := hWo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (ho.mem_nhds hW1) fun k hk => ?_
    have hk' : (k : UA E a) ∈ C := by
      refine hNC ⟨?_, k.2⟩
      have : GlobalTheory.EllU.finPart (k : UA E a) ∈ N := hk
      rwa [GlobalTheory.EllU.finPart_of_finU k.2] at this
    funext g
    exact hC _ hk' g
  · haveI := hS
    refine Submodule.finiteDimensional_of_le (S₂ := S) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact hSub k k.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.PevExp
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem tor_entry_mem_expLe_one_expGe_zero (h : ExpBasic) (a k : ℕ) (A B : GL (Fin a) ℂ) (i j : Fin a) :
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpLe 1 ∧
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpGe 0 := by
  obtain ⟨_, _, hmono, hmon, hconst, _⟩ := h
  have heq : (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ l : Fin a, fun z : Circle => (A : Matrix (Fin a) (Fin a) ℂ) i l *
        ((if (l:ℕ) < k then (z:ℂ) else 1) * (B : Matrix (Fin a) (Fin a) ℂ) l j) := by
    funext z
    rw [Finset.sum_apply, Units.val_mul, Units.val_mul, Matrix.mul_apply]
    simp [tor_coe, Matrix.diagonal_mul]
  rw [heq]
  constructor
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).1 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hmono 0 1 (by norm_num)).1
        (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).1 using 1
      funext z
      simp [hl]
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmono 0 1 (by norm_num)).2
        (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).2 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).2 using 1
      funext z
      simp [hl]

private theorem pow_mem_expLe_expGe_of_mem (h : ExpBasic) (f : Circle → ℂ) (hf : f ∈ ExpLe 1 ∧ f ∈ ExpGe 0) (n : ℕ) :
    (fun z => f z ^ n) ∈ ExpLe (n : ℤ) ∧ (fun z => f z ^ n) ∈ ExpGe 0 := by
  obtain ⟨hmulL, hmulG, _, _, hconst, _⟩ := h
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    exact hconst 1
  | succ n ih =>
    have e : (fun z => f z ^ (n + 1)) = fun z => (fun z => f z ^ n) z * f z := by
      funext z
      exact pow_succ _ _
    rw [e]
    constructor
    · have := hmulL _ _ _ _ ih.1 hf.1
      push_cast
      exact this
    · have := hmulG _ _ _ _ ih.2 hf.2
      simpa using this

private theorem prod_pow_mem_expLe_sum_expGe {ι : Type} [DecidableEq ι] (h : ExpBasic) (e : ι → Circle → ℂ)
    (he : ∀ i, e i ∈ ExpLe 1 ∧ e i ∈ ExpGe 0) (d : ι → ℕ) (S : Finset ι) :
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpLe ((∑ i ∈ S, d i : ℕ) : ℤ) ∧
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpGe 0 := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, Nat.cast_zero]
    exact h.2.2.2.2.1 1
  | insert x S hx ih =>
    have hp := pow_mem_expLe_expGe_of_mem h (e x) (he x) (d x)
    have e1 : (fun z => ∏ i ∈ insert x S, e i z ^ d i) =
        fun z => (fun z => e x z ^ d x) z * (fun z => ∏ i ∈ S, e i z ^ d i) z := by
      funext z
      exact Finset.prod_insert hx
    rw [e1]
    constructor
    · have := h.1 _ _ _ _ hp.1 ih.1
      rw [Finset.sum_insert hx, Nat.cast_add]
      exact this
    · have := h.2.1 _ _ _ _ hp.2 ih.2
      simpa using this

theorem UpperTheory.Gal.Wt.pevExp_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.PevExp := by
  intro h a k P A B
  classical
  let e : Fin a × Fin a → Circle → ℂ := fun p z =>
    ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p.1 p.2
  have he : ∀ p, e p ∈ ExpLe 1 ∧ e p ∈ ExpGe 0 := fun p => tor_entry_mem_expLe_one_expGe_zero h a k A B p.1 p.2
  have hsum : (fun z => pev P (A * (tor a k z * B))) =
      ∑ d ∈ P.support, fun z => AddMonoidAlgebra.coeff P d * ∏ i ∈ d.support, e i z ^ d i := by
    funext z
    rw [Finset.sum_apply]
    simp only [pev]
    rw [MvPolynomial.eval_eq]
  rw [hsum]
  constructor
  · refine Submodule.sum_mem _ fun d hd => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).1
    have hle : ((∑ i ∈ d.support, d i : ℕ) : ℤ) ≤ (P.totalDegree : ℤ) := by
      exact_mod_cast MvPolynomial.le_totalDegree hd
    have hm := (h.2.2.1 _ _ hle).1 hp
    convert Submodule.smul_mem _ (AddMonoidAlgebra.coeff P d) hm using 1
  · refine Submodule.sum_mem _ fun d _ => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).2
    convert Submodule.smul_mem _ (AddMonoidAlgebra.coeff P d) hp using 1
end

namespace UpperTheory.Gal.Wt

theorem expBasic_holds : ExpBasic := expBasic_of
theorem expDisj_holds : ExpDisj := expDisj_of
theorem evLem_holds : EvLem := evLem_of
theorem pevExp_holds : PevExp := pevExp_of expBasic_holds
theorem dom_holds : Dom := dom_of
theorem sqExp_holds : SqExp := sqExp_h expBasic_holds evLem_holds dom_holds
theorem topUp_holds : TopUp := topUp_of
theorem torFacts_holds : TorFacts := torFacts_of
theorem qR_holds : QR := qR_of
theorem wtBd_holds : WtBd := wtBd_of expBasic_holds expDisj_holds sqExp_holds topUp_holds torFacts_holds
theorem wExp_holds : WExp := wExp_h expBasic_holds sqExp_holds torFacts_holds
theorem rFinEx_holds : RFinEx := rFinEx_of
theorem deltaNear_holds : DeltaNear := deltaNear_h
theorem autCrit_holds : AutCrit := autCrit_of
theorem autMul_holds : AutMul := autMul_of
theorem nrmAut_holds : NrmAut := nrmAut_of autCrit_holds
theorem famOfA_holds : FamOfA := famOfA_of autMul_holds nrmAut_holds rFinEx_holds
theorem sumRep_holds : SumRep := sumRep_of
theorem neatLev_holds : NeatLev := neatLev_of
theorem ellC_holds : EllC := ellC_of
theorem twist_holds : Twist := twist_of autCrit_holds
theorem twistBd_holds : TwistBd := twistBd_of twist_holds
theorem ladic_weight_embedding_over_place : Kap0 := ladic_weight_at_embedding_over_place
theorem kaplFin_holds : KaplFin := kaplFin_of
theorem kapl_holds : Kapl := kapl_of kaplFin_holds
theorem sepPoly_holds : SepPoly := sepPoly_of kapl_holds
theorem nearSub_holds : NearSub := nearSub_of
theorem pieces_holds : Pieces := pieces_of sepPoly_holds nearSub_holds
theorem famOf_holds : FamOf := famOf_of expBasic_holds pevExp_holds sqExp_holds topUp_holds wExp_holds famOfA_holds
theorem famEx_holds : FamEx := famEx_of neatLev_holds ellC_holds twist_holds twistBd_holds ladic_weight_embedding_over_place pieces_holds deltaNear_holds famOf_holds
theorem famProj_holds : FamProj := famProj_of evLem_holds sumRep_holds
theorem famSum_holds : FamSum := famSum_of expBasic_holds evLem_holds torFacts_holds qR_holds wtBd_holds embProj_holds
theorem famWt_holds : FamWt := famWt_of famOff_holds famSum_holds

theorem wtLacEx_holds : UpperTheory.Gal.Int.Cong.WtLacEx := top_of famEx_holds famProj_holds famWt_holds

end UpperTheory.Gal.Wt
