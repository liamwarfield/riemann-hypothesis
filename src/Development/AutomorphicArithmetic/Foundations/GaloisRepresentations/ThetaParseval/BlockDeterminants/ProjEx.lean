module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
open GlobalTheory.UnitaryBC GlobalTheory.DefU

private theorem proj_of_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G → V →ₗ[ℂ] V)
    (A : Submodule ℂ V) (S : Set (Submodule ℂ V))
    (hSA : ∀ U ∈ S, U ≤ A) (hSs : ∀ U ∈ S, ∀ x, ∀ v ∈ U, ρ x v ∈ U)
    (hSi : ∀ U ∈ S, ∀ N ≤ U, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → N = ⊥ ∨ N = U)
    (hAS : A ≤ sSup S) (ψ : V) (hψA : ψ ∈ A) (hψ : ψ ≠ 0) :
    ∃ U ∈ S, ∃ pr : V →ₗ[ℂ] V, pr ψ ≠ 0 ∧ ∀ f ∈ A, pr f ∈ U ∧ ∀ x, pr (ρ x f) = ρ x (pr f) := by
  classical
  let P : Set (Submodule ℂ V) := {C | C ≤ A ∧ (∀ x, ∀ v ∈ C, ρ x v ∈ C) ∧ ψ ∉ C}
  have hbot : (⊥ : Submodule ℂ V) ∈ P :=
    ⟨bot_le, fun x v hv => by rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact zero_mem _,
      fun h => hψ ((Submodule.mem_bot ℂ).1 h)⟩
  obtain ⟨C, -, hC⟩ := zorn_le_nonempty₀ P (fun c hcP hc y hy => by
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    have hne : c.Nonempty := ⟨y, hy⟩
    refine ⟨sSup c, ⟨sSup_le fun z hz => (hcP hz).1, fun x v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact le_sSup hz ((hcP hz).2.1 x v hvz)
    · obtain ⟨z, hz, hvz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcP hz).2.2 hvz) ⊥ hbot
  obtain ⟨hCA, hCs, hψC⟩ := hC.prop
  have hsup : ∀ N ≤ A, (∀ x, ∀ v ∈ N, ρ x v ∈ N) → ¬ N ≤ C → ψ ∈ C ⊔ N := by
    intro N hNA hNs hNC
    by_contra hn
    have hm : C ⊔ N ∈ P := ⟨sup_le hCA hNA, fun x v hv => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hCs x a ha) (hNs x b hb), hn⟩
    exact hNC (le_sup_right.trans (hC.le_of_ge hm le_sup_left))
  obtain ⟨U, hUS, hUC⟩ : ∃ U ∈ S, ¬ U ≤ C := by
    by_contra hn
    push_neg at hn
    exact hψC (sSup_le hn (hAS hψA))
  have hUs := hSs U hUS
  have hdisj : C ⊓ U = ⊥ := by
    rcases hSi U hUS (C ⊓ U) inf_le_right (fun x v hv => ⟨hCs x v hv.1, hUs x v hv.2⟩) with h | h
    · exact h
    · exact absurd (inf_eq_right.1 h) hUC
  have hψU := hsup U (hSA U hUS) hUs hUC
  have hAle : A ≤ C ⊔ U := by
    refine hAS.trans (sSup_le fun Y hY => ?_)
    by_cases hYC : Y ≤ C
    · exact hYC.trans le_sup_left
    have hYs := hSs Y hY
    rcases hSi Y hY ((C ⊔ U) ⊓ Y) inf_le_right (fun x v hv => ⟨by
        obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hv.1
        rw [← e, map_add (f := _)]
        exact Submodule.add_mem_sup (hCs x a ha) (hUs x b hb), hYs x v hv.2⟩) with h | h
    · exfalso
      obtain ⟨c, hc, y, hy, e⟩ := Submodule.mem_sup.1 (hsup Y (hSA Y hY) hYs hYC)
      have hyCU : y ∈ C ⊔ U := by
        have : y = ψ - c := by rw [← e]; abel
        rw [this]
        exact sub_mem hψU (Submodule.mem_sup_left hc)
      have hy0 : y = 0 := (Submodule.mem_bot ℂ).1 (h ▸ (⟨hyCU, hy⟩ : y ∈ (C ⊔ U) ⊓ Y))
      rw [hy0, add_zero] at e
      exact hψC (e ▸ hc)
    · exact inf_eq_right.1 h
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (C ⊔ U)
  have hc : IsCompl U (C ⊔ D) := by
    refine ⟨Submodule.disjoint_def.2 fun u hu hu' => ?_, ?_⟩
    · obtain ⟨c, hc, d, hd, e⟩ := Submodule.mem_sup.1 hu'
      have hdCU : d ∈ C ⊔ U := by
        have : d = u - c := by rw [← e]; abel
        rw [this]
        exact sub_mem (Submodule.mem_sup_right hu) (Submodule.mem_sup_left hc)
      have hd0 : d = 0 := Submodule.disjoint_def.1 hD.disjoint d hdCU hd
      rw [hd0, add_zero] at e
      have : u ∈ C ⊓ U := ⟨e ▸ hc, hu⟩
      rw [hdisj] at this
      exact (Submodule.mem_bot ℂ).1 this
    · rw [codisjoint_iff, ← top_le_iff, ← hD.sup_eq_top]
      exact sup_le (sup_le (le_sup_left.trans le_sup_right) le_sup_left) (le_sup_right.trans le_sup_right)
  let pr : V →ₗ[ℂ] V := U.subtype ∘ₗ Submodule.linearProjOfIsCompl U (C ⊔ D) hc
  have hprU : ∀ u ∈ U, pr u = u := fun u hu =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨u, hu⟩)
  have hprC : ∀ c ∈ C, pr c = 0 := fun c hc' => by
    have h0 : Submodule.linearProjOfIsCompl U (C ⊔ D) hc c = 0 :=
      Submodule.projectionOnto_apply_of_mem_right hc (Submodule.mem_sup_left hc')
    simp [pr, h0]
  have hform : ∀ c ∈ C, ∀ u ∈ U, pr (c + u) = u := fun c hc' u hu => by
    rw [map_add (f := _), hprC c hc', hprU u hu, zero_add]
  refine ⟨U, hUS, pr, ?_, fun f hf => ?_⟩
  · obtain ⟨c, hc', u, hu, e⟩ := Submodule.mem_sup.1 (hAle hψA)
    rw [← e, hform c hc' u hu]
    intro h0
    rw [h0, add_zero] at e
    exact hψC (e ▸ hc')
  · obtain ⟨c, hc', u, hu, rfl⟩ := Submodule.mem_sup.1 (hAle hf)
    refine ⟨by rw [hform c hc' u hu]; exact hu, fun x => ?_⟩
    rw [hform c hc' u hu, map_add (f := _), hform _ (hCs x c hc') _ (hUs x u hu)]

theorem UpperTheory.TP.projEx :
    UpperTheory.TP.ProjEx := by
  intro E _ _ _ d ψ hψ hψ0
  obtain ⟨B₀, -, -, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E d
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (autU E d).subtype (autU E d).ker_subtype
  have hpv : ∀ (φ : UA E d → ℂ) (h : IsAutFormU φ), p φ = ⟨φ, h⟩ := fun φ h =>
    LinearMap.congr_fun hp (⟨φ, h⟩ : autU E d)
  let B : (UA E d → ℂ) →ₗ⋆[ℂ] (UA E d → ℂ) →ₗ[ℂ] ℂ := (B₀.compl₂ p).comp p
  have hB : ∀ φ φ', B φ φ' = B₀ (p φ) (p φ') := fun _ _ => rfl
  have hsum : ∀ φ : UA E d → ℂ, IsAutFormU φ → φ ∈ sSup {U : Submodule ℂ (UA E d → ℂ) | IsAutRepU U} := by
    intro φ hφ
    have h := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E d B (fun f hf h0 => by
        rw [hB, hpv f hf] at h0
        exact congrArg Subtype.val (hd _ h0))
      (fun x f g hf hg => by
        rw [hB, hB, hpv f hf, hpv g hg, hpv _ (RU_mem_autU x f hf), hpv _ (RU_mem_autU x g hg)]
        exact hi x ⟨f, hf⟩ ⟨g, hg⟩) φ hφ
    exact (iSup_le fun σ => le_sSup σ.2 : _ ≤ sSup {U : Submodule ℂ (UA E d → ℂ) | IsAutRepU U}) h
  obtain ⟨U, hU, pr, h1, h2⟩ := proj_of_sum (fun x => RU E d x) (autU E d)
    {U | IsAutRepU U} (fun U hU φ hφ => hU.aut φ hφ) (fun U hU => hU.stable)
    (fun U hU => hU.irred) (fun φ hφ => hsum φ hφ) ψ hψ hψ0
  exact ⟨U, pr, hU, h1, fun f hf => h2 f hf⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.AbsNe
open MeasureTheory

theorem UpperTheory.TP.absNe :
    UpperTheory.TP.AbsNe := by
  intro A B C _ _ _ μA μB μC _ _ _ H K hH hK hH0 hHtop hKtop f m s c₀ κ r w hκ hr hf hoff hon hm hK1 hbd hlt
  have hG := hf.integral_prod_right
  have hGeq : (fun y : B × C => ∫ x, f (x, y) ∂μA) =
      fun y => H.indicator (fun _ => (1 : ℂ)) y.1 * (κ * (s y.2 * c₀ y.2)) := by
    funext ⟨b, c⟩
    by_cases hb : b ∈ H
    · have e : (fun x => f (x, b, c)) = fun x => s c * m x c := funext fun x => hon x c b hb
      simp only [e, integral_const_mul, hm, Set.indicator_of_mem hb, one_mul]
      ring
    · have e : (fun x => f (x, b, c)) = fun _ => (0 : ℂ) := funext fun x => hoff x b c hb
      simp [e, hb]
  have hv : Integrable (fun c => s c * c₀ c) μC := by
    rw [hGeq] at hG
    have hae := hG.prod_right_ae
    by_contra hni
    have hnot : ∀ᵐ b ∂μB, b ∉ H := by
      filter_upwards [hae] with b hb hbH
      apply hni
      have h1 : Integrable (fun c => κ * (s c * c₀ c)) μC := by simpa [hbH] using hb
      have h2 := h1.const_mul κ⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hκ] using h2
    have h0 := ae_iff.mp hnot
    simp only [not_not, Set.setOf_mem_eq] at h0
    exact hH0 h0
  have hI : ∫ y, f y ∂μA.prod (μB.prod μC) =
      (∫ b, H.indicator (fun _ => (1 : ℂ)) b ∂μB) * (κ * ∫ c, s c * c₀ c ∂μC) := by
    rw [integral_prod_symm _ hf, hGeq,
      integral_prod_mul (fun b => H.indicator (fun _ => (1 : ℂ)) b) (fun c => κ * (s c * c₀ c)),
      integral_const_mul]
  have hind : ∫ b, H.indicator (fun _ => (1 : ℂ)) b ∂μB ≠ 0 := by
    rw [integral_indicator hH, setIntegral_const]
    simp [Measure.real, ENNReal.toReal_eq_zero_iff, hH0, hHtop]
  have hp : ∫ c, s c * c₀ c ∂μC ≠ 0 := by
    intro h0
    have hsplit := integral_add_compl hK hv
    rw [h0] at hsplit
    have hKint : ∫ c in K, s c * c₀ c ∂μC = ∫ c in K, (r : ℂ) ∂μC :=
      setIntegral_congr_fun hK fun c hc => by simp [(hK1 c hc).1, (hK1 c hc).2]
    have eq : ‖∫ c in K, s c * c₀ c ∂μC‖ₑ = ‖∫ c in Kᶜ, s c * c₀ c ∂μC‖ₑ := by
      rw [eq_neg_of_add_eq_zero_left hsplit, enorm_neg]
    have lower : ‖∫ c in K, s c * c₀ c ∂μC‖ₑ = μC K * ENNReal.ofReal r := by
      rw [hKint, setIntegral_const, ← ofReal_norm_eq_enorm]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr]
      rw [Measure.real, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hKtop]
    have upper : ‖∫ c in Kᶜ, s c * c₀ c ∂μC‖ₑ ≤ (∫⁻ c in Kᶜ, w c ∂μC) * ENNReal.ofReal r := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun c => ?_
      rw [enorm_mul]
      refine mul_le_mul' (hbd c).2 ?_
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hbd c).1
    have strict := ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top hlt
    rw [eq] at lower
    exact absurd (lower ▸ upper) (not_le.mpr strict)
  rw [hI]
  exact mul_ne_zero hind (mul_ne_zero hκ hp)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.AbsIso
namespace UpperTheory.TP

theorem absIso : AbsIso := by
  intro G V T _ _ _ _ _ ρ U H τ hG hinv hU hτ f hf0 hfU hfe u hu
  classical
  let ρH : Representation ℂ H V := ρ.comp H.subtype
  let R := MonoidAlgebra ℂ H
  haveI : IsSimpleModule R τ.asModule := (Representation.irreducible_iff_isSimpleModule_asModule τ).1 hτ
  let Z : Set G := {z | ∀ h' ∈ H, Commute z h'}
  let S : Set V := {v | ∃ z ∈ Z, ∃ x, v = ρ z (f x)}
  have hmul : ∀ (a b : G) v, ρ (a * b) v = ρ a (ρ b v) := fun a b v => by rw [map_mul]; rfl
  have hze : ∀ z ∈ Z, ∀ (h : H) y, ρ z (f (τ h y)) = ρ h (ρ z (f y)) := fun z hz h y => by
    rw [hfe, ← hmul, ← hmul, (hz h h.2).eq]
  have hS : Submodule.span ℂ S = U := by
    have hle : Submodule.span ℂ S ≤ U := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨z, -, x, rfl⟩
      exact hinv z _ (hfU x)
    refine (hU _ hle ?_).resolve_left ?_
    · intro g v hv
      obtain ⟨h, hh, hc⟩ := hG g
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨z, hz, x, rfl⟩ := hv
        have hw : h⁻¹ * g * z ∈ Z := fun h' hh' => (hc h' hh').mul_left (hz h' hh')
        refine Submodule.subset_span ⟨_, hw, τ ⟨h, hh⟩ x, ?_⟩
        rw [hfe, ← hmul, ← hmul]
        have e : g * z = h⁻¹ * g * z * h := by rw [(hw h hh).eq]; group
        change ρ (g * z) (f x) = ρ (h⁻¹ * g * z * h) (f x)
        rw [← e]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha
    · intro h0
      apply hf0
      ext x
      have : ρ 1 (f x) ∈ Submodule.span ℂ S := Submodule.subset_span ⟨1, fun h' _ => Commute.one_left h', x, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      simpa using this
  refine ⟨?_, fun hu0 => ?_⟩
  · rw [← hS] at hu
    obtain ⟨m, a, g, rfl⟩ := Submodule.mem_span_set'.1 hu
    choose z hz x hx using fun i => (g i).2
    refine ⟨m, fun i => ρ (z i) ∘ₗ f, fun i => a i • x i, fun i y => hinv _ _ (hfU y), fun i h y => hze _ (hz i) h y, ?_⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hx i]
  · let M := ρH.asModule
    let I := isotypicComponent R M τ.asModule
    let I' : Submodule ℂ V := (I.restrictScalars ℂ).comap ρH.asModuleEquiv.symm.toLinearMap
    have hUI : U ≤ I' := by
      rw [← hS]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨z, hz, x, rfl⟩
      let F : τ.asModule →ₗ[R] M := Representation.IntertwiningMap.equivLinearMapAsModule τ ρH
        ⟨ρ z ∘ₗ f, fun h => LinearMap.ext fun y => hze z hz h y⟩
      have h1 : LinearMap.range F ≤ I := by
        rcases LinearMap.injective_or_eq_zero F with hf | hf
        · exact le_sSup ⟨(LinearEquiv.ofInjective F hf).symm⟩
        · simp [hf]
      exact h1 ⟨τ.asModuleEquiv.symm x, rfl⟩
    obtain ⟨ι, ⟨e⟩⟩ := (IsIsotypicOfType.isotypicComponent R M τ.asModule).linearEquiv_finsupp
    have hne : e ⟨ρH.asModuleEquiv.symm u, hUI hu⟩ ≠ 0 := by
      intro h0
      have := e.injective (h0.trans (map_zero e).symm)
      apply hu0
      simpa using congrArg Subtype.val this
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
    let Q : I →ₗ[R] τ.asModule := Finsupp.lapply i ∘ₗ e.toLinearMap
    let q0 : I' →ₗ[ℂ] T :=
      { toFun := fun v => τ.asModuleEquiv (Q ⟨ρH.asModuleEquiv.symm v.1, v.2⟩)
        map_add' := fun a b => by
          rw [← map_add (f := _)]; congr 1; rw [← map_add (f := _)]; congr 1
        map_smul' := fun c a => by
          rw [RingHom.id_apply, ← map_smul, ← LinearMap.map_smul_of_tower]; congr 2 }
    obtain ⟨p, hp⟩ := LinearMap.exists_extend q0
    have hpv : ∀ (v : V) (hv : v ∈ I'), p v = τ.asModuleEquiv (Q ⟨ρH.asModuleEquiv.symm v, hv⟩) :=
      fun v hv => LinearMap.congr_fun hp ⟨v, hv⟩
    refine ⟨p, ?_, fun h y hy => ?_⟩
    · rw [hpv u (hUI hu)]
      intro h0
      exact hi (τ.asModuleEquiv.injective (h0.trans (map_zero _).symm))
    · have hy' := hUI hy
      have hhy := hUI (hinv h y hy)
      rw [hpv _ hy', hpv _ hhy]
      have e1 : (⟨ρH.asModuleEquiv.symm (ρ h y), hhy⟩ : I) = MonoidAlgebra.of ℂ H h • (⟨ρH.asModuleEquiv.symm y, hy'⟩ : I) := by
        ext
        exact Representation.asModuleEquiv_symm_map_rho ρH h y
      rw [e1, map_smul]
      exact (Representation.asModuleEquiv_map_smul τ _ _).trans (by simp)

end UpperTheory.TP
end
