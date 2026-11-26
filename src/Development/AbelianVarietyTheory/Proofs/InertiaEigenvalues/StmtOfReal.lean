module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfIndepMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StmtOfReal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantTwCoef
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
open ReciprocityTheory.Def (Z1 H1)

namespace GlobalTheory.TopSteps.CharAllCoef

section General

variable {O G : Type} [CommRing O] [Group G] [TopologicalSpace G]

theorem exists_mapH1_eq {M' M M'' : Type} [AddCommGroup M'] [Module O M'] [AddCommGroup M] [Module O M]
    [AddCommGroup M''] [Module O M''] {π' : Representation O G M'} {π : Representation O G M}
    {π'' : Representation O G M''} (f : M' →ₗ[O] M) (hf : ∀ g m, f (π' g m) = π g (f m))
    (q : M →ₗ[O] M'') (hq : ∀ g m, q (π g m) = π'' g (q m)) (hfi : Function.Injective f)
    (hqs : Function.Surjective q) (hex : Function.Exact f q)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (c : H1 π ⊤) (hc : mapH1 q hq c = 0) :
    ∃ c₀ : H1 π' ⊤, mapH1 f hf c₀ = c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨b'', -, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hc
  obtain ⟨b, rfl⟩ := hqs b''
  have hb' : ∀ g, π'' g (q b) - q b = q ((z : G → M) g) := fun g => congrFun hb g
  have hr : ∀ g, ∃ y, f y = (z : G → M) g - (π g b - b) := fun g =>
    (hex _).mp (by rw [map_sub, map_sub, hq, hb', sub_self])
  choose w hw using hr
  have hwlc : IsLocallyConstant w := by
    have h1 : IsLocallyConstant fun g => (z : G → M) g - (π g b - b) :=
      z.2.1.1.sub ((hlc b).sub (IsLocallyConstant.const b))
    refine IsLocallyConstant.desc w f ?_ hfi
    have : f ∘ w = fun g => (z : G → M) g - (π g b - b) := funext hw
    rw [this]; exact h1
  refine ⟨Submodule.Quotient.mk ⟨w, ⟨hwlc, fun _ => Submodule.mem_top⟩, ?_⟩, ?_⟩
  · funext x
    change π' x.1 (w x.2) - w (x.1 * x.2) + w x.1 = 0
    apply hfi
    rw [map_add (f := _), map_sub, hf, hw, hw, hw, cocycle_mul, map_zero, map_mul]
    simp only [map_sub, Module.End.mul_apply]
    abel
  · refine (Submodule.Quotient.eq _).mpr ⟨-b, Submodule.mem_top, ?_⟩
    funext g
    change π g (-b) - -b = f (w g) - (z : G → M) g
    rw [hw, map_neg]
    abel

theorem exists_res_inj [IsDomain O] [IsDiscreteValuationRing O] {lam : O} (hl : Irreducible lam)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] [Nontrivial X] :
    ∃ f : (O ⧸ Ideal.span {lam}) →ₗ[O] X, Function.Injective f ∧ f ≠ 0 := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {lam} := hl.maximalIdeal_eq
  obtain ⟨x, hx0, hx⟩ : ∃ x : X, x ≠ 0 ∧ lam • x = 0 := by
    by_contra h
    push Not at h
    have hinj : Function.Injective (fun x : X => lam • x) := by
      intro a b hab
      by_contra hne
      exact h (a - b) (sub_ne_zero.mpr hne) (by rw [smul_sub]; exact sub_eq_zero.mpr hab)
    have hsurj := Finite.surjective_of_injective hinj
    have : (⊤ : Submodule O X) = ⊥ := by
      refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {lam}) ⊤ Module.Finite.fg_top ?_ ?_
      · intro y _
        obtain ⟨y', rfl⟩ := hsurj y
        exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
      · rw [← hmax, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact top_ne_bot this
  refine ⟨Submodule.liftQ (Ideal.span {lam}) (LinearMap.toSpanSingleton O X x) ?_, ?_, ?_⟩
  · rw [Ideal.span, Submodule.span_le]
    rintro _ rfl
    exact hx
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hy' : y • x = 0 := hy
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [← hmax]
    intro hu
    exact hx0 (hu.smul_eq_zero.mp hy')
  · intro h
    have : (1 : O) • x = 0 := LinearMap.congr_fun h (Submodule.Quotient.mk 1)
    exact hx0 (by simpa using this)

theorem cls_eq_zero [IsDomain O] [IsDiscreteValuationRing O] {lam : O} (hl : Irreducible lam)
    {M : Type} [AddCommGroup M] [Module O M] [Module.Flat O M] (W : Representation O G M) (χ : G →* Oˣ)
    (cls : ∀ (X : Type) [AddCommGroup X] [Module O X], Set (H1 (twCoef W χ X) ⊤))
    (hlc : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X] (m : M ⊗[O] X),
      IsLocallyConstant fun g => twCoef W χ X g m)
    (h0 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X], 0 ∈ cls X)
    (hmap : ∀ (X : Type) [AddCommGroup X] [Module O X] [Finite X]
      (X' : Type) [AddCommGroup X'] [Module O X'] [Finite X'] (f : X →ₗ[O] X') (c : H1 (twCoef W χ X) ⊤),
      (c ∈ cls X → coefH1 W χ f c ∈ cls X') ∧ (Function.Injective f → coefH1 W χ f c ∈ cls X' → c ∈ cls X))
    (hres : ∀ (s : ℕ) (c : Fin s → H1 (twCoef W χ (O ⧸ Ideal.span {lam})) ⊤),
      (∀ a, c a ∈ cls (O ⧸ Ideal.span {lam})) → IndepMod lam c → s ≤ 0)
    (X : Type) [AddCommGroup X] [Module O X] [Finite X] : cls X = {0} := by
  have hk : ∀ c ∈ cls (O ⧸ Ideal.span {lam}), c = 0 := by
    intro c hc
    by_contra hne
    have := hres 1 (fun _ => c) (fun _ => hc) (by
      intro x hx a
      rw [Fin.sum_univ_one] at hx
      rw [Subsingleton.elim a 0, ← Ideal.mem_span_singleton, ← hl.maximalIdeal_eq]
      intro hu
      exact hne (hu.smul_eq_zero.mp hx))
    omega
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨h0 X, ?_⟩
  generalize hn : Nat.card X = n
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    intro c hc
    rcases subsingleton_or_nontrivial X with hX | hX
    · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      have : z = 0 := Subtype.ext (funext fun g => Subsingleton.elim _ _)
      rw [this, Submodule.Quotient.mk_zero]
    · obtain ⟨f, hfi, hf0⟩ := exists_res_inj hl X
      haveI : Finite (O ⧸ Ideal.span {lam}) := Finite.of_injective f hfi
      haveI : Finite (X ⧸ LinearMap.range f) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
      have hlt : Nat.card (X ⧸ LinearMap.range f) < n := by
        rw [← hn, Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)]
        haveI : Nontrivial (LinearMap.range f) :=
          Submodule.nontrivial_iff_ne_bot.mpr (fun h => hf0 (LinearMap.range_eq_bot.mp h))
        have h1 : 1 < Nat.card (LinearMap.range f) := Finite.one_lt_card
        have h2 : 0 < Nat.card (X ⧸ LinearMap.range f) := Nat.card_pos
        nlinarith
      have hq := ih _ hlt (X ⧸ LinearMap.range f) rfl _
        ((hmap X _ (LinearMap.range f).mkQ c).1 hc)
      obtain ⟨c₀, hc₀⟩ := exists_mapH1_eq (π' := twCoef W χ (O ⧸ Ideal.span {lam})) (f.lTensor M)
        (fun g m => by
          induction m using TensorProduct.induction_on with
          | zero => simp
          | tmul a x => simp [coefRep_tmul]
          | add a b ha hb => simp only [map_add (f := _), ha, hb])
        ((LinearMap.range f).mkQ.lTensor M) _
        (Module.Flat.lTensor_preserves_injective_linearMap f hfi)
        (LinearMap.lTensor_surjective M (Submodule.mkQ_surjective _))
        (lTensor_exact M (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _))
        (hlc X) c hq
      have hc₀' : coefH1 W χ f c₀ = c := hc₀
      have := hk c₀ ((hmap _ X f c₀).2 hfi (hc₀' ▸ hc))
      rw [← hc₀', this, map_zero]

theorem isLocallyConstant_smul {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] {Y : Type} [AddCommGroup Y] [Module O Y]
    [Finite Y] (m : Y) : IsLocallyConstant fun a : ℤ_[l] => algebraMap ℤ_[l] O a • m := by
  rw [IsLocallyConstant.iff_exists_open]
  intro a
  have hN : (Nat.card Y : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  refine ⟨Metric.ball a ‖(Nat.card Y : ℤ_[l])‖, Metric.isOpen_ball, Metric.mem_ball_self (norm_pos_iff.mpr hN), ?_⟩
  intro b hb
  rw [mem_ball_iff_norm] at hb
  have hd : (Nat.card Y : ℤ_[l]) ∣ b - a := by
    rcases ValuationRing.dvd_total (Nat.card Y : ℤ_[l]) (b - a) with h | ⟨d, hd⟩
    · exact h
    · exfalso
      rw [hd, norm_mul] at hb
      have := PadicInt.norm_le_one d
      nlinarith [norm_nonneg (b - a)]
  obtain ⟨d, hd⟩ := hd
  rw [← sub_eq_zero, ← sub_smul, ← map_sub, hd, mul_comm, map_mul, mul_smul, map_natCast,
    Nat.cast_smul_eq_nsmul, card_nsmul_eq_zero', smul_zero]

end General

theorem isLocallyConstant_twCoef {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [Algebra ℤ_[l] O] (Γ : GalData G Qp LL O) (χ : G → ℤ_[l]ˣ) (hc : Continuous χ)
    (hε : ∀ g, (Γ.ε g : O) = algebraMap ℤ_[l] O (χ g)) (c : ℕ)
    (Y : Type) [AddCommGroup Y] [Module O Y] [Finite Y] (m : O ⊗[O] Y) :
    IsLocallyConstant fun g => twCoef (Γ.Wchi c) Γ.χ₁ Y g m := by
  haveI : Finite (O ⊗[O] Y) := Finite.of_equiv _ (TensorProduct.lid O Y).toEquiv.symm
  have hε' : ∀ g, Γ.ε g = Units.map (algebraMap ℤ_[l] O : ℤ_[l] →* O) (χ g) := fun g => Units.ext (hε g)
  have h1 : Continuous fun g : G => (((χ g) ^ (-((c : ℤ) - 1)) : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (hc.zpow _)
  have h2 := (isLocallyConstant_smul (l := l) (O := O) m).comp_continuous h1
  convert h2 using 2 with g
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.twCoef_Wchi, hε', ← map_zpow]
  rfl

theorem exists_eps {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) :
    ∃ χ : S.G → ℤ_[l]ˣ, Continuous χ ∧ ∀ g, (S.Γ.ε g : S.O) = algebraMap ℤ_[l] S.O (χ g) := by
  obtain ⟨χ, hχ, hc, -⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  refine ⟨fun g => χ g, hc.comp continuous_subtype_val, fun g => ?_⟩
  apply Subtype.ext
  have h1 := S.hyp.2.1.2.2.2 g
  have h2 : ((P.PD S.K).χ g : ℚ_[l]) = (P.χQ g : ℚ_[l]) := P.PD_χ S.K g
  rw [h2, ← hχ] at h1
  exact h1

theorem zero_mem {O N : Type} [CommRing O] [AddCommGroup N] [Module O N] {s : Set N}
    (h : ∃ A : Submodule O N, s = A) : 0 ∈ s := by
  obtain ⟨A, rfl⟩ := h
  exact A.zero_mem

theorem cls_eq_zero_of_flat {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) {M : Type} [AddCommGroup M]
    [Module S.O M] [Module.Flat S.O M] (W : Representation S.O S.G M) (hL : S.Lem0 W) (hR : S.ResBound W 0)
    (hlc : ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] (m : M ⊗[S.O] X),
      IsLocallyConstant fun g => twCoef W S.Γ.χ₁ X g m)
    (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] : S.cls W X = {0} := by
  obtain ⟨⟨hD, hV, -⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  have hl : Irreducible S.Γ.lam := S.hyp.1.2.2.2.2.2
  exact @cls_eq_zero S.O S.G _ _ _ hD hV _ hl M _ _ _ W S.Γ.χ₁
    (fun X _ _ => S.cls W X) hlc (fun Y _ _ _ => zero_mem (hL Y).1)
    (fun Y _ _ _ Y' _ _ _ f x => (hL Y).2.2 Y' f x) hR X _ _ _

theorem main : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), ∀ c : ℕ, S.Lem0 (S.Γ.Wchi c) → S.ResBound (S.Γ.Wchi c) 0 → ∀ (X : Type) [AddCommGroup X] [Module S.O X] [Finite X], S.cls (S.Γ.Wchi c) X = {0} := by
  intro l _ P S c hL hR X _ _ _
  exact cls_eq_zero_of_flat S _ hL hR
    (fun Y _ _ _ m => (exists_eps S).elim fun χ h => isLocallyConstant_twCoef S.Γ χ h.1 h.2 c Y m) X

end GlobalTheory.TopSteps.CharAllCoef
end

namespace GlobalTheory.TopSteps.CharVanish
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem cls_eq_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (hC : S.CrysCalc) (hR : S.Real)
    (c : ℕ) (h2 : 2 ≤ c) (ht : c ≤ S.D.t) (X : Type) [AddCommGroup X] [Module S.O X] [Finite X] :
    S.cls (S.Γ.Wchi c) X = {0} := by
  have hcl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hL : S.Lem0 (S.Γ.Wchi c) :=
    (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hcl (GlobalTheory.TopSteps.StdAdm.stdAdm S hC hcl)).2 c (by omega) ht
  exact GlobalTheory.TopSteps.CharAllCoef.main S c hL
    ((GlobalTheory.TopSteps.CharBound.resBound_chars S hR).1 c h2 ht hL) X

theorem stmt_of_real : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → (∀ S : TopSit P, S.Real) → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P := by
  intro l _ P AI hT hR K LL n r emb D Γ hyp c h2 ht X _ _ _
  have : NeZero n := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hyp.1⟩
  let S : TopSit P := ⟨K, LL, n, r, emb, D, Γ, hyp⟩
  exact cls_eq_zero S (GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps AI hT S) (hR S) c h2 ht X

end GlobalTheory.TopSteps.CharVanish
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFourierExpansionConjugateHalfSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFourierExpansionConjugateHalfSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.FinFourier

variable {D : D7}

theorem interp_of_sep {α : Type} [DecidableEq α] (P : Set (α → ℂ)) (h1 : (1 : α → ℂ) ∈ P)
    (hmul : ∀ f ∈ P, ∀ g ∈ P, f * g ∈ P) (hadd : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P)
    (hsmul : ∀ (c : ℂ), ∀ f ∈ P, c • f ∈ P) (K : Set α) (s : Finset α) (rep : α → α)
    (hrep : ∀ x ∈ K, rep x ∈ s)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∃ g ∈ P, g a ≠ g b ∧ ∀ x ∈ K, g x = g (rep x))
    (f : α → ℂ) (hf : ∀ x ∈ K, f x = f (rep x)) : ∃ F ∈ P, ∀ x ∈ K, f x = F x := by
  have h0 : (0 : α → ℂ) ∈ P := by simpa using hsmul 0 1 h1
  have hsum : ∀ (t : Finset α) (u : α → α → ℂ), (∀ a ∈ t, u a ∈ P) → (∑ a ∈ t, u a) ∈ P := by
    intro t u hu
    induction t using Finset.induction_on with
    | empty => simpa using h0
    | insert b t hb ih =>
      rw [Finset.sum_insert hb]
      exact hadd _ (hu _ (Finset.mem_insert_self _ _)) _ (ih fun a ha => hu a (Finset.mem_insert_of_mem ha))
  have hprod : ∀ (t : Finset α) (u : α → α → ℂ), (∀ a ∈ t, u a ∈ P) → (∏ a ∈ t, u a) ∈ P := by
    intro t u hu
    induction t using Finset.induction_on with
    | empty => simpa using h1
    | insert b t hb ih =>
      rw [Finset.prod_insert hb]
      exact hmul _ (hu _ (Finset.mem_insert_self _ _)) _ (ih fun a ha => hu a (Finset.mem_insert_of_mem ha))
  have hsep' : ∀ a b : α, ∃ g : α → ℂ, a ∈ s → b ∈ s → a ≠ b → g ∈ P ∧ g a ≠ g b ∧ ∀ x ∈ K, g x = g (rep x) := by
    intro a b
    by_cases h : a ∈ s ∧ b ∈ s ∧ a ≠ b
    · obtain ⟨g, hg⟩ := hsep a h.1 b h.2.1 h.2.2
      exact ⟨g, fun _ _ _ => hg⟩
    · exact ⟨0, fun ha hb hab => absurd ⟨ha, hb, hab⟩ h⟩
  choose g hg using hsep'
  let δ : α → α → ℂ := fun a => ∏ b ∈ s.erase a, (g a b a - g a b b)⁻¹ • (g a b + (-(g a b b)) • (1 : α → ℂ))
  have hδP : ∀ a ∈ s, δ a ∈ P := fun a ha => hprod _ _ fun b hb => hsmul _ _ (hadd _
    (hg a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm).1 _ (hsmul _ _ h1))
  have hδ : ∀ a ∈ s, ∀ x ∈ K, δ a x = if rep x = a then 1 else 0 := by
    intro a ha x hx
    simp only [δ, Finset.prod_apply, Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    split_ifs with hxa
    · apply Finset.prod_eq_one
      intro b hb
      have hb' := hg a b ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
      rw [hb'.2.2 x hx, hxa]
      have : g a b a - g a b b ≠ 0 := sub_ne_zero.2 hb'.2.1
      rw [mul_one, ← sub_eq_add_neg, inv_mul_cancel₀ this]
    · apply Finset.prod_eq_zero (i := rep x)
      · exact Finset.mem_erase.2 ⟨hxa, hrep x hx⟩
      · have hb' := hg a (rep x) ha (hrep x hx) (Ne.symm hxa)
        rw [hb'.2.2 x hx]
        ring
  refine ⟨∑ a ∈ s, f a • δ a, hsum _ _ fun a ha => hsmul _ _ (hδP a ha), fun x hx => ?_⟩
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a ha => by rw [hδ a ha x hx]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq s (rep x) f, if_pos (hrep x hx), hf x hx]

theorem finite_cover_pow {O K : Type} [CommRing O] [Field K] [Algebra O K] (ϖ : O) (hϖ : algebraMap O K ϖ ≠ 0)
    (N M : ℕ) (hfin : Finite (O ⧸ Ideal.span {ϖ ^ (N + M)})) (m n : Type) [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] :
    ∃ T : Finset (Matrix m n K), ∀ X : Matrix m n K,
      (∀ i j, ∃ o : O, algebraMap O K (ϖ ^ N) * X i j = algebraMap O K o) →
      ∃ t ∈ T, ∀ i j, ∃ o : O, (X - t) i j = algebraMap O K (ϖ ^ M * o) := by
  classical
  set I : Ideal O := Ideal.span {ϖ ^ (N + M)} with hIdef
  have ha : algebraMap O K (ϖ ^ N) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hϖ
  haveI : Finite (m → n → O ⧸ I) := inferInstance
  haveI : Fintype (m → n → O ⧸ I) := Fintype.ofFinite _
  let lift : (m → n → O ⧸ I) → m → n → O :=
    fun q i j => Function.surjInv (Ideal.Quotient.mk_surjective (I := I)) (q i j)
  refine ⟨Finset.univ.image fun q => Matrix.of fun i j => (algebraMap O K (ϖ ^ N))⁻¹ * algebraMap O K (lift q i j), ?_⟩
  intro X hX
  choose z hz using hX
  let q : m → n → O ⧸ I := fun i j => Ideal.Quotient.mk I (z i j)
  refine ⟨_, Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, fun i j => ?_⟩
  have hq : Ideal.Quotient.mk I (lift q i j) = Ideal.Quotient.mk I (z i j) :=
    Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) _
  rw [Ideal.Quotient.eq, hIdef, Ideal.mem_span_singleton'] at hq
  obtain ⟨w, hw⟩ := hq
  refine ⟨-w, ?_⟩
  have hij := hz i j
  simp only [Matrix.sub_apply, Matrix.of_apply]
  have hX : X i j = (algebraMap O K (ϖ ^ N))⁻¹ * algebraMap O K (z i j) := by
    rw [← hij, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have hzl : z i j - lift q i j = ϖ ^ N * (ϖ ^ M * -w) := by
    rw [← neg_sub, ← hw]; ring
  rw [hX, ← mul_sub, ← map_sub, hzl, map_mul (algebraMap O K) (ϖ ^ N), ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

end GlobalTheory.DownLift.GenSplit.FinFourier

namespace GlobalTheory.DownLift.GenSplit


open GlobalTheory.SplitScalar in
theorem finite_fourier_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (ϖ : OI v), Irreducible ϖ → ∀ (M N : ℕ), (∀ x : WO S T, IsHalf (cA D e) x → ¬ InPow ϖ M (adjCo φ S T BS BT x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T BS BT e ϖ M, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1) → ∀ (a : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ), (∀ X Z, InPow ϖ M Z → a (X + Z) = a X) → ∃ c : WO S T →₀ ℂ, (∀ y ∈ c.support, IsHalf e y) ∧ ∀ x, IsHalf (cA D e) x → Bdd ϖ N (adjCo φ S T BS BT x) → a (adjCo φ S T BS BT x) = c.sum fun y z => z * ψ (symplO S T x y) := by
  intro D ψ _ S T ΛS ΛT _ _ v φ e _ BS BT ϖ hϖ M N hyp a ha
  classical

  let P : Set (WO S T → ℂ) := {F | ∃ c : WO S T →₀ ℂ, (∀ y ∈ c.support, IsHalf e y) ∧
    ∀ x, F x = c.sum fun y z => z * ψ (symplO S T x y)}
  have h0 : ∀ x : WO S T, ∀ y : WO S T, (0 : ℂ) * ψ (symplO S T x y) = 0 := fun _ _ => zero_mul _
  have hP1 : (1 : WO S T → ℂ) ∈ P := ⟨Finsupp.single 0 1, fun y hy => by
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]; exact isHalf_zero e, fun x => by
    rw [Finsupp.sum_single_index (h0 x 0), symplO_zero_right, AddChar.map_zero_eq_one, one_mul]; rfl⟩
  have hPadd : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P := by
    rintro f ⟨c, hc, hf⟩ g ⟨d, hd, hg⟩
    refine ⟨c + d, fun y hy => ?_, fun x => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hy) with h | h
      · exact hc y h
      · exact hd y h
    · rw [Pi.add_apply, hf, hg, Finsupp.sum_add_index' (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _)]
  have hPsmul : ∀ (r : ℂ), ∀ f ∈ P, r • f ∈ P := by
    rintro r f ⟨c, hc, hf⟩
    refine ⟨r • c, fun y hy => hc y (Finsupp.support_smul hy), fun x => ?_⟩
    rw [Pi.smul_apply, hf, Finsupp.sum_smul_index' (fun y => h0 x y), smul_eq_mul, Finsupp.mul_sum]
    simp only [smul_eq_mul, mul_assoc]
  have hPmul : ∀ f ∈ P, ∀ g ∈ P, f * g ∈ P := by
    rintro f ⟨c, hc, hf⟩ g ⟨d, hd, hg⟩
    refine ⟨c.sum fun y z => d.sum fun y' z' => Finsupp.single (y + y') (z * z'), fun y hy => ?_, fun x => ?_⟩
    · obtain ⟨y₁, hy₁, hy⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
      obtain ⟨y₂, hy₂, hy⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hy)
      rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy)]
      exact isHalf_add (hc y₁ hy₁) (hd y₂ hy₂)
    · rw [Pi.mul_apply, hf, hg, Finsupp.sum_sum_index (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _),
        Finsupp.sum_mul]
      refine Finsupp.sum_congr fun y _ => ?_
      rw [Finsupp.sum_sum_index (fun y => h0 x y) (fun _ _ _ => add_mul _ _ _), Finsupp.mul_sum]
      refine Finsupp.sum_congr fun y' _ => ?_
      rw [Finsupp.sum_single_index (h0 x _), GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul]
      ring

  let H : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v)) :=
    { carrier := {X | InPow ϖ M X}
      add_mem' := fun {X Y} hX hY i j => by
        obtain ⟨o₁, h₁⟩ := hX i j
        obtain ⟨o₂, h₂⟩ := hY i j
        exact ⟨o₁ + o₂, by rw [Matrix.add_apply, h₁, h₂, ← map_add (f := _), mul_add]⟩
      zero_mem' := fun i j => ⟨0, by simp⟩
      neg_mem' := fun {X} hX i j => by
        obtain ⟨o, h⟩ := hX i j
        exact ⟨-o, by rw [Matrix.neg_apply, h, ← map_neg, mul_neg]⟩ }
  have hadj : ∀ x y : WO S T, adjCo φ S T BS BT (x - y) = adjCo φ S T BS BT x - adjCo φ S T BS BT y := by
    intro x y
    have e1 : (x - y : WO S T).map (cA D) = x.map (cA D) - y.map (cA D) := by ext i j; simp
    have e2 : ∀ {m n : Type} (A B : Matrix m n (AE D)),
        (A - B).map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) = A.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) - B.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) :=
      fun A B => by ext i j; simp
    simp only [adjCo, e1, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, e2]
  let q : WO S T → Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H :=
    fun x => (adjCo φ S T BS BT x : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H)
  have hqeq : ∀ x y, q x = q y ↔ InPow ϖ M (adjCo φ S T BS BT (x - y)) := by
    intro x y
    rw [hadj]
    exact QuotientAddGroup.eq_iff_sub_mem
  let K : Set (WO S T) := {x | IsHalf (cA D e) x ∧ Bdd ϖ N (adjCo φ S T BS BT x)}
  have hϖ0 : algebraMap (OI v) (Fv D.host.F v) ϖ ≠ 0 :=
    (FaithfulSMul.algebraMap_injective (OI v) (Fv D.host.F v)).ne_iff' (map_zero _) |>.2 hϖ.ne_zero
  have hfin : Finite (OI v ⧸ Ideal.span {ϖ ^ (N + M)}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero _ hϖ.ne_zero)
  obtain ⟨T₀, hT₀⟩ := FinFourier.finite_cover_pow ϖ hϖ0 N M hfin (Fin S.rank) (Fin T.rank)
  have hfinK : (q '' K).Finite := by
    refine (T₀.finite_toSet.image (QuotientAddGroup.mk (s := H))).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, h⟩ := hT₀ _ hx.2
    exact ⟨t, ht, (QuotientAddGroup.eq_iff_sub_mem (N := H)).2 (show InPow ϖ M _ from h) |>.symm⟩
  let pick : (Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) ⧸ H) → WO S T :=
    fun c => if h : ∃ x ∈ K, q x = c then h.choose else 0
  have hpick : ∀ x ∈ K, pick (q x) ∈ K ∧ q (pick (q x)) = q x := by
    intro x hx
    have h : ∃ x' ∈ K, q x' = q x := ⟨x, hx, rfl⟩
    simp only [pick, dif_pos h]
    exact h.choose_spec
  have hsep : ∀ a' ∈ hfinK.toFinset.image pick, ∀ b' ∈ hfinK.toFinset.image pick, a' ≠ b' →
      ∃ g ∈ P, g a' ≠ g b' ∧ ∀ x ∈ K, g x = g (pick (q x)) := by
    intro a' ha' b' hb' hab
    obtain ⟨c₁, hc₁, rfl⟩ := Finset.mem_image.1 ha'
    obtain ⟨x₁, hx₁, rfl⟩ := hfinK.mem_toFinset.1 hc₁
    obtain ⟨c₂, hc₂, rfl⟩ := Finset.mem_image.1 hb'
    obtain ⟨x₂, hx₂, rfl⟩ := hfinK.mem_toFinset.1 hc₂
    have A := hpick x₁ hx₁
    have B := hpick x₂ hx₂
    have hne : ¬ InPow ϖ M (adjCo φ S T BS BT (pick (q x₁) - pick (q x₂))) := by
      intro h
      apply hab
      have h' := (hqeq _ _).2 h
      rw [A.2, B.2] at h'
      rw [h']
    obtain ⟨y, hy, hyL, hyne⟩ := hyp _ (isHalf_sub A.1.1 B.1.1) hne
    refine ⟨fun x => ψ (symplO S T x y), ⟨Finsupp.single y 1, fun y' hy' => ?_, fun x => ?_⟩, ?_, ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hy')]; exact hy
    · rw [Finsupp.sum_single_index (h0 x y), one_mul]
    · intro h
      apply hyne
      simp only at h
      rw [symplO_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul, h, ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one]
    · intro x hx
      have hxr : x - pick (q x) ∈ halfPow φ S T BS BT e ϖ M :=
        ⟨isHalf_sub hx.1 (hpick x hx).1.1, (hqeq _ _).1 (hpick x hx).2.symm⟩
      show ψ (symplO S T x y) = ψ (symplO S T (pick (q x)) y)
      conv_lhs => rw [← add_sub_cancel (pick (q x)) x]
      rw [GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul, hyL _ hxr, mul_one]
  have hf : ∀ x ∈ K, a (adjCo φ S T BS BT x) = a (adjCo φ S T BS BT (pick (q x))) := by
    intro x hx
    have hI := (hqeq _ _).1 (hpick x hx).2.symm
    rw [hadj] at hI
    have h := ha (adjCo φ S T BS BT (pick (q x))) _ hI
    rwa [add_sub_cancel] at h
  obtain ⟨F, ⟨c, hc, hF⟩, hFK⟩ := FinFourier.interp_of_sep P hP1 hPmul hPadd hPsmul K
    (hfinK.toFinset.image pick) (fun x => pick (q x))
    (fun x hx => Finset.mem_image.2 ⟨q x, hfinK.mem_toFinset.2 ⟨x, hx, rfl⟩, rfl⟩) hsep
    (fun x => a (adjCo φ S T BS BT x)) hf
  exact ⟨c, hc, fun x hx hB => (hFK x ⟨hx, hB⟩).trans (hF x)⟩

end GlobalTheory.DownLift.GenSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFourierExpansionConjugateHalfSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteFourierExpansion_conjugateHalf_splitPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (ϖ : OI v), Irreducible ϖ → ∀ (M N : ℕ), (∀ x : WO S T, IsHalf (cA D e) x → ¬ InPow ϖ M (adjCo φ S T BS BT x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T BS BT e ϖ M, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1) → ∀ (a : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ), (∀ X Z, InPow ϖ M Z → a (X + Z) = a X) → ∃ c : WO S T →₀ ℂ, (∀ y ∈ c.support, IsHalf e y) ∧ ∀ x, IsHalf (cA D e) x → Bdd ϖ N (adjCo φ S T BS BT x) → a (adjCo φ S T BS BT x) = c.sum fun y z => z * ψ (symplO S T x y) := by
  first | exact @GlobalTheory.DownLift.GenSplit.finite_fourier_half | exact GlobalTheory.DownLift.GenSplit.finite_fourier_half | (intros; apply GlobalTheory.DownLift.GenSplit.finite_fourier_half <;> assumption)
end
end
