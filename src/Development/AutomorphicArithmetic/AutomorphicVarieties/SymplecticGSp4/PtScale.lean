module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.SymplecticGSp4
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LocUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtScale
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pts_wv {K : Type} [CommRing K] (t : Multiplicative (ℤ × ℤ) →* Kˣ) (w : ℤ × ℤ) :
    wv (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))) w = t (Multiplicative.ofAdd w) := by
  obtain ⟨a, b⟩ := w
  have h : Multiplicative.ofAdd ((a, b) : ℤ × ℤ) =
      Multiplicative.ofAdd ((1, 0) : ℤ × ℤ) ^ a * Multiplicative.ofAdd ((0, 1) : ℤ × ℤ) ^ b := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_zpow, toAdd_mul, Prod.ext_iff]
  rw [h, map_mul, map_zpow, map_zpow]
  rfl

private theorem pts_abs {O S K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing S] [Algebra O S] [IsCO O S] [Field K] [IsAlgClosed K] [Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (W : WPres O (ℤ × ℤ) S) (hz : ∀ i, W.z i ∈ maximalIdeal S)
    (A B : Subalgebra O S) (hA : W.A = A) [Module.Finite O B] (hB : W.part 0 ≤ B.toSubmodule) (ξ : A →ₐ[O] K) :
    ∃ (t : Kˣ × Kˣ) (y : S →ₐ[O] K), ∀ w, ∀ x : A, (x : S) ∈ W.part w → y x = (wv t w : K) * ξ x := by
  subst hA
  have hB' : IsNoetherian O B.toSubmodule := by
    have : IsNoetherian O B := isNoetherian_of_isNoetherianRing_of_finite O B
    exact this
  have hP : IsNoetherian O (W.part 0) := isNoetherian_of_le hB
  have hG : (W.gr 0).FG := by
    apply Submodule.fg_of_fg_map_injective W.A.val.toLinearMap Subtype.val_injective
    have hle : Submodule.map W.A.val.toLinearMap (W.gr 0) ≤ W.part 0 := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    first
      | exact isNoetherian_submodule.mp hP _ hle
      | exact isNoetherian_submodule'.mp hP _ hle
  obtain ⟨t, Ξ, hΞ, -⟩ := points_finite O (ℤ × ℤ) S W hz K ξ (hG.map _)
  refine ⟨(t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1))), Ξ, ?_⟩
  intro w x hx
  have hx' : x ∈ W.gr w := hx
  have h1 := act_of_mem W.gr t ξ hx'
  rw [← hΞ] at h1
  rw [pts_wv]
  exact h1

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptScale :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ∃ t r, D.EPt r ∧ ∀ g, r g = tconj t (M.rep ξ g) := by
  intro Ω _ _ _ l _ c D hD M hF ξ
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨hinj, -, -, hcomp, -⟩ := dvrFacts l c.O
  haveI : Algebra.IsAlgebraic ℤ_[l] ℚ_[l] := IsLocalization.isAlgebraic ℚ_[l] (nonZeroDivisors ℤ_[l])
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) := Algebra.IsAlgebraic.trans ℤ_[l] ℚ_[l] (PadicAlgCl l)
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.extendScalars hinj
  obtain ⟨-, -, WS, hWS, hz⟩ := sInternal D hD M
  have hpart : WS.part = M.sPart := funext hWS
  have hA : WS.A = M.SS := by
    simp only [WPres.A, Model.SS, hpart]
  haveI hfin : Module.Finite c.O (Algebra.adjoin c.O (mono M.ru.hom 0)) := hF M.S M.ru M.pt
  have hB : WS.part 0 ≤ (Algebra.adjoin c.O (mono M.ru.hom 0)).toSubmodule := by
    rw [hWS, spanMono D hD M hF 0, Submodule.span_le]
    exact Algebra.subset_adjoin
  obtain ⟨t, y, hy⟩ := pts_abs WS hz M.SS _ hA hB ξ
  refine ⟨t, mapRep (y : M.S →+* PadicAlgCl l) M.ru.hom, ⟨M.S, _, _, _, M.ru, y, M.pt, rfl⟩, ?_⟩
  intro g
  ext i j
  have h := hy (wt i j) (M.ent g i j) (by rw [hWS]; exact M.entry_mem g i j)
  have e : ((M.ent g i j : M.SS) : M.S) = M.ru.hom g i j := rfl
  rw [e] at h
  simpa [tconj, Model.rep, mapRep, Model.rS] using h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtExt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, D.Fin0 → ∀ (K : Type) [CommRing K] [Algebra c.O K] (ξ ξ' : M.SS →ₐ[c.O] K), M.rep ξ = M.rep ξ' → ξ = ξ' := by
  intro Ω _ _ _ l _ c D hD M h0 K _ _ ξ ξ' hrep
  have hent : ∀ g i j, ξ (M.ent g i j) = ξ' (M.ent g i j) := by
    intro g i j
    have := congrArg (fun r => r g i j) hrep
    simpa [Model.rep, mapRep, Model.rS, RingHom.mapMatrix_apply] using this
  let Q : Subalgebra c.O M.S := (AlgHom.equalizer ξ ξ').map M.SS.val
  have hQent : ∀ g i j, M.ru.hom g i j ∈ Q := by
    intro g i j
    exact ⟨M.ent g i j, hent g i j, rfl⟩
  have hQmono : ∀ w, mono M.ru.hom w ⊆ (Q : Set M.S) := by
    intro w y hy
    obtain ⟨L, -, rfl⟩ := hy
    apply Subalgebra.list_prod_mem
    intro z hz
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hz
    exact hQent _ _ _
  have hle : (⨆ j, M.sPart j) ≤ Subalgebra.toSubmodule Q := by
    refine iSup_le fun w => ?_
    rw [spanMono D hD M h0 w, Submodule.span_le]
    exact hQmono w
  apply AlgHom.ext
  intro x
  have hx : (x : M.S) ∈ ⨆ j, M.sPart j := x.2
  obtain ⟨y, hy, hyx⟩ := hle hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ValProd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem val_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {m n : ℕ} (h : m ∣ n)
    (hA : A.valuation (m : Ω) < 1) : A.valuation (n : Ω) < 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  have hk : A.valuation (k : Ω) ≤ 1 := by
    simpa using A.valuation_le_one (k : A)
  calc A.valuation (m : Ω) * A.valuation (k : Ω) ≤ A.valuation (m : Ω) * 1 := mul_le_mul' le_rfl hk
    _ < 1 := by rwa [mul_one]

private theorem val_prod {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (S : Finset ℕ)
    (hA : A.valuation ((∏ p ∈ S, p : ℕ) : Ω) < 1) : ∃ p ∈ S, A.valuation (p : Ω) < 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hA
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Nat.cast_mul, map_mul] at hA
    by_cases hp : A.valuation (a : Ω) < 1
    · exact ⟨a, Finset.mem_insert_self a S, hp⟩
    · have h1 : A.valuation (a : Ω) = 1 :=
        le_antisymm (by simpa using A.valuation_le_one (a : A)) (not_lt.mp hp)
      rw [h1, one_mul] at hA
      obtain ⟨p, hpS, hp'⟩ := ih hA
      exact ⟨p, Finset.mem_insert_of_mem hpS, hp'⟩

private theorem vlen_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l)
    (N : ℕ) [NeZero N] (e : ℕ) (he : e ≠ 0) (ψ : DirichletCharacter c.O N) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Vlen Ω c e ψ ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ) := by
  classical
  haveI := c.dvr
  haveI := c.fin
  have hcls := Chr.clsFacts ℚ Ω N
  have hker : (Chr.cls ℚ Ω N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    simp [Chr.dirG, hg]
  have hopen : IsOpen ((Chr.dirG ℚ Ω ψ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hker hcls.1
  have hpow : Chr.dirG ℚ Ω ψ ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, Chr.dirG, MonoidHom.comp_apply, ← map_pow,
      pow_card_eq_one, map_one]
  have hint : ∀ (A : ValuationSubring Ω) (x : Ω) (z : ℤ), A.valuation x < 1 →
      A.valuation (x * (z : Ω)) < 1 := by
    intro A x z hx
    rw [map_mul]
    have hz : A.valuation (z : Ω) ≤ 1 := by simpa using A.valuation_le_one (z : A)
    calc A.valuation x * A.valuation (z : Ω) ≤ A.valuation x * 1 := mul_le_mul' le_rfl hz
      _ < 1 := by rwa [mul_one]
  show Chr.VS l (l * N) e (Chr.dirG ℚ Ω ψ) ≤ Chr.VS l (∏ p ∈ S, p) e (Chr.dirG ℚ Ω ψ)
  unfold Chr.VS
  set_option synthInstance.maxHeartbeats 200000 in
   refine Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)
  intro x hx
  simp only [Base.ShaU, Base.mem_locSel] at hx ⊢
  intro D hD
  rcases hD with ⟨A, hAS, rfl⟩ | ⟨A, rfl⟩
  · obtain ⟨p, hpS, hp⟩ := val_prod A S hAS
    by_cases hdvd : p ∣ l * N
    · exact hx (Dec A) (Or.inl ⟨A, val_dvd A hdvd hp, rfl⟩)
    · have pp := hS p hpS
      have hpl : p ≠ l := by
        rintro rfl
        exact hdvd (dvd_mul_right p N)
      have hpN : ¬ p ∣ N := fun h' => hdvd (dvd_mul_of_dvd_right h' l)
      have hN : ¬ A.valuation (N : Ω) < 1 := by
        intro hN
        have hcop : Nat.gcd p N = 1 := ((Nat.Prime.coprime_iff_not_dvd pp).2 hpN)
        have hb := Nat.gcd_eq_gcd_ab p N
        rw [hcop] at hb
        have h1 : (1 : Ω) = (p : Ω) * (Nat.gcdA p N : Ω) + (N : Ω) * (Nat.gcdB p N : Ω) := by
          have := congrArg (fun z : ℤ => (z : Ω)) hb
          push_cast at this
          exact this
        have hsum := Valuation.map_add_lt A.valuation (hint A _ (Nat.gcdA p N) hp)
          (hint A _ (Nat.gcdB p N) hN)
        rw [← h1, map_one] at hsum
        exact lt_irrefl _ hsum
      have hIne : Ine A ≤ (Chr.dirG ℚ Ω ψ).ker := le_trans (hcls.2.2.2.2 A hN) hker
      have hU : (⊤ : Subgroup (G ℚ Ω)) ⊓ Ine A ≤ ⊤ ⊓ Dec A := inf_le_inf_left _ (Ine_le_Dec A)
      have hinj := (Chr.locUnr Ω l c.O e (Fintype.card (ZMod N)ˣ) (Chr.dirG ℚ Ω ψ) he
        Fintype.card_ne_zero hopen hpow p A pp hpl hp (⊤ ⊓ Ine A) (⊤ ⊓ Dec A) hU
        (top_inf_eq _) (top_inf_eq _)).2 (inf_le_right.trans hIne)
      have h0 := hx (Ine A) (Or.inr ⟨A, rfl⟩)
      have h2 : Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) hU
          (Base.resU (Chr.rho l e (Chr.dirG ℚ Ω ψ)) (inf_le_left : ⊤ ⊓ Dec A ≤ ⊤) x) = 0 := by
        rw [Base.resU_resU]
        exact h0
      exact hinj (h2.trans (map_zero _).symm)
  · exact hx (Ine A) (Or.inr ⟨A, rfl⟩)

theorem UpperTheory.V.GradeZeroInterpolatingElement.shaEq :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → Aut.OfCase D h e ψ → Vlen Ω c e ψ ≤ D.sha := by
  intro Ω _ _ _ h t _ l _ c e _ he _ ψ _ D hD hA
  have key : ∀ {n' p₁ m₀ : ℕ}, Aut.OfChar D e ψ n' p₁ m₀ → Vlen Ω c e ψ ≤ D.sha := by
    intro n' p₁ m₀ hc
    unfold Raw.sha
    rw [hc.e_eq, hc.psi]
    exact vlen_le Ω l c h.N e he.ne' ψ D.S hD.S_prime
  rcases hA with ⟨_, hc⟩ | ⟨_, hc⟩
  · exact key hc
  · exact key hc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem list_neg {α : Type} (d : α → ℤ × ℤ) (L : List α) (h : ((L.map d).sum).2 < 0) :
    ∃ a ∈ L, (d a).2 < 0 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Prod.snd_add] at h
    by_cases hb : (d b).2 < 0
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨a, ha, h'⟩ := ih (by omega)
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem list_pos {α : Type} (d : α → ℤ × ℤ) (L : List α) (h : 0 < ((L.map d).sum).2) :
    ∃ a ∈ L, 0 < (d a).2 := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, Prod.snd_add] at h
    by_cases hb : 0 < (d b).2
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨a, ha, h'⟩ := ih (by omega)
      exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

private theorem span_zero {O S K : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    (B : Subalgebra O S) (ξ : B →ₐ[O] K) (T : Set S) (hT : ∀ y ∈ T, ∃ h : y ∈ B, ξ ⟨y, h⟩ = 0)
    (x : B) (hx : x.1 ∈ Submodule.span O T) : ξ x = 0 := by
  obtain ⟨x, hxB⟩ := x
  have hx' : x ∈ Submodule.span O T := hx
  clear hx
  suffices H : ∃ h : x ∈ B, ξ ⟨x, h⟩ = 0 by
    obtain ⟨_, h⟩ := H
    exact h
  clear hxB
  induction hx' using Submodule.span_induction with
  | mem y hy => exact hT y hy
  | zero => exact ⟨B.zero_mem, map_zero ξ⟩
  | add y z _ _ hy hz =>
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨B.add_mem hy1 hz1, ?_⟩
    have e : (⟨y + z, B.add_mem hy1 hz1⟩ : B) = ⟨y, hy1⟩ + ⟨z, hz1⟩ := rfl
    rw [e, map_add (f := _), hy2, hz2, add_zero]
  | smul a y _ hy =>
    obtain ⟨hy1, hy2⟩ := hy
    refine ⟨B.smul_mem hy1 a, ?_⟩
    have e : (⟨a • y, B.smul_mem hy1 a⟩ : B) = a • ⟨y, hy1⟩ := rfl
    rw [e, map_smul, hy2, smul_zero]

private theorem prod_zero {O S K α : Type} [CommRing O] [CommRing S] [Algebra O S] [CommRing K] [Algebra O K]
    (B : Subalgebra O S) (ξ : B →ₐ[O] K) (e : α → B) (L : List α) (a : α) (ha : a ∈ L) (h0 : ξ (e a) = 0) :
    ∃ h : (L.map fun a => (e a).1).prod ∈ B, ξ ⟨_, h⟩ = 0 := by
  have hp : (((L.map e).prod : B) : S) = (L.map fun a => (e a).1).prod := by
    simpa [List.map_map, Function.comp_def] using map_list_prod B.val (L.map e)
  have hm : (L.map fun a => (e a).1).prod ∈ B := by
    rw [← hp]
    exact ((L.map e).prod).2
  refine ⟨hm, ?_⟩
  have e1 : (⟨_, hm⟩ : B) = (L.map e).prod := Subtype.ext hp.symm
  rw [e1, map_list_prod, List.map_map]
  apply List.prod_eq_zero
  simp only [List.mem_map, Function.comp_apply]
  exact ⟨a, ha, h0⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.signs :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ((∀ i j, (wt i j).2 < 0 → ¬ Ge (M.rep ξ) i j) → NegZero M.gr (ξ.comp M.toSS)) ∧ ((∀ i j, 0 < (wt i j).2 → ¬ Ge (M.rep ξ) i j) → PosZero M.gr (ξ.comp M.toSS)) ∧ (PosZero M.gr (ξ.comp M.toSS) → ¬ Ge (M.rep ξ) 0 2) ∧ (NegZero M.gr (ξ.comp M.toSS) → ¬ Ge (M.rep ξ) 2 0) ∧ ∀ ξ' : M.SS →ₐ[c.O] PadicAlgCl l, Same0 M.gr (ξ.comp M.toSS) (ξ'.comp M.toSS) → (∀ g i, M.rep ξ g i i = M.rep ξ' g i i) ∧ (DiagType (M.rep ξ) → DiagType (M.rep ξ')) := by
  intro Ω _ _ _ l _ c D hD M _ h0 ξ
  have hv : ∀ (ζ : M.SS →ₐ[c.O] PadicAlgCl l) g i j, M.rep ζ g i j = ζ (M.ent g i j) := fun _ _ _ _ => rfl
  have hwt : ∀ i j : Fin 4, (wt i j).1 = 0 → True := fun _ _ _ => trivial
  have zero_of : ∀ n : ℤ, ∀ f ∈ M.gr n,
      (∀ L : List (G ℚ Ω × Fin 4 × Fin 4), (L.map fun a => wt a.2.1 a.2.2).sum = ((0 : ℤ), n) →
        ∃ a ∈ L, ξ (M.ent a.1 a.2.1 a.2.2) = 0) → ξ (M.toSS f) = 0 := by
    intro n f hf hL
    have hx := (kerA D hD M).2.2 n f hf
    rw [spanMono D hD M h0] at hx
    apply span_zero M.SS ξ (mono M.ru.hom ((0 : ℤ), n)) _ (M.toSS f) hx
    rintro y ⟨L, hsum, rfl⟩
    obtain ⟨a, ha, hz⟩ := hL L hsum
    exact prod_zero M.SS ξ (fun a => M.ent a.1 a.2.1 a.2.2) L a ha hz
  have from_part : ∀ n : ℤ, ∀ g i j, wt i j = ((0 : ℤ), n) → ∃ f ∈ M.gr n, M.toSS f = M.ent g i j := by
    intro n g i j he
    apply (kerA D hD M).2.1 n (M.ent g i j)
    have := M.entry_mem g i j
    rw [he] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hneg n hn f hf
    change ξ (M.toSS f) = 0
    apply zero_of n f hf
    intro L hsum
    obtain ⟨a, ha, hlt⟩ := list_neg (fun a => wt a.2.1 a.2.2) L (by rw [hsum]; exact hn)
    refine ⟨a, ha, ?_⟩
    by_contra hne
    exact hneg _ _ hlt ⟨a.1, hne⟩
  · intro hpos n hn f hf
    change ξ (M.toSS f) = 0
    apply zero_of n f hf
    intro L hsum
    obtain ⟨a, ha, hlt⟩ := list_pos (fun a => wt a.2.1 a.2.2) L (by rw [hsum]; exact hn)
    refine ⟨a, ha, ?_⟩
    by_contra hne
    exact hpos _ _ hlt ⟨a.1, hne⟩
  · rintro hpos ⟨g, hg⟩
    obtain ⟨f, hf, hfx⟩ := from_part 1 g 0 2 (by decide)
    apply hg
    have := hpos 1 one_pos f hf
    change ξ (M.toSS f) = 0 at this
    rw [hfx] at this
    exact this
  · rintro hneg ⟨g, hg⟩
    obtain ⟨f, hf, hfx⟩ := from_part (-1) g 2 0 (by decide)
    apply hg
    have := hneg (-1) (by norm_num) f hf
    change ξ (M.toSS f) = 0 at this
    rw [hfx] at this
    exact this
  · intro ξ' hs
    have key : ∀ x : M.SS, (x : M.S) ∈ M.sPart ((0 : ℤ), 0) → ξ x = ξ' x := by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := (kerA D hD M).2.1 0 x hx
      exact hs f hf
    constructor
    · intro g i
      rw [hv, hv]
      apply key
      have := M.entry_mem g i i
      rwa [show wt i i = ((0 : ℤ), 0) by simp [wt]] at this
    · intro hd i j hij ⟨g, hg⟩ ⟨h, hh⟩
      rw [hv] at hg hh
      have hp : ((M.ent g i j * M.ent h j i : M.SS) : M.S) ∈ M.sPart ((0 : ℤ), 0) := by
        rw [spanMono D hD M h0]
        apply Submodule.subset_span
        refine ⟨[(g, i, j), (h, j, i)], ?_, ?_⟩
        · refine Prod.ext ?_ ?_ <;> simp [wt] <;> ring
        · simp [Model.ent]
      have he := key _ hp
      rw [map_mul, map_mul] at he
      apply mul_ne_zero hg hh
      rw [← he]
      by_cases a : ξ (M.ent g i j) = 0
      · rw [a, zero_mul]
      · have hnot := hd i j hij ⟨g, by rw [hv]; exact a⟩
        have hz : ξ (M.ent h j i) = 0 := by
          by_contra hz
          exact hnot ⟨h, by rw [hv]; exact hz⟩
        rw [hz, mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoPowClogLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem two_pow_clog_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.clog 2 m ≤ 2 * m := by
  rcases Nat.lt_or_ge 1 m with h1 | h1
  · have hk : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) h1
    have hlt := Nat.pow_pred_clog_lt_self 2 h1
    obtain ⟨k, hk'⟩ : ∃ k, Nat.clog 2 m = k + 1 := ⟨Nat.clog 2 m - 1, by omega⟩
    rw [hk'] at hlt ⊢
    simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel] at hlt
    rw [pow_succ]
    linarith
  · have : m = 1 := by omega
    subst this
    simp

private theorem nII_le (X l N o q c n f : ℕ) (hX : 16 ≤ X) (hl : l ≤ X) (hN : N ≤ X) (ho : o ≤ X) (hq : q ≤ X)
    (hc : 2 ^ c ≤ X) (hn : 2 ^ n ≤ l ^ f) (hl0 : 0 < l) (hN0 : 0 < N) :
    2 ^ Nat.clog 2 (max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2)) ≤ X ^ (2 * f + 10) := by
  have hX1 : 1 ≤ X := by omega
  have hX2 : 2 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have mlp : ∀ {a b i j : ℕ}, a ≤ X ^ i → b ≤ X ^ j → a * b ≤ X ^ (i + j) := by
    intro a b i j ha hb
    rw [pow_add]
    exact Nat.mul_le_mul ha hb
  have h4 : 4 ^ n ≤ X ^ (f * 2) := by
    have e4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e4, pow_mul]
    exact Nat.pow_le_pow_left (hn.trans (Nat.pow_le_pow_left hl f)) 2
  have hA1 : l * N * 4 ^ n ≤ X ^ (1 + 1 + f * 2) :=
    mlp (mlp (hl.trans (pow_one X).ge) (hN.trans (pow_one X).ge)) h4
  have hB : 2 ^ c * o * l ^ 3 * q ^ 2 ≤ X ^ (1 + 1 + 3 + 2) :=
    mlp (mlp (mlp (hc.trans (pow_one X).ge) (ho.trans (pow_one X).ge))
      (Nat.pow_le_pow_left hl 3)) (Nat.pow_le_pow_left hq 2)
  have hA2 : 2 ^ (c + 6) * o * l ^ 3 * q ^ 2 ≤ 64 * X ^ (1 + 1 + 3 + 2) := by
    calc 2 ^ (c + 6) * o * l ^ 3 * q ^ 2 = 64 * (2 ^ c * o * l ^ 3 * q ^ 2) := by ring
      _ ≤ 64 * X ^ (1 + 1 + 3 + 2) := Nat.mul_le_mul_left 64 hB
  have hpos : 1 ≤ l * N * 4 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hmax1 : 1 ≤ max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) := hpos.trans (le_max_left _ _)
  have k1 : 2 * (l * N * 4 ^ n) ≤ X ^ (2 * f + 10) :=
    calc 2 * (l * N * 4 ^ n) ≤ X * X ^ (1 + 1 + f * 2) := Nat.mul_le_mul hX2 hA1
      _ = X ^ (1 + (1 + 1 + f * 2)) := by ring
      _ ≤ X ^ (2 * f + 10) := hmono (by omega)
  have h128 : 128 ≤ X ^ 2 := by nlinarith
  have k2 : 2 * (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) ≤ X ^ (2 * f + 10) :=
    calc 2 * (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) ≤ 2 * (64 * X ^ (1 + 1 + 3 + 2)) := Nat.mul_le_mul_left 2 hA2
      _ = 128 * X ^ (1 + 1 + 3 + 2) := by ring
      _ ≤ X ^ 2 * X ^ (1 + 1 + 3 + 2) := Nat.mul_le_mul_right _ h128
      _ = X ^ (2 + (1 + 1 + 3 + 2)) := by ring
      _ ≤ X ^ (2 * f + 10) := hmono (by omega)
  calc 2 ^ Nat.clog 2 (max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2))
      ≤ 2 * max (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) := two_pow_clog_le _ hmax1
    _ ≤ X ^ (2 * f + 10) := by
      rcases max_choice (l * N * 4 ^ n) (2 ^ (c + 6) * o * l ^ 3 * q ^ 2) with h | h <;> rw [h] <;> assumption

private theorem le_pow_self' {X : ℕ} (hX : 2 ≤ X) (k : ℕ) : k ≤ X ^ k := by
  calc k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    _ ≤ X ^ k := Nat.pow_le_pow_left hX k

private theorem mul_le_pow' {X a b i j : ℕ} (ha : a ≤ X ^ i) (hb : b ≤ X ^ j) : a * b ≤ X ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

private theorem two_pow_nIII_le {X l q P n f : ℕ} (hX : 2 ≤ X) (hl : l ≤ X) (hl0 : 0 < l) (hn : 2 ^ n < l ^ f) :
    2 ^ Nat.clog 2 (max (l * q * P * 4 ^ n) (8 * l ^ 2)) ≤ X ^ (1 + (10 + q + P + 2 * f)) := by
  have hX1 : 1 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have h4 : 4 ^ n ≤ X ^ (f * 2) := by
    have e4 : (4 : ℕ) ^ n = (2 ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [e4, pow_mul]
    exact Nat.pow_le_pow_left (hn.le.trans (Nat.pow_le_pow_left hl f)) 2
  have hA1 : l * q * P * 4 ^ n ≤ X ^ (1 + q + P + f * 2) :=
    mul_le_pow' (mul_le_pow' (mul_le_pow' (hl.trans (pow_one X).ge) (le_pow_self' hX q))
      (le_pow_self' hX P)) h4
  have h8 : 8 ≤ X ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ X ^ 3 := Nat.pow_le_pow_left hX 3
  have hA2 : 8 * l ^ 2 ≤ X ^ (3 + 2) := mul_le_pow' h8 (Nat.pow_le_pow_left hl 2)
  have hmax1 : 1 ≤ max (l * q * P * 4 ^ n) (8 * l ^ 2) :=
    (Nat.one_le_iff_ne_zero.mpr (by positivity)).trans (le_max_right _ _)
  have k1 : 2 * (l * q * P * 4 ^ n) ≤ X ^ (1 + (10 + q + P + 2 * f)) :=
    calc 2 * (l * q * P * 4 ^ n) ≤ X * X ^ (1 + q + P + f * 2) := Nat.mul_le_mul hX hA1
      _ = X ^ (1 + (1 + q + P + f * 2)) := by ring
      _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := hmono (by omega)
  have k2 : 2 * (8 * l ^ 2) ≤ X ^ (1 + (10 + q + P + 2 * f)) :=
    calc 2 * (8 * l ^ 2) ≤ X * X ^ (3 + 2) := Nat.mul_le_mul hX hA2
      _ = X ^ (1 + (3 + 2)) := by ring
      _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := hmono (by omega)
  calc 2 ^ Nat.clog 2 (max (l * q * P * 4 ^ n) (8 * l ^ 2))
      ≤ 2 * max (l * q * P * 4 ^ n) (8 * l ^ 2) := two_pow_clog_le _ hmax1
    _ ≤ X ^ (1 + (10 + q + P + 2 * f)) := by
      rcases max_choice (l * q * P * 4 ^ n) (8 * l ^ 2) with h | h <;> rw [h] <;> assumption

private theorem pZero_le' (m : ℕ) : pZero m ≤ 2 * m + 10 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [pZero]
  · exact (pZeroLe m hm).2.2.2

private theorem final_le (C A a B o l n N P e : ℕ) (hl : 2 ≤ l) (hN : 0 < N) (he : 0 < e) (hP : P ≤ B)
    (hn : 2 ^ n ≤ (l * N * e) ^ a) :
    (2 * C * ((l - 1) * 2 ^ n * (2 * o) : ℕ) * (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) ^ A *
      Real.log (pZero (l * N * P)) : ℝ) ≤
      ((l : ℝ) * N * e) ^ (2 * C + (1 + a + 2 * o) + (1 + a + 1 + B + 2) * A + (2 + (1 + 1 + B) + 10 + 1)) := by
  obtain ⟨X, hXdef⟩ : ∃ X, X = l * N * e := ⟨_, rfl⟩
  rw [← hXdef] at hn
  have hNe : 1 ≤ N * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hle : 1 ≤ l * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlN : 1 ≤ l * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlX : l ≤ X := by
    calc l = l * 1 := (mul_one _).symm
      _ ≤ l * (N * e) := Nat.mul_le_mul_left _ hNe
      _ = X := by rw [hXdef]; ring
  have hNX : N ≤ X := by
    calc N = N * 1 := (mul_one _).symm
      _ ≤ N * (l * e) := Nat.mul_le_mul_left _ hle
      _ = X := by rw [hXdef]; ring
  have heX : e ≤ X := by
    calc e = 1 * e := (one_mul _).symm
      _ ≤ (l * N) * e := Nat.mul_le_mul_right _ hlN
      _ = X := by rw [hXdef]
  have hX2 : 2 ≤ X := hl.trans hlX
  have hX1 : 1 ≤ X := by omega
  have hmono : ∀ {i j : ℕ}, i ≤ j → X ^ i ≤ X ^ j := fun h => Nat.pow_le_pow_right hX1 h
  have hPB : P ≤ X ^ B := hP.trans (le_pow_self' hX2 B)
  have b1 : 2 * C ≤ X ^ (2 * C) := le_pow_self' hX2 _
  have b2 : (l - 1) * 2 ^ n * (2 * o) ≤ X ^ (1 + a + 2 * o) :=
    mul_le_pow' (mul_le_pow' (((Nat.sub_le l 1).trans hlX).trans (pow_one X).ge) hn) (le_pow_self' hX2 _)
  have he1 : e + 1 ≤ X ^ 2 := by nlinarith
  have b3 : l * 2 ^ n * N * P * (e + 1) ≤ X ^ (1 + a + 1 + B + 2) :=
    mul_le_pow' (mul_le_pow' (mul_le_pow' (mul_le_pow' (hlX.trans (pow_one X).ge) hn)
      (hNX.trans (pow_one X).ge)) hPB) he1
  have hy : l * N * P ≤ X ^ (1 + 1 + B) :=
    mul_le_pow' (mul_le_pow' (hlX.trans (pow_one X).ge) (hNX.trans (pow_one X).ge)) hPB
  have hy1 : 1 ≤ X ^ (1 + 1 + B) := Nat.one_le_pow _ _ (by omega)
  have h16 : 16 ≤ X ^ 4 := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ X ^ 4 := Nat.pow_le_pow_left hX2 4
  have b4 : pZero (l * N * P) ≤ X ^ (2 + (1 + 1 + B) + 10 + 1) := by
    calc pZero (l * N * P) ≤ 2 * (l * N * P) + 10 := pZero_le' _
      _ ≤ 2 * X ^ (1 + 1 + B) + 10 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 hy) 10
      _ ≤ X ^ 4 * X ^ (1 + 1 + B) := by nlinarith
      _ = X ^ (4 + (1 + 1 + B)) := by ring
      _ ≤ X ^ (2 + (1 + 1 + B) + 10 + 1) := hmono (by omega)
  have hXr : ((l : ℝ) * N * e) = (X : ℝ) := by rw [hXdef]; push_cast; ring
  rw [hXr]
  have c1 : 2 * (C : ℝ) ≤ (X : ℝ) ^ (2 * C) := by exact_mod_cast b1
  have c2 : (((l - 1) * 2 ^ n * (2 * o) : ℕ) : ℝ) ≤ (X : ℝ) ^ (1 + a + 2 * o) := by exact_mod_cast b2
  have c3 : (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) ≤ (X : ℝ) ^ (1 + a + 1 + B + 2) := by
    have : (((l * 2 ^ n * N * P * (e + 1) : ℕ) : ℝ)) ≤ (X : ℝ) ^ (1 + a + 1 + B + 2) := by exact_mod_cast b3
    simpa using this
  have hlog0 : 0 ≤ Real.log (pZero (l * N * P)) := Real.log_natCast_nonneg _
  have c4 : Real.log (pZero (l * N * P)) ≤ (X : ℝ) ^ (2 + (1 + 1 + B) + 10 + 1) := by
    have hb4 : ((pZero (l * N * P) : ℕ) : ℝ) ≤ (X : ℝ) ^ (2 + (1 + 1 + B) + 10 + 1) := by exact_mod_cast b4
    exact (Real.log_le_self (Nat.cast_nonneg _)).trans hb4
  have hY0 : 0 ≤ (((l * 2 ^ n * N * P : ℕ) : ℝ) * (e + 1)) := by positivity
  have s1 := mul_le_mul c1 c2 (by positivity) (by positivity)
  have s2 := mul_le_mul s1 (pow_le_pow_left₀ hY0 c3 A) (by positivity) (by positivity)
  have s3 := mul_le_mul s2 c4 hlog0 (by positivity)
  refine s3.trans (le_of_eq ?_)
  rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]

theorem UpperTheory.V.GradeZeroInterpolatingElement.arith :
    ∀ (χ : Formalism.HC.PChar) (C A : ℕ), ∃ C' : ℕ, ∀ h : Host, h.chi = χ → ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 2 ≤ e → ∀ ψ ∈ h.X c e, ∀ n' p₁ : ℕ, (n' = h.nII l ψ ∧ p₁ = 1) ∨ (n' = h.nIII l ψ ∧ p₁ = UpperTheory.V.pOne χ) → (2 * C * ((l - 1) * 2 ^ n' * (2 * h.o) : ℕ) * (((l * 2 ^ n' * h.N * p₁ : ℕ) : ℝ) * (e + 1)) ^ A * Real.log (pZero (l * h.N * p₁)) : ℝ) ≤ ((l : ℝ) * h.N * e) ^ C' := by
  intro χ C A
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = (2 * (4 * ordC χ).totient + 10) +
      (1 + (10 + χ.N + pOne χ + 2 * (4 * ordC χ).totient)) := ⟨_, rfl⟩
  refine ⟨2 * C + (1 + a + 2 * ordC χ) + (1 + a + 1 + (1 + pOne χ) + 2) * A +
    (2 + (1 + 1 + (1 + pOne χ)) + 10 + 1), ?_⟩
  intro h hχ
  subst hχ
  intro l _ c e hl2 he ψ hψ n' p₁ hcase
  have pl : l.Prime := Fact.out
  have hl : 2 ≤ l := pl.two_le
  have hN0 := h.N_pos
  have hchar := ((Host.mem_X h).1 hψ).1
  obtain ⟨-, -, hn0, -, -⟩ := cmDatum_char_two_adic_order_bounds h c.O ψ hchar l pl hl2
  have hidx := hostIndex h
  have hNe : 1 ≤ h.N * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hle : 1 ≤ l * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hlX : l ≤ l * h.N * e := by
    calc l = l * 1 := (mul_one _).symm
      _ ≤ l * (h.N * e) := Nat.mul_le_mul_left _ hNe
      _ = l * h.N * e := by ring
  have hNX : h.N ≤ l * h.N * e := by
    calc h.N = h.N * 1 := (mul_one _).symm
      _ ≤ h.N * (l * e) := Nat.mul_le_mul_left _ hle
      _ = l * h.N * e := by ring
  have h16 : 16 ≤ h.N := Nat.le_of_dvd hN0 hidx.2.2.1
  have hX16 : 16 ≤ l * h.N * e := h16.trans hNX
  have hX1 : 1 ≤ l * h.N * e := by omega
  have hX2 : 2 ≤ l * h.N * e := by omega
  have hqN : h.q ≤ h.N := Nat.le_of_dvd hN0 h.q_dvd
  have hoq : h.o ≤ h.q := hidx.2.2.2.2.1
  have hcN : 2 ^ c2 ψ ≤ h.N := Nat.le_of_dvd hN0 (compCond c.O h.N ψ 2 Nat.prime_two).2.2.2.2.1
  have hP : p₁ ≤ 1 + pOne h.chi := by
    rcases hcase with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega
  have hn : 2 ^ n' ≤ (l * h.N * e) ^ a := by
    rw [ha]
    rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · have key := nII_le (l * h.N * e) l h.N h.o h.q (c2 ψ) (n0 l ψ) (4 * h.o).totient hX16 hlX hNX
        ((hoq.trans hqN).trans hNX) (hqN.trans hNX) (hcN.trans hNX) hn0.le (by omega) hN0
      unfold Host.nII
      exact key.trans (Nat.pow_le_pow_right hX1 (Nat.le_add_right _ _))
    · have key := two_pow_nIII_le (X := l * h.N * e) (q := h.q) (P := pOne h.chi)
        (f := (4 * h.o).totient) hX2 hlX (by omega) hn0
      unfold Host.nIII
      exact key.trans (Nat.pow_le_pow_right hX1 (Nat.le_add_left _ _))
  exact final_le C A a (1 + pOne h.chi) h.o l n' h.N p₁ e hl hN0 (by omega) hP hn
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.NonemptyCoverOfRelativePresentationSmoothPt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem rp_coeff {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem rp_ext {O σ Q : Type} [CommRing O] [Fintype σ] [AddCommGroup Q] [Module O Q]
    (D E : MvPowerSeries σ O →ₗ[O] Q)
    (hD : ∀ f g, D (f * g) = MvPowerSeries.constantCoeff f • D g + MvPowerSeries.constantCoeff g • D f)
    (hE : ∀ f g, E (f * g) = MvPowerSeries.constantCoeff f • E g + MvPowerSeries.constantCoeff g • E f)
    (hX : ∀ s, D (MvPowerSeries.X s) = E (MvPowerSeries.X s)) (f : MvPowerSeries σ O) : D f = E f := by
  let W' := WPres.free O (fun _ : σ => (0 : ℤ))
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  have h0 := (der_extend O _ ℤ W' h' Q).2 (D - E) (fun f g => by
    rw [ho, ho]
    simp only [LinearMap.sub_apply]
    rw [hD, hE, smul_sub, smul_sub]
    abel) (fun (s : σ) => by
    show D (MvPowerSeries.X s) - E (MvPowerSeries.X s) = 0
    rw [hX, sub_self])
  rw [sub_eq_zero.1 h0]

private theorem rp_ex {O σ : Type} [CommRing O] [Fintype σ] (d : σ → O) :
    ∃ L : MvPowerSeries σ O →ₗ[O] O,
      (∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f) ∧
      (∀ s, L (MvPowerSeries.X s) = d s) ∧
      ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := by
  classical
  let L : MvPowerSeries σ O →ₗ[O] O :=
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries σ O →ₗ[O] O).smulRight (d s)
  have hL : ∀ f, L f = ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • d s := fun f => by
    simp [L]
  refine ⟨L, fun f g => ?_, fun s => ?_, hL⟩
  · rw [hL, hL, hL]
    simp only [rp_coeff, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  · rw [hL]
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

private theorem rp_lift {O X B R S Q : Type} [CommRing O] [AddCommGroup X] [CommRing B] [Algebra O B] [CommRing R]
    [Algebra O R] [CommRing S] [Algebra O S] [AddCommGroup Q] [Module O Q]
    (WB : WPres O X B) (hB : WB.HasOrigin) (W : WPres O X R) (h : W.HasOrigin) {τ : Type} (e : WB.σ ⊕ τ ≃ W.σ)
    (hwt : ∀ s, W.wt (e (.inl s)) = WB.wt s)
    (hker : RingHom.ker W.π = (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)))
    (qh : R →ₐ[O] S) (x₀ : S →ₐ[O] O) (hx : x₀.comp qh = W.origin h) (p : O →ₗ[O] Q) (hp : Function.Surjective p)
    (j : X) (D : S →ₗ[O] Q) (hD : D ∈ PtDer x₀ Q) (hDw : ∀ s, W.wt s ≠ j → D (qh (W.z s)) = 0)
    (D₁ : B →ₗ[O] O) (hD₁ : D₁ ∈ PtDer (WB.origin hB) O) (hD₁w : ∀ s, WB.wt s ≠ j → D₁ (WB.z s) = 0)
    (hpD : ∀ s, p (D₁ (WB.z s)) = D (qh (W.z (e (.inl s))))) :
    ∃ D' ∈ PtDer (W.origin h) O, HasWt W.part j D' ∧ ∀ f, p (D' f) = D (qh f) := by
  classical
  have hd : ∀ s : W.σ, ∃ d : O, (∀ t, s = e (.inl t) → d = D₁ (WB.z t)) ∧ (W.wt s ≠ j → d = 0) ∧
      p d = D (qh (W.z s)) := fun s => by
    obtain ⟨u, rfl⟩ := e.surjective s
    rcases u with t | t
    · refine ⟨D₁ (WB.z t), fun t' ht => ?_, fun hj => hD₁w t (by rwa [← hwt]), hpD t⟩
      rw [Sum.inl.inj (e.injective ht)]
    · by_cases hj : W.wt (e (.inr t)) = j
      · obtain ⟨a, ha⟩ := hp (D (qh (W.z (e (.inr t)))))
        exact ⟨a, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun h' => absurd hj h', ha⟩
      · exact ⟨0, fun t' ht => absurd (e.injective ht) Sum.inr_ne_inl, fun _ => rfl,
          by rw [map_zero, hDw _ hj]⟩
  choose d hd1 hd2 hd3 using hd
  obtain ⟨L, hL, hLX, hLs⟩ := rp_ex d
  have hren : ∀ g, L (MvPowerSeries.rename (fun s => e (.inl s)) g) = D₁ (WB.π g) :=
    rp_ext (L ∘ₗ (MvPowerSeries.rename (fun s => e (.inl s)) : MvPowerSeries WB.σ O →ₐ[O] _).toLinearMap)
      (D₁ ∘ₗ WB.π.toLinearMap)
      (fun f g => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, hL,
          MvPowerSeries.constantCoeff_rename])
      (fun f g => by
        have h1 : D₁ (WB.π f * WB.π g) = _ := hD₁ _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, h1, WB.origin_π])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPowerSeries.rename_X, hLX]
        exact hd1 _ s rfl)
  have hk : ∀ f, W.π f = 0 → L f = 0 := fun f hf => by
    have hf' : f ∈ RingHom.ker W.π := hf
    have key : ∀ f ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)), L f = 0 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hg' : WB.π g = 0 := hg
        rw [hren, hg', map_zero]
      | zero => exact map_zero L
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x hx hx' =>
        have : x ∈ RingHom.ker W.π := by rw [hker]; exact hx
        rw [smul_eq_mul, hL, hx', h x this, smul_zero, zero_smul, add_zero]
    exact key f (hker ▸ hf')
  have hs : Function.Surjective W.π.toLinearMap := W.surj
  let E : R →ₗ[O] O := ((LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)) ∘ₗ
    (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm.toLinearMap
  have hE : ∀ f, E (W.π f) = L f := fun f => by
    have : (W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f) = Submodule.Quotient.mk f := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker W.π.toLinearMap).liftQ L (fun f hf => hk f hf)
      ((W.π.toLinearMap.quotKerEquivOfSurjective hs).symm (W.π f)) = _
    rw [this]
    rfl
  have hEd : ∀ a b, E (a * b) = W.origin h a • E b + W.origin h b • E a := fun a b => by
    obtain ⟨f, rfl⟩ := W.surj a
    obtain ⟨g, rfl⟩ := W.surj b
    rw [← map_mul, hE, hE, hE, hL, W.origin_π, W.origin_π]
  have hxo : ∀ f, x₀ (qh (W.π f)) = MvPowerSeries.constantCoeff f := fun f => by
    rw [← AlgHom.comp_apply, hx, W.origin_π]
  have hred : ∀ f, D (qh (W.π f)) = p (L f) :=
    rp_ext (D ∘ₗ (qh.comp W.π).toLinearMap) (p ∘ₗ L)
      (fun f g => by
        have h1 : D (qh (W.π f) * qh (W.π g)) = _ := hD _ _
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, map_mul, h1, hxo])
      (fun f g => by simp only [LinearMap.comp_apply, hL, map_add (f := _), map_smul])
      (fun s => by
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply, hLX, hd3]
        rfl)
  refine ⟨E, hEd, fun i hi a ha => ?_, fun a => ?_⟩
  · obtain ⟨f, hf, hfa⟩ := ha
    have hfa' : W.π f = a := hfa
    rw [← hfa', hE, hLs]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : W.wt s = j
    · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
    · rw [hd2 s hs, smul_zero]
  · obtain ⟨f, hf⟩ := W.surj a
    rw [← hf, hE, hred]

private theorem rp_rename_mem {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ τ : Type} [Finite σ]
    (u : σ → τ) (wt : τ → X) (ws : σ → X) (h : ∀ s, wt (u s) = ws s) {j : X} {g : MvPowerSeries σ O}
    (hg : g ∈ wtPart O ws j) : MvPowerSeries.rename u g ∈ wtPart O wt j := fun n hn => by
  rw [MvPowerSeries.coeff_rename]
  refine Finset.sum_eq_zero fun d hd => hg d fun hj => hn ?_
  have hd' : Finsupp.mapDomain u d = n := by simpa using hd
  rw [← hd', ← hj, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul])]
  simp [h]

private theorem rp_homog {O : Type} [CommRing O] {X : Type} [AddCommGroup X] {σ : Type} [Fintype σ]
    (wt : σ → X) {κ : Type} [Finite κ] (g : κ → MvPowerSeries σ O) (c : κ → X)
    (hg : ∀ i, g i ∈ wtPart O wt (c i)) : IsHomog O wt (Ideal.span (Set.range g)) := by
  have hp : ∀ i, g i ∈ (WPres.free O wt).part (c i) := fun i => ⟨g i, hg i, rfl⟩
  exact (homog_span O _ X (WPres.free O wt) κ (fun i => ⟨g i, (WPres.free O wt).part_le_A (hp i)⟩) c hp).1

private theorem rp_card {α β X : Type} [Finite α] [Finite β] (a : α → X) (b : β → X) (j : X) :
    Nat.card {i // Sum.elim a b i = j} = Nat.card {i // a i = j} + Nat.card {i // b i = j} := by
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  rfl

theorem UpperTheory.nonempty_cover_of_relative_presentation_smoothPt :
    ∀ (O X : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [Module.Free ℤ X] [Module.Finite ℤ X] (B U : Type) [CommRing B] [Algebra O B] [CommRing U] [Algebra O U] (WB : WPres O X B) (hB : WB.HasOrigin) (i : B →ₐ[O] U) (W : WPres O X U) (h : W.HasOrigin) (τ κ : Type) [Fintype τ] (e : WB.σ ⊕ τ ≃ W.σ) (f : κ → MvPowerSeries W.σ O) (wf : κ → X) (n : X → ℕ), IsRelPres WB i W e f wf → SmoothPt WB.part (WB.origin hB) n → Nonempty (Cover WB hB i W h e wf n) := by
  intro O X _ _ _ _ _ _ _ _ _ B U _ _ _ _ WB hB i W h τ κ _ e f wf n hrel hsm
  obtain ⟨he1, he2, hf, hker⟩ := hrel
  obtain ⟨τ₀, _, w, φ, hφ, hdim⟩ := hsm
  set J : Ideal (MvPowerSeries W.σ O) := (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) with hJ
  have hJh : IsHomog O W.wt J := by
    obtain ⟨k, f0, c0, hf0, h0⟩ := ker_gen O X WB.σ WB.wt _ WB.homog
    rw [hJ, h0, Ideal.map_span, ← Set.range_comp]
    exact rp_homog W.wt _ c0 fun t => rp_rename_mem _ W.wt WB.wt he1 (hf0 t)
  have hle : ∀ F ∈ J, W.π F = 0 := fun F hF => (hker ▸ Ideal.mem_sup_left hF : F ∈ RingHom.ker W.π)
  let qh : (MvPowerSeries W.σ O ⧸ J) →ₐ[O] U := Ideal.Quotient.liftₐ J W.π hle
  have hqh : ∀ F, qh (Ideal.Quotient.mk J F) = W.π F := fun _ => rfl
  haveI : Nontrivial (MvPowerSeries W.σ O ⧸ J) := ((W.origin h).comp qh).toRingHom.domain_nontrivial
  haveI := co_mvps O O W.σ
  haveI : IsCO O (MvPowerSeries W.σ O ⧸ J) :=
    co_quot O _ _ (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hkm : RingHom.ker (Ideal.Quotient.mkₐ O J) = J := Ideal.Quotient.mkₐ_ker O J
  let WA : WPres O X (MvPowerSeries W.σ O ⧸ J) :=
    { σ := W.σ, wt := W.wt, π := Ideal.Quotient.mkₐ O J, surj := Ideal.Quotient.mkₐ_surjective O J
      homog := by rw [hkm]; exact hJh }
  obtain ⟨h', ψ, hψ, -⟩ := chart_add O X _ WB hB τ₀ w φ hφ _ WA τ e he1 hkm
  let ρ : MvPowerSeries WB.σ O →ₐ[O] (MvPowerSeries W.σ O ⧸ J) :=
    (Ideal.Quotient.mkₐ O J).comp (MvPowerSeries.rename fun s => e (.inl s))
  have hρ : ∀ F ∈ RingHom.ker WB.π, ρ F = 0 := fun F hF =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hF)
  let iP : B →ₐ[O] (MvPowerSeries W.σ O ⧸ J) :=
    (Ideal.Quotient.liftₐ (RingHom.ker WB.π) ρ hρ).comp
      (Ideal.quotientKerAlgEquivOfSurjective WB.surj).symm.toAlgHom
  have hiP : ∀ F, iP (WB.π F) = ρ F := fun F => by
    have : (Ideal.quotientKerAlgEquivOfSurjective WB.surj).symm (WB.π F) = Ideal.Quotient.mk _ F := by
      rw [AlgEquiv.symm_apply_eq]; rfl
    show Ideal.Quotient.liftₐ (RingHom.ker WB.π) ρ hρ
      ((Ideal.quotientKerAlgEquivOfSurjective WB.surj).symm (WB.π F)) = _
    rw [this]
    rfl
  have hor : (W.origin h).comp qh = WA.origin h' := AlgHom.ext fun y => by
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact (W.origin_π h F).trans (WA.origin_π h' F).symm
  have hzl : ∀ s, W.z (e (.inl s)) = i (WB.z s) := fun s => by
    rw [WPres.z, WPres.z, ← he2, MvPowerSeries.rename_X]
  refine ⟨{
    P := MvPowerSeries W.σ O ⧸ J
    WP := WA
    org := h'
    p := qh
    iP := iP
    g := fun u => Ideal.Quotient.mk J (f u)
    wts := fun s => ⟨s, rfl⟩
    surj := fun y => ?_
    part := fun j => ?_
    comp := AlgHom.ext fun y => ?_
    org_p := hor
    hg := fun u => ⟨_, hf u, rfl⟩
    ker := ?_
    smooth := ⟨τ₀ ⊕ τ, inferInstance, _, ψ, hψ, fun j => ?_⟩
    der := fun a j Db hDb DB hDB hw hi hz => ?_ }⟩
  · obtain ⟨F, rfl⟩ := W.surj y
    exact ⟨_, hqh F⟩
  · ext y
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
      exact ⟨F, hF, rfl⟩
  · obtain ⟨F, rfl⟩ := WB.surj y
    rw [AlgHom.comp_apply, hiP, ← he2]
    rfl
  · refine le_antisymm (fun y hy => ?_) (Ideal.span_le.2 ?_)
    · obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
      have h3 : F ∈ J ⊔ Ideal.span (Set.range f) := by
        rw [← hker]
        exact hy
      have h4 : J ⊔ Ideal.span (Set.range f) ≤
          (Ideal.span (Set.range fun k => Ideal.Quotient.mk J (f k))).comap (Ideal.Quotient.mk J) := by
        refine sup_le (fun y hy => ?_) (Ideal.span_le.2 ?_)
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hy]
          exact zero_mem _
        · rintro _ ⟨k, rfl⟩
          exact Ideal.subset_span ⟨k, rfl⟩
      exact h4 h3
    · rintro _ ⟨k, rfl⟩
      exact (hker ▸ Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩) : f k ∈ RingHom.ker W.π)
  · rw [rp_card, hdim]
  · have hB0 : ∀ s, WB.wt s ≠ j → DB (WB.z s) = 0 := fun s hs => hw _ hs _ (WB.z_mem s)
    refine rp_lift WB hB WA h' e he1 hkm qh (W.origin h) hor (Ideal.Quotient.mkₐ O _).toLinearMap
      (Ideal.Quotient.mkₐ_surjective O _) j Db hDb (fun s hs => ?_) DB hDB hB0 fun s => ?_
    · obtain ⟨s | t, rfl⟩ := e.surjective s
      · show Db (W.z (e (.inl s))) = 0
        rw [hzl, hi, hB0 s (by rw [← he1]; exact hs), map_zero]
      · exact hz t hs
    · show _ = Db (W.z (e (.inl s)))
      rw [hzl, hi]
      rfl
end
