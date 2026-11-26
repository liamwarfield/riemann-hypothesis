module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsOfUniformisation
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesOfNaturalNilpotentPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalGroupSeriesToricPointExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalGroupSeriesToricPointExtension
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem chi_ext {X S : Type} [AddCommGroup X] [CommRing S] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (χ χ' : Multiplicative X →* Sˣ)
    (h : ∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = χ' (Multiplicative.ofAdd (β j))) : χ = χ' := by
  have : (MonoidHom.toAdditiveRight χ).toIntLinearMap = (MonoidHom.toAdditiveRight χ').toIntLinearMap :=
    β.ext fun j => congrArg Additive.ofMul (Units.ext (h j))
  refine MonoidHom.ext fun y => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun this y.toAdd)

private theorem chi_ex {X S : Type} [AddCommGroup X] [CommRing S] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (t : Fin r → S) (ht : ∀ i, IsNilpotent (t i)) :
    ∃ χ : Multiplicative X →* Sˣ, ∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j := by
  refine ⟨MonoidHom.toAdditiveRight.symm (β.constr ℤ
    (fun j => Additive.ofMul (ht j).isUnit_one_add.unit)).toAddMonoidHom, fun j => ?_⟩
  change ((Additive.toMul (β.constr ℤ (fun j => Additive.ofMul (ht j).isUnit_one_add.unit) (β j)) : Sˣ) : S) = _
  rw [Module.Basis.constr_basis]
  rfl

private def pairAlg (R : Type) {S : Type} [CommRing R] [CommRing S] [Algebra R S] (J : Ideal S) :
    Subalgebra R (S × S) where
  carrier := {p | p.2 - p.1 ∈ J}
  mul_mem' := fun {a b} ha hb => by
    have : (a * b).2 - (a * b).1 = a.2 * (b.2 - b.1) + (a.2 - a.1) * b.1 := by simp; ring
    change _ ∈ J
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hb) (J.mul_mem_right _ ha)
  add_mem' := fun {a b} ha hb => by
    have : (a + b).2 - (a + b).1 = (a.2 - a.1) + (b.2 - b.1) := by simp; ring
    change _ ∈ J
    rw [this]
    exact J.add_mem ha hb
  algebraMap_mem' := fun c => by
    change _ ∈ J
    simp

private theorem coord_ex {R : Type} [CommRing R] {I : Ideal R} {G B : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [GrpObj B] {X : Type} [AddCommGroup X] (E : PtExt I G B X) {d r : ℕ} {F : Fin d → PS R 2 d} {x : Fam G d}
    (hx : NilChart G F x) (β : Module.Basis (Fin r) ℤ X) (S : Type) [CommRing S] [Algebra R S]
    (h : ∃ k, Kills I k S) (t : Fin r → S) (ht : ∀ i, IsNilpotent (t i)) :
    ∃ b : Fin d → S, (∀ i, IsNilpotent (b i)) ∧ ∀ χ : Multiplicative X →* Sˣ,
      (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S b := by
  let J : Ideal S := Ideal.span (Set.range t)
  obtain ⟨N, hN⟩ : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical ⟨(Set.finite_range t).toFinset, by simp [J]⟩).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  let P : Type := pairAlg R J
  let ρ : P →ₐ[R] S := (AlgHom.fst R S S).comp (pairAlg R J).val
  let τ : P →ₐ[R] S := (AlgHom.snd R S S).comp (pairAlg R J).val
  let σ : S →ₐ[R] P := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict _ (fun y => by
    change _ ∈ J
    simp)
  have hinj : ∀ p : P, ρ p = 0 → τ p = 0 → p = 0 := fun p h1 h2 => Subtype.ext (Prod.ext h1 h2)
  have hker : IsNilpotent (RingHom.ker ρ) := by
    refine ⟨N + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff]
    intro p hp
    have h1 : RingHom.ker ρ ≤ J.comap τ := fun q hq => by
      have h2 : τ q - ρ q ∈ J := q.2
      rw [RingHom.mem_ker] at hq
      rwa [hq, sub_zero] at h2
    have h2 := Ideal.pow_le_self (I := RingHom.ker ρ) (Nat.succ_ne_zero N) hp
    have h3 := Ideal.le_comap_pow τ (N + 1) (Ideal.pow_right_mono h1 (N + 1) hp)
    rw [pow_succ, hN, zero_mul, Ideal.mem_comap, Ideal.zero_eq_bot, Ideal.mem_bot] at h3
    exact hinj p h2 h3
  have hP : ∃ k, Kills I k P := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, fun c hc => hinj _ (by rw [AlgHom.commutes, hk c hc]) (by rw [AlgHom.commutes, hk c hc])⟩
  let u : Fin r → P := fun j => ⟨(0, t j), by
    change t j - 0 ∈ J
    rw [sub_zero]
    exact Ideal.subset_span ⟨j, rfl⟩⟩
  have hnil : ∀ p : P, ρ p = 0 → IsNilpotent p := fun p hp => by
    obtain ⟨n, hn⟩ := hker
    have := Ideal.pow_mem_pow (show p ∈ RingHom.ker ρ from hp) n
    rw [hn] at this
    exact ⟨n, this⟩
  obtain ⟨χ₁, hχ₁⟩ := chi_ex β u (fun j => hnil _ rfl)
  have h1 : (Units.map (ρ : P →* S)).comp χ₁ = 1 := chi_ext β _ _ fun j => by
    change ρ (χ₁ _ : P) = 1
    rw [hχ₁, map_add (f := _), map_one]
    exact add_zero _
  obtain ⟨a, ha, hz⟩ := hx.surj P S ρ σ (AlgHom.ext fun _ => rfl) hker (E.i P hP χ₁)
    (by rw [← E.i_nat P S ρ hP h, h1, map_one])
  refine ⟨fun i => τ (a i), fun i => (hnil _ (ha i)).map τ, fun χ hχ => ?_⟩
  rw [← hx.nat P S τ a (fun i => hnil _ (ha i)), ← hz, ← E.i_nat P S τ hP h]
  congr 1
  refine chi_ext β _ _ fun j => ?_
  change _ = τ (χ₁ _ : P)
  rw [hχ₁, map_add (f := _), map_one, hχ]
  rfl

theorem exists_series_torus : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X), ∃ J : Fin d → PS R 1 r, IsHomF (gmF R r) F.F J ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) := by
  intro R _ I hI G _ _ B _ _ X _ E d g F FB x xB hx _ r β
  classical
  have hc : ∀ (S : Type) [CommRing S] [Algebra R S] (t : Fin r → S), ∃ b : Fin d → S,
      ∀ h : ∃ k, Kills I k S, (∀ i, IsNilpotent (t i)) → (∀ i, IsNilpotent (b i)) ∧ ∀ χ : Multiplicative X →* Sˣ,
      (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S b := by
    intro S _ _ t
    by_cases h : (∃ k, Kills I k S) ∧ ∀ i, IsNilpotent (t i)
    · obtain ⟨b, hb⟩ := coord_ex E hx β S h.1 t h.2
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose c hc using hc
  have hJ : ∀ j : Fin d, ∃ f : PS R 1 r, ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin 1 → Fin r → S),
      True → (∃ k, Kills I k S) → (∀ i j, IsNilpotent (a i j)) → c S (a 0) j = nv (algebraMap R S) f a := by
    intro j
    refine exists_series_of_natural R I hI 1 r (fun _ _ _ => True) (fun _ _ => trivial) (fun S _ _ a => c S (a 0) j) ?_
    intro S _ _ S' _ _ φ a _ _ _ h ha
    have h' : ∃ k, Kills I k S' := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, fun c hc => by rw [← φ.commutes, hk c hc, map_zero]⟩
    obtain ⟨χ, hχ⟩ := chi_ex β (a 0) (ha 0)
    obtain ⟨h1, h2⟩ := hc S (a 0) h (ha 0)
    obtain ⟨h3, h4⟩ := hc S' (fun j => φ (a 0 j)) h' (fun i => (ha 0 i).map φ)
    have h5 := h4 ((Units.map (φ : S →* S')).comp χ) fun j => by
      change φ (χ _ : S) = _
      rw [hχ, map_add (f := _), map_one]
    rw [E.i_nat S S' φ h h', h2 χ hχ, hx.nat S S' φ _ h1] at h5
    exact congrFun (hx.inj S' _ _ (fun i => (h1 i).map φ) h3 h5) j
  choose J hJ using hJ
  have hJ' : ∀ (S : Type) [CommRing S] [Algebra R S] (t : Fin r → S), (∃ k, Kills I k S) →
      (∀ i, IsNilpotent (t i)) → (fun j => nv (algebraMap R S) (J j) ![t]) = c S t := by
    intro S _ _ t h ht
    funext j
    exact (hJ j S ![t] trivial h (fun i => by fin_cases i; exact ht)).symm
  have h0 : ∀ j, MvPowerSeries.constantCoeff (J j) = 0 := by
    intro j
    have : (MvPowerSeries.C (MvPowerSeries.constantCoeff (J j)) : PS R 1 r) = 0 := by
      refine eq_of_nv_eq R I inferInstance 1 r _ _ fun S _ _ k hk _ a ha => ?_
      obtain ⟨ψ, h1, h2, -⟩ := (nv_calculus R S (algebraMap R S) 1 r a ha).1
      rw [← h1, ← h1, h2, map_zero]
      have hz : ∀ i : Fin r, IsNilpotent ((0 : Fin r → S) i) := fun _ => IsNilpotent.zero
      obtain ⟨h3, h4⟩ := hc S 0 ⟨k, hk⟩ hz
      have h5 := h4 1 (fun j => by simp)
      rw [map_one, ← hx.zero S] at h5
      have h6 := congrFun ((hJ' S 0 ⟨k, hk⟩ hz).trans
        (hx.inj S _ _ (fun _ => IsNilpotent.zero) h3 h5).symm) j
      rw [(nv_calculus R S (algebraMap R S) 1 r ![0] (fun i => by fin_cases i; exact hz)).2.2.2.2.2
        (fun i _ i' _ => by fin_cases i; simp)] at h6
      simpa using h6
    simpa using congrArg MvPowerSeries.constantCoeff this
  refine ⟨J, ⟨h0, fun j => ?_⟩, fun S _ _ h χ t ht hχ => ?_⟩
  · refine eq_of_nv_eq R I inferInstance 2 r _ _ fun S _ _ k hk _ a ha => ?_
    have h : ∃ k, Kills I k S := ⟨k, hk⟩
    obtain ⟨⟨ψ, hψ, -, hX⟩, -, hs, -⟩ := nv_calculus R S (algebraMap R S) 2 r a ha
    have hev : ∀ (p : Fin r → PS R 2 r) (t : Fin r → S), (∀ i, MvPowerSeries.constantCoeff (p i) = 0) →
        (∀ i, ψ (p i) = t i) → (∀ i, IsNilpotent (t i)) →
        ∀ i, nv (algebraMap R S) (ev (n := 2) ![p] (J i)) a = c S t i := by
      intro p t hp hpt ht i
      rw [← hJ' S t h ht]
      refine (hs 1 r ![p] (J i) (fun i => by fin_cases i; exact hp)).trans ?_
      congr 1
      funext i j
      fin_cases i
      exact (hψ _).symm.trans (hpt j)
    have hcc : ∀ (l : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff (ev (n := 2) ![pt R r l] (J i)) = 0 := by
      intro l i
      have hp : ∀ q : Fin 1 × Fin r, MvPowerSeries.constantCoeff ((![pt R r l] : Fin 1 → Pt R 2 r) q.1 q.2) = 0 := by
        rintro ⟨q, q'⟩
        fin_cases q
        simp [pt]
      exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero hp) hp (h0 i)
    have hn : ∀ i, IsNilpotent (a 0 i + a 1 i + a 0 i * a 1 i) := fun i =>
      (Commute.all _ _).isNilpotent_add ((Commute.all _ _).isNilpotent_add (ha 0 i) (ha 1 i))
        ((Commute.all _ _).isNilpotent_mul_left (ha 1 i))
    rw [hev (gmF R r) _ (fun i => by simp [gmF]) (fun i => by simp [gmF, hX]) hn,
      hs _ _ _ _ (fun l => by fin_cases l <;> exact hcc _)]
    obtain ⟨χ₀, hχ₀⟩ := chi_ex β (a 0) (ha 0)
    obtain ⟨χ₁, hχ₁⟩ := chi_ex β (a 1) (ha 1)
    obtain ⟨n0, e0⟩ := hc S (a 0) h (ha 0)
    obtain ⟨n1, e1⟩ := hc S (a 1) h (ha 1)
    obtain ⟨n2, e2⟩ := hc S _ h hn
    have e3 := e2 (χ₀ * χ₁) fun j => by
      rw [MonoidHom.mul_apply, Units.val_mul, hχ₀, hχ₁]
      ring
    rw [map_mul, e0 _ hχ₀, e1 _ hχ₁, hx.law S _ _ n0 n1] at e3
    have n3 : ∀ k, IsNilpotent (nv (algebraMap R S) (F.F k) ![c S (a 0), c S (a 1)]) := fun k =>
      ((nv_calculus R S (algebraMap R S) 2 d _ (fun l => by
        fin_cases l
        · exact n0
        · exact n1)).2.1 _ (F.const k)).1
    rw [← congrFun (hx.inj S _ _ n3 n2 e3) j]
    congr 1
    funext l i
    fin_cases l
    · exact (hev (pt R r 0) (a 0) (fun i => by simp [pt]) (fun i => hX (0, i)) (ha 0) i).symm
    · exact (hev (pt R r 1) (a 1) (fun i => by simp [pt]) (fun i => hX (1, i)) (ha 1) i).symm
  · rw [hJ' S t h ht]
    exact (hc S t h ht).2 χ hχ

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalGroupSeriesToricPointExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroupSeries_toricPointExtension : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X), ∃ J : Fin d → PS R 1 r, IsHomF (gmF R r) F.F J ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) := by
  first | exact @GlobalTheory.ChF.exists_series_torus | exact GlobalTheory.ChF.exists_series_torus | (intros; apply GlobalTheory.ChF.exists_series_torus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionAbelianPartFormalGroupHom
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionAbelianPartFormalGroupHom
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem kills_of_algHom {R : Type} [CommRing R] {I : Ideal R} {S S' : Type} [CommRing S] [Algebra R S]
    [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (h : ∃ k, Kills I k S) : ∃ k, Kills I k S' := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun t ht => by rw [← φ.commutes, hk t ht, map_zero]⟩

private theorem exists_split_thickening {R : Type} [CommRing R] {d : ℕ} (S : Type) [CommRing S] [Algebra R S]
    (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra R T) (ρ π : T →ₐ[R] S) (σ : S →ₐ[R] T) (a' : Fin d → T),
      ρ.comp σ = AlgHom.id R S ∧ IsNilpotent (RingHom.ker ρ) ∧ (∀ i, ρ (a' i) = 0) ∧ ∀ i, π (a' i) = a i := by
  let J : Ideal S := Ideal.span (Set.range a)
  have hJ : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ha i
  let T : Subalgebra R (S × S) := AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R S S))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R S S))
  let ρ : T →ₐ[R] S := (AlgHom.fst R S S).comp T.val
  let π : T →ₐ[R] S := (AlgHom.snd R S S).comp T.val
  let σ : S →ₐ[R] T := ((AlgHom.id R S).prod (AlgHom.id R S)).codRestrict T (fun _ => rfl)
  have hm : ∀ i, ((0, a i) : S × S) ∈ T := fun i => by
    show Ideal.Quotient.mk J 0 = Ideal.Quotient.mk J (a i)
    rw [map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨i, rfl⟩
  refine ⟨T, inferInstance, inferInstance, ρ, π, σ, fun i => ⟨(0, a i), hm i⟩, rfl, ?_, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨N, hN⟩ := hJ
  have hle : RingHom.ker ρ ≤ J.comap π := fun t ht => by
    have h1 : t.1.1 = 0 := ht
    have h2 : Ideal.Quotient.mk J t.1.1 = Ideal.Quotient.mk J t.1.2 := t.2
    rw [h1, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at h2
    exact h2
  refine ⟨N + 1, le_bot_iff.1 fun t ht => ?_⟩
  have h1 : t.1.1 = 0 := (Ideal.pow_le_self (Nat.succ_ne_zero N) ht : t ∈ RingHom.ker ρ)
  have h2 := Ideal.le_comap_pow π N (Ideal.pow_right_mono hle N (Ideal.pow_le_pow_right (Nat.le_succ N) ht))
  rw [hN] at h2
  have h3 : π t = 0 := by simpa using h2
  exact Subtype.ext (Prod.ext h1 h3)

private theorem exists_nilpotent_image {R : Type} [CommRing R] {I : Ideal R}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {B : Over (Spec (CommRingCat.of R))} [GrpObj B]
    {X : Type} [AddCommGroup X] (E : PtExt I G B X) {d g : ℕ} {F : Fin d → PS R 2 d} {FB : Fin g → PS R 2 g}
    {x : Fam G d} {xB : Fam B g} (hx : NilChart G F x) (hB : NilChart B FB xB)
    (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S) (ha : ∀ i, IsNilpotent (a i)) :
    ∃ b : Fin g → S, (∀ j, IsNilpotent (b j)) ∧ E.q S h (x S a) = xB S b := by
  obtain ⟨T, _, _, ρ, π, σ, a', hσ, ⟨N, hN⟩, h0, h1⟩ := exists_split_thickening (R := R) S a ha
  have hT := kills_of_algHom σ h
  have hnil : ∀ t : T, ρ t = 0 → IsNilpotent t := fun t ht => ⟨N, by
    have := Ideal.pow_mem_pow (show t ∈ RingHom.ker ρ from ht) N
    rw [hN] at this
    simpa using this⟩
  have ha' : ∀ i, IsNilpotent (a' i) := fun i => hnil _ (h0 i)
  obtain ⟨b, hb, hz⟩ := hB.surj T S ρ σ hσ ⟨N, hN⟩ (E.q T hT (x T a')) (by
    rw [← E.q_nat T S ρ hT h, hx.nat T S ρ a' ha', show (fun i => ρ (a' i)) = 0 from funext h0, hx.zero,
      map_one])
  have hb' : ∀ j, IsNilpotent (b j) := fun j => hnil _ (hb j)
  refine ⟨fun j => π (b j), fun j => (hb' j).map π, ?_⟩
  rw [← hB.nat T S π b hb', ← hz, ← E.q_nat T S π hT h, hx.nat T S π a' ha', show (fun i => π (a' i)) = a from funext h1]

theorem ptExt_q_series : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∃ Q : Fin g → PS R 1 d, IsHomF F.F FB.F Q ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) := by
  intro R _ I hI G _ _ B _ _ X _ E d g F FB x xB hx hB
  classical
  let c : ∀ (S : Type) [CommRing S] [Algebra R S], (Fin d → S) → Fin g → S := fun S _ _ a =>
    if h : (∃ k, Kills I k S) ∧ ∀ i, IsNilpotent (a i) then
      (exists_nilpotent_image E hx hB S h.1 a h.2).choose else 0
  have hc : ∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S),
      (∀ i, IsNilpotent (a i)) → (∀ j, IsNilpotent (c S a j)) ∧ E.q S h (x S a) = xB S (c S a) := by
    intro S _ _ h a ha
    have : c S a = (exists_nilpotent_image E hx hB S h a ha).choose := dif_pos ⟨h, ha⟩
    rw [this]
    exact (exists_nilpotent_image E hx hB S h a ha).choose_spec
  have hnat : ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S')
      (a : Fin d → S), (∃ k, Kills I k S) → (∀ i, IsNilpotent (a i)) →
      (fun j => φ (c S a j)) = c S' (fun i => φ (a i)) := by
    intro S _ _ S' _ _ φ a h ha
    have h' := kills_of_algHom φ h
    have ha' : ∀ i, IsNilpotent (φ (a i)) := fun i => (ha i).map φ
    refine hB.inj S' _ _ (fun j => ((hc S h a ha).1 j).map φ) (hc S' h' _ ha').1 ?_
    rw [← (hc S' h' _ ha').2, ← hB.nat S S' φ _ (hc S h a ha).1, ← (hc S h a ha).2, ← E.q_nat S S' φ h h',
      hx.nat S S' φ a ha]
  choose Q hQ using fun j : Fin g => GlobalTheory.T.exists_powerSeries_of_natural_nilpotentPoints R I hI 1 d (fun _ _ _ => True) (fun _ _ => trivial)
    (fun S _ _ a => c S (a 0) j)
    (fun S _ _ S' _ _ φ a _ _ _ h ha => congrFun (hnat S S' φ (a 0) h (ha 0)) j)
  have hQ' : ∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S),
      (∀ i, IsNilpotent (a i)) → (fun j => nv (algebraMap R S) (Q j) ![a]) = c S a := by
    intro S _ _ h a ha
    funext j
    exact (hQ j S ![a] trivial h (fun i l => by fin_cases i; exact ha l)).symm
  have hconst : ∀ j, MvPowerSeries.constantCoeff (Q j) = 0 := by
    intro j
    refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
    have hk : ∃ m, Kills I m (R ⧸ I ^ (k + 1)) := ⟨k, fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 ht⟩
    have h0 : ∀ i : Fin d, IsNilpotent ((0 : Fin d → R ⧸ I ^ (k + 1)) i) := fun _ => IsNilpotent.zero
    have h1 : c (R ⧸ I ^ (k + 1)) 0 = 0 :=
      hB.inj _ _ _ (hc _ hk 0 h0).1 (fun _ => IsNilpotent.zero) (by
        rw [← (hc _ hk 0 h0).2, hx.zero, hB.zero, map_one])
    have h2 := congrFun (hQ' _ hk 0 h0) j
    have h3 := (nv_calculus R (R ⧸ I ^ (k + 1)) (algebraMap _ _) 1 d ![0]
      (fun i l => by fin_cases i; exact h0 l)).2.2.2.2.2 (fun i l i' l' => by fin_cases i; simp) (Q j)
    rw [h1] at h2
    rw [h2] at h3
    have h4 : algebraMap R (R ⧸ I ^ (k + 1)) (MvPowerSeries.constantCoeff (Q j)) = 0 := by
      simpa using h3.symm
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact Ideal.pow_le_pow_right (Nat.le_succ k) (Ideal.Quotient.eq_zero_iff_mem.1 h4)
  refine ⟨Q, ⟨hconst, fun j => ?_⟩, fun S _ _ h a ha => by rw [hQ' S h a ha]; exact (hc S h a ha).2⟩
  refine GlobalTheory.T.powerSeries_eq_of_evalAtNilpotentPoints_eq R I inferInstance 2 d _ _ fun S _ _ k hk _ a ha => ?_
  have h : ∃ k, Kills I k S := ⟨k, hk⟩
  obtain ⟨⟨ψ, hψ, -, hX⟩, hn, hs, -⟩ := nv_calculus R S (algebraMap R S) 2 d a ha
  have hpt : ∀ i : Fin 2, ∀ l, nv (algebraMap R S) (ev (n := 2) ![pt R d i] (Q l)) a = c S (a i) l := by
    intro i l
    have e := hs 1 d ![pt R d i] (Q l) (fun i' l' => by fin_cases i'; simp [pt])
    have e2 : (fun i' l' => nv (algebraMap R S) ((![pt R d i] : Fin 1 → Fin d → PS R 2 d) i' l') a) = ![a i] := by
      funext i' l'
      fin_cases i'
      exact (hψ _).symm.trans (hX (i, l'))
    rw [e2] at e
    exact e.trans (congrFun (hQ' S h (a i) (ha i)) l)
  have hpc : ∀ i : Fin 2, ∀ l, MvPowerSeries.constantCoeff (ev (n := 2) ![pt R d i] (Q l)) = 0 := by
    intro i l
    refine MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero ?_) ?_ (hconst l)
    all_goals
      rintro ⟨i', l'⟩
      fin_cases i'
      simp [pt]
  have ea : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
  have hFn : ∀ l, IsNilpotent (nv (algebraMap R S) (F.F l) a) := fun l => (hn _ (F.const l)).1
  have e1 := hs 1 d ![F.F] (Q j) (fun i' l' => by fin_cases i'; exact F.const l')
  have e2 : (fun i' l' => nv (algebraMap R S) ((![F.F] : Fin 1 → Fin d → PS R 2 d) i' l') a) =
      ![fun l => nv (algebraMap R S) (F.F l) a] := by
    funext i' l'
    fin_cases i'
    rfl
  rw [e2] at e1
  have e3 := hs 2 g ![fun i => ev (n := 2) ![pt R d 0] (Q i), fun i => ev (n := 2) ![pt R d 1] (Q i)] (FB.F j)
    (fun i' l' => by fin_cases i'; exacts [hpc 0 l', hpc 1 l'])
  have e4 : (fun i' l' => nv (algebraMap R S) ((![fun i => ev (n := 2) ![pt R d 0] (Q i),
      fun i => ev (n := 2) ![pt R d 1] (Q i)] : Fin 2 → Fin g → PS R 2 d) i' l') a) = ![c S (a 0), c S (a 1)] := by
    funext i' l'
    fin_cases i'
    exacts [hpt 0 l', hpt 1 l']
  rw [e4] at e3
  have hcn : ∀ i l, IsNilpotent ((![c S (a 0), c S (a 1)] : Fin 2 → Fin g → S) i l) := fun i l => by
    fin_cases i
    exacts [(hc S h _ (ha 0)).1 l, (hc S h _ (ha 1)).1 l]
  have key : c S (fun l => nv (algebraMap R S) (F.F l) a) =
      fun l => nv (algebraMap R S) (FB.F l) ![c S (a 0), c S (a 1)] := by
    refine hB.inj S _ _ (hc S h _ hFn).1
      (fun l => ((nv_calculus R S (algebraMap R S) 2 g _ hcn).2.1 _ (FB.const l)).1) ?_
    rw [← (hc S h _ hFn).2, ← hB.law S _ _ (hc S h _ (ha 0)).1 (hc S h _ (ha 1)).1, ← (hc S h _ (ha 0)).2,
      ← (hc S h _ (ha 1)).2, ← map_mul, hx.law S _ _ (ha 0) (ha 1), ← ea]
  rw [e3]
  exact e1.trans ((congrFun (hQ' S h _ hFn) j).trans (congrFun key j))

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionAbelianPartFormalGroupHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPointExtension_abelianPart_formalGroup_hom : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∃ Q : Fin g → PS R 1 d, IsHomF F.F FB.F Q ∧ (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) := by
  first | exact @GlobalTheory.ChF.ptExt_q_series | exact GlobalTheory.ChF.ptExt_q_series | (intros; apply GlobalTheory.ChF.ptExt_q_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqSplitExact
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqSplitExact
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem isUnit_of_map_eq_one {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (h : M.map (Ideal.Quotient.mk I) = 1) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have h1 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, h, Matrix.det_one, map_one]
  have h2 := IsAdicComplete.le_jacobson_bot I (Ideal.Quotient.eq.1 h1)
  have := Ideal.mem_jacobson_bot.1 h2 1
  simpa using this

private theorem splitEx_of_exact {K : Type} [CommRing K] {d r g : ℕ} (A : Matrix (Fin d) (Fin r) K)
    (B : Matrix (Fin g) (Fin d) K) (h0 : B * A = 0) (h1 : ∀ w, ∃ v, B *ᵥ v = w)
    (h2 : ∀ v, B *ᵥ v = 0 → ∃ t, A *ᵥ t = v) (h3 : ∀ t, A *ᵥ t = 0 → t = 0) : SplitEx A B := by
  choose v hv using h1
  let B' : Matrix (Fin d) (Fin g) K := Matrix.of fun i j => v (Pi.single j 1) i
  have hB : B * B' = 1 := by
    ext i j
    have := congrFun (hv (Pi.single j 1)) i
    rw [Matrix.one_apply, ← Pi.single_apply j (1 : K) i, ← this]
    rfl
  have h4 : ∀ j : Fin d, ∃ t, A *ᵥ t = (1 - B' * B) *ᵥ (Pi.single j 1) := fun j => h2 _ (by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, ← Matrix.mul_assoc, hB, Matrix.mul_one, Matrix.one_mul, sub_self,
      Matrix.zero_mulVec])
  choose t ht using h4
  let A' : Matrix (Fin r) (Fin d) K := Matrix.of fun i j => t j i
  have hA : A * A' = 1 - B' * B := by
    ext i j
    have := congrFun (ht j) i
    rw [Matrix.mulVec_single_one] at this
    exact this
  refine ⟨h0, A', B', ?_, hB, by rw [hA]; simp⟩
  have h5 : A * (A' * A - 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hA, Matrix.sub_mul, Matrix.mul_assoc, h0]; simp
  rw [← sub_eq_zero]
  ext i j
  have := h3 ((A' * A - 1) *ᵥ Pi.single j 1) (by rw [Matrix.mulVec_mulVec, h5, Matrix.zero_mulVec])
  rw [Matrix.mulVec_single_one] at this
  exact congrFun this i

private theorem splitEx_lift {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {d r g : ℕ}
    (A : Matrix (Fin d) (Fin r) R) (B : Matrix (Fin g) (Fin d) R) (h0 : B * A = 0)
    (h : SplitEx (A.map (Ideal.Quotient.mk I)) (B.map (Ideal.Quotient.mk I))) : SplitEx A B := by
  obtain ⟨-, A1, B1, h1, h2, h3⟩ := h
  let A0 : Matrix (Fin r) (Fin d) R := A1.map (Function.surjInv Ideal.Quotient.mk_surjective)
  let B0 : Matrix (Fin d) (Fin g) R := B1.map (Function.surjInv Ideal.Quotient.mk_surjective)
  have hA0 : A0.map (Ideal.Quotient.mk I) = A1 := by
    ext i j; exact Function.surjInv_eq _ _
  have hB0 : B0.map (Ideal.Quotient.mk I) = B1 := by
    ext i j; exact Function.surjInv_eq _ _
  obtain ⟨U, hU⟩ := isUnit_of_map_eq_one I (A0 * A) (by rw [Matrix.map_mul, hA0, h1])
  obtain ⟨V, hV⟩ := isUnit_of_map_eq_one I (B * B0) (by rw [Matrix.map_mul, hB0, h2])
  obtain ⟨M, hM⟩ := isUnit_of_map_eq_one I (A * A0 + B0 * B) (by
    rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, hA0, hB0, h3])
  obtain ⟨B', hB', hB0'⟩ : ∃ B' : Matrix (Fin d) (Fin g) R, B * B' = 1 ∧ B0 = B' * V.val :=
    ⟨B0 * (V⁻¹).val, by rw [← Matrix.mul_assoc, ← hV]; simp, by rw [Matrix.mul_assoc]; simp⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : Matrix (Fin r) (Fin d) R, A2 * A = 1 :=
    ⟨(U⁻¹).val * A0, by rw [Matrix.mul_assoc, ← hU]; simp⟩
  have e1 : A2 * (1 - B' * B) * A = 1 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc, h0]; simp [hA2]
  have e2 : A2 * (1 - B' * B) * B' = 0 := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc, hB']; simp
  refine ⟨h0, A2 * (1 - B' * B), B', e1, hB', ?_⟩
  generalize A2 * (1 - B' * B) = A' at e1 e2
  have p1 : (A * A' + B' * B) * A = A := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, e1, h0]; simp
  have p2 : (A * A' + B' * B) * B' = B' := by
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, e2, hB']; simp
  have p3 : (A * A' + B' * B) * M.val = 1 * M.val := by
    rw [hM, hB0', Matrix.mul_add, ← Matrix.mul_assoc, p1, Matrix.mul_assoc B', ← Matrix.mul_assoc _ B', p2,
      Matrix.one_mul]
  exact (Units.mul_left_inj M).1 p3

section Dual
variable {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K]

private def epsV {n : ℕ} (v : Fin n → K) : Fin n → DualNumber K := fun i => TrivSqZeroExt.inr (v i)

private theorem epsV_nil {n : ℕ} (v : Fin n → K) (i : Fin n) : IsNilpotent (epsV v i) :=
  ⟨2, by rw [pow_two]; exact TrivSqZeroExt.inr_mul_inr _ _ _⟩

private theorem epsV_zero {n : ℕ} : epsV (0 : Fin n → K) = 0 := by
  funext i; exact TrivSqZeroExt.inr_zero _

private theorem epsV_inj {n : ℕ} {v w : Fin n → K} (h : epsV v = epsV w) : v = w := by
  funext i; exact TrivSqZeroExt.inr_injective (congrFun h i)

private theorem nv_epsV {n m : ℕ} (φ : Fin m → PS R 1 n) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (v : Fin n → K) : (fun j => nv (algebraMap R (DualNumber K)) (φ j) ![epsV v]) =
      epsV ((lin φ).map (algebraMap R K) *ᵥ v) := by
  funext j
  have h := (nv_calculus R (DualNumber K) (algebraMap R _) 1 n ![epsV v]
    (fun i j => by simpa using epsV_nil v j)).2.2.2.2.2
    (fun i j i' j' => by simp [epsV]) (φ j)
  rw [h, hφ, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [epsV, Matrix.mulVec, dotProduct, TrivSqZeroExt.inr_sum, Matrix.map_apply, lin, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def, ← Algebra.smul_def, TrivSqZeroExt.inr_smul]
  rfl

private theorem kills_dual {I : Ideal R} {k : ℕ} (h : Kills I k K) : Kills I k (DualNumber K) := fun t ht => by
  rw [TrivSqZeroExt.algebraMap_eq_inl', h t ht, TrivSqZeroExt.inl_zero]

private theorem exists_char {X : Type} [AddCommGroup X] {r : ℕ} (β : Module.Basis (Fin r) ℤ X) (t : Fin r → K) :
    ∃ χ : Multiplicative X →* (DualNumber K)ˣ, ∀ j,
      (χ (Multiplicative.ofAdd (β j)) : DualNumber K) = 1 + epsV t j := by
  let u : Fin r → (DualNumber K)ˣ := fun j => (epsV_nil t j).isUnit_one_add.unit
  let f : X →ₗ[ℤ] Additive (DualNumber K)ˣ := β.constr ℤ fun j => Additive.ofMul (u j)
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, fun j => ?_⟩
  have : f (β j) = Additive.ofMul (u j) := β.constr_basis ℤ _ j
  change ((Additive.toMul (f (β j)) : (DualNumber K)ˣ) : DualNumber K) = _
  rw [this]; rfl

private theorem eq_epsV {n : ℕ} (a : Fin n → DualNumber K) (h : ∀ i, (a i).fst = 0) :
    a = epsV fun i => (a i).snd := by
  funext i; ext <;> simp [epsV, h]

end Dual

theorem tangent_splitEx : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → SplitEx (lin J) (lin Q) := by
  intro R _ I _ G _ _ B _ _ X _ E d g F FB x xB hx hxB r β J Q hJ hQ hq hi
  have key : ∀ (K : Type) [CommRing K] [Algebra R K] (k : ℕ), Kills I k K →
      SplitEx ((lin J).map (algebraMap R K)) ((lin Q).map (algebraMap R K)) := by
    intro K _ _ k hK
    have hS : ∃ k, Kills I k (DualNumber K) := ⟨k, kills_dual hK⟩
    have hq' : ∀ v, E.q _ hS (x _ (epsV v)) = xB _ (epsV ((lin Q).map (algebraMap R K) *ᵥ v)) := fun v => by
      rw [hq _ hS _ (epsV_nil v), nv_epsV Q hQ]
    have hi' : ∀ (χ : Multiplicative X →* (DualNumber K)ˣ) t, (∀ j,
        (χ (Multiplicative.ofAdd (β j)) : DualNumber K) = 1 + epsV t j) →
        E.i _ hS χ = x _ (epsV ((lin J).map (algebraMap R K) *ᵥ t)) := fun χ t h => by
      rw [hi _ hS χ _ (epsV_nil t) h, nv_epsV J hJ]
    let ρ : DualNumber K →ₐ[R] K := TrivSqZeroExt.fstHom R K K
    let σ : K →ₐ[R] DualNumber K := TrivSqZeroExt.inlAlgHom R K K
    have hρσ : ρ.comp σ = AlgHom.id R K := by ext; rfl
    have hker : RingHom.ker ρ ^ 2 = ⊥ := by
      rw [pow_two, eq_bot_iff, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']
    have hred : ∀ {n : ℕ} (v : Fin n → K), (fun i => ρ (epsV v i)) = 0 := fun v => rfl
    refine splitEx_of_exact _ _ ?_ (fun w => ?_) (fun v hv => ?_) (fun t ht => ?_)
    · refine Matrix.ext_of_mulVec_single fun j => ?_
      obtain ⟨χ, hχ⟩ := exists_char β (Pi.single j (1 : K))
      have h1 := (E.exact _ hS _).2 ⟨χ, rfl⟩
      rw [hi' χ _ hχ, hq', ← hxB.zero, ← epsV_zero] at h1
      have h2 := epsV_inj (hxB.inj _ _ _ (epsV_nil _) (epsV_nil _) h1)
      rw [← Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec]
    · obtain ⟨z, hz, hz'⟩ := E.lift _ hS K ρ σ hρσ hker (xB _ (epsV w))
        (by rw [hxB.nat _ _ _ _ (epsV_nil w), hred, hxB.zero])
      obtain ⟨a, ha, rfl⟩ := hx.surj _ K ρ σ hρσ ⟨2, hker⟩ z hz
      rw [eq_epsV a ha, hq'] at hz'
      exact ⟨_, epsV_inj (hxB.inj _ _ _ (epsV_nil _) (epsV_nil _) hz')⟩
    · have h1 := hq' v
      rw [hv, epsV_zero, hxB.zero] at h1
      obtain ⟨χ, hχ⟩ := (E.exact _ hS _).1 h1
      have h2 := E.i_nat _ K ρ hS ⟨k, hK⟩ χ
      rw [hχ, hx.nat _ _ _ _ (epsV_nil v), hred, hx.zero, ← map_one (E.i K ⟨k, hK⟩)] at h2
      have h3 := E.i_inj _ _ h2
      have h4 : ∀ j, ((χ (Multiplicative.ofAdd (β j)) : DualNumber K) - 1).fst = 0 := fun j => by
        have := congrArg Units.val (DFunLike.congr_fun h3 (Multiplicative.ofAdd (β j)))
        rw [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one, sub_eq_zero]
        exact this
      have h5 := hi' χ _ (fun j => (sub_eq_iff_eq_add'.1 (congrFun (eq_epsV _ h4) j)))
      rw [hχ] at h5
      exact ⟨_, (epsV_inj (hx.inj _ _ _ (epsV_nil _) (epsV_nil _) h5)).symm⟩
    · obtain ⟨χ, hχ⟩ := exists_char β t
      have h1 := hi' χ t hχ
      rw [ht, epsV_zero, hx.zero, ← map_one (E.i _ hS)] at h1
      have h2 := E.i_inj _ _ h1
      apply epsV_inj
      rw [epsV_zero]
      funext j
      have := hχ j
      rw [h2] at this
      simpa using this
  refine splitEx_lift I _ _ ?_ (key (R ⧸ I) 0 fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using ht))
  ext i j
  refine IsHausdorff.haus (inferInstance : IsHausdorff I R) _ fun k => ?_
  have h1 := (key (R ⧸ I ^ (k + 1)) k fun t ht => Ideal.Quotient.eq_zero_iff_mem.2 ht).1
  rw [← Matrix.map_mul] at h1
  have h2 : (lin Q * lin J) i j ∈ I ^ (k + 1) := Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h1 i) j)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ k) h2

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqSplitExactStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPointExtension_tangentSeq_splitExact : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → SplitEx (lin J) (lin Q) := by
  first | exact @GlobalTheory.ChF.tangent_splitEx | exact GlobalTheory.ChF.tangent_splitEx | (intros; apply GlobalTheory.ChF.tangent_splitEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqEquivariant
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private def tv {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (e : S) {n : ℕ} (v : Fin n → R) :
    Fin n → S := fun i => algebraMap R S (v i) * e

private theorem tv_nil {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {e : S} (he : e * e = 0) {n : ℕ}
    (v : Fin n → R) (i : Fin n) : IsNilpotent (tv e v i) :=
  ⟨2, by simp only [tv, mul_pow, pow_two e, he, mul_zero]⟩

private theorem nv_tv {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {e : S} (he : e * e = 0) {n m : ℕ}
    (φ : Fin m → PS R 1 n) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (v : Fin n → R) :
    (fun j => nv (algebraMap R S) (φ j) ![tv e v]) = tv e (lin φ *ᵥ v) := by
  funext j
  have h := (nv_calculus R S (algebraMap R S) 1 n ![tv e v] (fun i k => by
    fin_cases i; exact tv_nil he v k)).2.2.2.2.2 (fun i k i' k' => by
      fin_cases i; fin_cases i'
      show algebraMap R S (v k) * e * (algebraMap R S (v k') * e) = 0
      rw [_root_.mul_mul_mul_comm, he, mul_zero]) (φ j)
  rw [h, hφ, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tv, lin, Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul,
    Matrix.cons_val_fin_one, _root_.mul_assoc]

private theorem mat_ext {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {m n : ℕ}
    (A A' : Matrix (Fin m) (Fin n) R)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S], (∃ k, Kills I k S) → ∀ e : S, e * e = 0 →
      ∀ v : Fin n → R, tv e (A *ᵥ v) = tv e (A' *ᵥ v)) : A = A' := by
  ext i j
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := R)) _ fun k => ?_
  have hk : Kills I k (DualNumber (R ⧸ I ^ (k + 1))) := fun t ht => by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ I ^ (k + 1)), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ht, map_zero]
  have h1 := congrArg TrivSqZeroExt.snd (congrFun (h (DualNumber (R ⧸ I ^ (k + 1))) ⟨k, hk⟩ DualNumber.eps
    DualNumber.eps_mul_eps (Pi.single j 1)) i)
  simp only [tv, Matrix.mulVec_single_one, Matrix.col_apply,
    IsScalarTower.algebraMap_apply R (R ⧸ I ^ (k + 1)) (DualNumber (R ⧸ I ^ (k + 1))),
    ← Algebra.smul_def, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, _root_.mul_one,
    Ideal.Quotient.algebraMap_eq] at h1
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right (Nat.le_succ k) (Ideal.Quotient.eq.1 h1)

private def chi {R S X : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup X] {e : S}
    (he : e * e = 0) (L : X →+ R) : Multiplicative X →* Sˣ :=
  MonoidHom.toHomUnits
    { toFun := fun y => 1 + algebraMap R S (L y.toAdd) * e
      map_one' := by simp
      map_mul' := fun y z => by
        simp only [toAdd_mul, map_add (f := _)]
        linear_combination (-(algebraMap R S (L y.toAdd) * algebraMap R S (L z.toAdd))) * he }

theorem lin_tangentSeq_equivariant : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → ∀ (f : G ⟶ G) (α : Fin d → PS R 1 d), Reads x x f α → (∀ (fB : B ⟶ B) (αB : Fin g → PS R 1 g), Reads xB xB fB αB → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) z, E.q S h (z ≫ f) = E.q S h z ≫ fB) → lin Q * lin α = lin αB * lin Q) ∧ ∀ hm : X →+ X, (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) χ χ', (∀ y, χ' (Multiplicative.ofAdd y) = χ (Multiplicative.ofAdd (hm y))) → E.i S h χ ≫ f = E.i S h χ') → lin α * lin J = lin J * Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) := by
  intro R _ I _ G _ _ B _ _ X _ E d g F FB x xB hx hxB r β J Q hJ hQ hq hi f α hα
  refine ⟨fun fB αB hαB hc => mat_ext I _ _ fun S _ _ h e he v => ?_,
    fun hm hc => mat_ext I _ _ fun S _ _ h e he v => ?_⟩
  · refine hxB.inj S _ _ (tv_nil he _) (tv_nil he _) ?_
    have h1 := hc S h (x S (tv e v))
    rw [hα.2 S _ (tv_nil he v), nv_tv he α hα.1, hq S h _ (tv_nil he _), hq S h _ (tv_nil he _),
      nv_tv he Q hQ, nv_tv he Q hQ, hαB.2 S _ (tv_nil he _), nv_tv he αB hαB.1] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h1
  · refine hx.inj S _ _ (tv_nil he _) (tv_nil he _) ?_
    let L : X →ₗ[ℤ] R := β.constr ℤ v
    have hL : ∀ j, L (β j) = v j := fun j => β.constr_basis ℤ v j
    have hL' : ∀ j, L (hm (β j)) =
        (Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) *ᵥ v) j := fun j => by
      simp [L, Module.Basis.constr_apply_fintype, Matrix.mulVec, dotProduct]
    have h1 := hc S h (chi he L.toAddMonoidHom) (chi he (L.toAddMonoidHom.comp hm)) (fun y => Units.ext rfl)
    rw [hi S h _ (tv e v) (tv_nil he _) (fun j => by
        show 1 + algebraMap R S (L (β j)) * e = _
        rw [hL]; rfl),
      hi S h _ (tv e (Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) *ᵥ v)) (tv_nil he _) (fun j => by
        show 1 + algebraMap R S (L (hm (β j))) * e = _
        rw [hL']; rfl),
      nv_tv he J hJ, nv_tv he J hJ, hα.2 S _ (tv_nil he _), nv_tv he α hα.1] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h1

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ToricPointExtensionTangentSeqEquivariantStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPointExtension_tangentSeq_equivariant : ∀ (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] (E : PtExt I G B X) (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam B g), NilChart G F.F x → NilChart B FB.F xB → ∀ (r : ℕ) (β : Module.Basis (Fin r) ℤ X) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (J j) = 0) → (∀ j, MvPowerSeries.constantCoeff (Q j) = 0) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (a : Fin d → S), (∀ i, IsNilpotent (a i)) → E.q S h (x S a) = xB S (fun j => nv (algebraMap R S) (Q j) ![a])) → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) (χ : Multiplicative X →* Sˣ) (t : Fin r → S), (∀ i, IsNilpotent (t i)) → (∀ j, (χ (Multiplicative.ofAdd (β j)) : S) = 1 + t j) → E.i S h χ = x S (fun j => nv (algebraMap R S) (J j) ![t])) → ∀ (f : G ⟶ G) (α : Fin d → PS R 1 d), Reads x x f α → (∀ (fB : B ⟶ B) (αB : Fin g → PS R 1 g), Reads xB xB fB αB → (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) z, E.q S h (z ≫ f) = E.q S h z ≫ fB) → lin Q * lin α = lin αB * lin Q) ∧ ∀ hm : X →+ X, (∀ (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S) χ χ', (∀ y, χ' (Multiplicative.ofAdd y) = χ (Multiplicative.ofAdd (hm y))) → E.i S h χ ≫ f = E.i S h χ') → lin α * lin J = lin J * Matrix.of (fun i k => ((β.repr (hm (β i)) k : ℤ) : R)) := by
  first | exact @GlobalTheory.ChF.lin_tangentSeq_equivariant | exact GlobalTheory.ChF.lin_tangentSeq_equivariant | (intros; apply GlobalTheory.ChF.lin_tangentSeq_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private noncomputable def starMat {X : Type} [AddCommGroup X] {r : ℕ} (β : Module.Basis (Fin r) ℤ X)
    (OE : Type) [CommRing OE] [StarRing OE] [Module OE X] : OE →+* Matrix (Fin r) (Fin r) ℤ where
  toFun a := Matrix.of fun i k => β.repr (star a • β i) k
  map_one' := by
    ext i k
    simp [Matrix.one_apply, Finsupp.single_apply]
  map_mul' a b := by
    ext i k
    have h : star (a * b) • β i = ∑ j, β.repr (star a • β i) j • (star b • β j) := by
      rw [star_mul, mul_smul]
      conv_lhs => rw [← β.sum_repr (star a • β i)]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.of_apply, Matrix.mul_apply, h, map_sum, map_zsmul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  map_zero' := by
    ext i k
    simp
  map_add' a b := by
    ext i k
    simp [add_smul]

theorem unif_extSer_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) [IsAdicComplete I R] (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam D.toPre.P.A g), NilChart G F.F x → NilChart D.toPre.P.A FB.F xB → ∃ (r : ℕ) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (α : OE → Fin d → PS R 1 d) (αB : OE → Fin g → PS R 1 g), (∀ a, Reads x x (io.act a) (α a)) → (∀ a, Reads xB xB (oD.onB.act a) (αB a)) → ∃ N : OE →+* Matrix (Fin r) (Fin r) ℤ, ∀ a, lin Q * lin (α a) = lin (αB a) * lin Q ∧ lin (α a) * lin J = lin J * (N a).map (Int.castRingHom R) := by
  intro R _ _ I D A G _ _ U _ d g F FB x xB hx hxB
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_torus_extension_points_of_uniformisation R I D A G U
  let β : Module.Basis (Fin (Module.finrank ℤ D.toPre.X)) ℤ D.toPre.X := Module.finBasis ℤ D.toPre.X
  obtain ⟨Q, hQ, hQ'⟩ := GlobalTheory.T.toricPointExtension_abelianPart_formalGroup_hom R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB
  obtain ⟨J, hJ, hJ'⟩ := GlobalTheory.T.exists_formalGroupSeries_toricPointExtension R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β
  refine ⟨_, J, Q, ⟨hJ, hQ, GlobalTheory.T.toricPointExtension_tangentSeq_splitExact R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β J Q
    hJ.1 hQ.1 hQ' hJ'⟩, ?_⟩
  intro OE _ _ _ io oD oA hO α αB hα hαB
  refine ⟨starMat β OE, fun a => ?_⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.toricPointExtension_tangentSeq_equivariant R I G D.toPre.P.A D.toPre.X E d g F FB x xB hx hxB _ β J Q
    hJ.1 hQ.1 hQ' hJ' (io.act a) (α a) (hα a)
  refine ⟨h1 _ _ (hαB a) (fun S _ _ h => (hE OE io oD oA hO a S h).1), ?_⟩
  exact h2 (DistribSMul.toAddMonoidHom D.toPre.X (star a)) (fun S _ _ h => (hE OE io oD oA hO a S h).2)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariantStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_split_formal_group_law_equivariant : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G) [IsAdicComplete I R] (d g : ℕ) (F : FGLaw R d) (FB : FGLaw R g) (x : Fam G d) (xB : Fam D.toPre.P.A g), NilChart G F.F x → NilChart D.toPre.P.A FB.F xB → ∃ (r : ℕ) (J : Fin d → PS R 1 r) (Q : Fin g → PS R 1 d), ExtSer F.F FB.F J Q ∧ ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (α : OE → Fin d → PS R 1 d) (αB : OE → Fin g → PS R 1 g), (∀ a, Reads x x (io.act a) (α a)) → (∀ a, Reads xB xB (oD.onB.act a) (αB a)) → ∃ N : OE →+* Matrix (Fin r) (Fin r) ℤ, ∀ a, lin Q * lin (α a) = lin (αB a) * lin Q ∧ lin (α a) * lin J = lin J * (N a).map (Int.castRingHom R) := by
  first | exact @GlobalTheory.unif_extSer_equivariant | exact GlobalTheory.unif_extSer_equivariant | (intros; apply GlobalTheory.unif_extSer_equivariant <;> assumption)
end
