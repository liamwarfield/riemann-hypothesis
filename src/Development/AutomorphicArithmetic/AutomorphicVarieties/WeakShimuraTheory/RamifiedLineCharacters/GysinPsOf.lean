module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CoefFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.OpenKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ContResQ

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupRaw
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ExtRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def actM {A V J : Type} [CommRing A] [AddCommGroup V] [Module A V] (r t : A) (Y : J → V) :
    A × (J → V) →+ A × (J → V) where
  toFun u := (r * u.1, fun j => t • u.2 j + (r * u.1) • Y j)
  map_zero' := by ext <;> simp
  map_add' u v := by
    ext
    · simp [mul_add]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, smul_add, add_smul]
      abel

private def mkRep {Γ M : Type} [Group Γ] [AddCommGroup M] (n : ℕ) [Module (ZMod n) M] (T : Γ → M →+ M) (h1 : ∀ u, T 1 u = u)
    (hm : ∀ g h u, T (g * h) u = T g (T h u)) : Representation (ZMod n) Γ M where
  toFun g := ((T g).toZModLinearMap n : Module.End (ZMod n) M)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hm g h)

private theorem continuous_of_right_invariant_on_nhds_one {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (U : Set Γ) (hU : U ∈ nhds (1 : Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ U, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_const_mul g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht hU] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem UpperTheory.V.Ws.Gys.extRep :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → (∀ i, IsLocallyConstant fun g => a (Φ.χ i g)) → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod (l ^ 1)) M) (_ : Finite M) (_ : TopologicalSpace M) (_ : DiscreteTopology M) (ρ : Representation (ZMod (l ^ 1)) Γ M)
        (p : M →+ k) (q : J → M →+ k) (m0 : M), ContAction ρ ∧ (∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ρ g = 1) ∧
        (∀ g u, p (ρ g u) = a (Φ.rt w g) * p u) ∧ (∀ j g u, q j (ρ g u) = a (Φ.rt (w + w') g) * q j u + y j g * a (Φ.rt w g) * p u) ∧
        m0 ≠ 0 ∧ ∀ u ∈ Submodule.span (ZMod (l ^ 1)) {m0}, u ≠ 0 → p u ≠ 0 := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ ha hχ w w' J _ y hy
  classical
  have hlp : (l ^ 1 : ℕ) = l := pow_one l
  have hA : ∀ (v : ℤ × ℤ) g, a ↑(Φ.rt v g) =
      (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹) ^ v.1 * (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹) ^ v.2 := by
    intro v g
    have e : ∀ u : Oˣ, a ↑u = ((Units.map a.toMonoidHom u : kˣ) : k) := fun u => rfl
    rw [e, e, e, e]
    simp only [Fr.rt, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_zpow, map_inv, Units.val_mul,
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
  have hsplit : ∀ g, a ↑(Φ.rt (w + w') g) = a ↑(Φ.rt w g) * a ↑(Φ.rt w' g) := by
    intro g
    rw [hA, hA, hA]
    simp only [Prod.fst_add, Prod.snd_add]
    have h0 : a ↑(Φ.χ 0 g) ≠ 0 := ((Φ.χ 0 g).isUnit.map a).ne_zero
    have h1 : a ↑(Φ.χ 1 g) ≠ 0 := ((Φ.χ 1 g).isUnit.map a).ne_zero
    have h2 : a ↑(Φ.χ 2 g) ≠ 0 := ((Φ.χ 2 g).isUnit.map a).ne_zero
    have n1 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero h1)
    have n2 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero h2)
    rw [zpow_add₀ n1, zpow_add₀ n2]
    ring
  have hy1 : ∀ j, y j 1 = 0 := by
    intro j
    have := (hy j).coc 1 1
    simp only [mul_one, map_one, Units.val_one] at this
    linear_combination -this
  have hY : (⋃ j, Set.range (y j)).Finite := Set.finite_iUnion fun j => (hy j).lc.range_finite
  let A : Subring k := a.range
  haveI : Finite A := Set.Finite.to_subtype (s := (a.range : Set k)) (by rw [RingHom.coe_range]; exact ha)
  let V : Submodule A k := Submodule.span A (⋃ j, Set.range (y j))
  haveI : Module.Finite A V := Module.Finite.span_of_finite A hY
  haveI : Finite V := Module.finite_of_finite A
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hchar : ∀ x : k, (l ^ 1) • x = 0 := by
    intro x
    rw [nsmul_eq_mul, hlp, CharP.cast_eq_zero, zero_mul]
  letI iM : Module (ZMod (l ^ 1)) (A × (J → V)) := AddCommGroup.zmodModule (fun x => by
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      change (((l ^ 1) • x.1 : A) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hchar _
    · funext j
      apply Subtype.ext
      change (((l ^ 1) • x.2 j : V) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hchar _)
  letI : TopologicalSpace (A × (J → V)) := ⊥
  haveI : DiscreteTopology (A × (J → V)) := ⟨rfl⟩
  let rr : Γ → A := fun g => ⟨a ↑(Φ.rt w g), a.mem_range_self _⟩
  let tt : Γ → A := fun g => ⟨a ↑(Φ.rt (w + w') g), a.mem_range_self _⟩
  let YY : Γ → J → V := fun g j => ⟨y j g, Submodule.subset_span (Set.mem_iUnion.2 ⟨j, g, rfl⟩)⟩
  let T : Γ → (A × (J → V)) →+ (A × (J → V)) := fun g => actM (rr g) (tt g) (YY g)
  have cs : ∀ (c : A) (v : V), ((c • v : V) : k) = (c : k) * (v : k) := fun c v => rfl
  have h1 : ∀ u, T 1 u = u := by
    intro u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w 1) * (u.1 : k) = u.1
      simp
    · funext j
      apply Subtype.ext
      show ((tt 1 • u.2 j + (rr 1 * u.1) • YY 1 j : V) : k) = u.2 j
      rw [Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') 1) * (u.2 j : k) + (a ↑(Φ.rt w 1) * (u.1 : k)) * y j 1 = u.2 j
      simp [hy1]
  have hm : ∀ g h u, T (g * h) u = T g (T h u) := by
    intro g h u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w (g * h)) * (u.1 : k) = a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))
      rw [map_mul, Units.val_mul, map_mul, mul_assoc]
    · funext j
      apply Subtype.ext
      show ((tt (g * h) • u.2 j + (rr (g * h) * u.1) • YY (g * h) j : V) : k) =
        ((tt g • (tt h • u.2 j + (rr h * u.1) • YY h j) + (rr g * (rr h * u.1)) • YY g j : V) : k)
      rw [Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') (g * h)) * (u.2 j : k) + (a ↑(Φ.rt w (g * h)) * (u.1 : k)) * y j (g * h) =
        a ↑(Φ.rt (w + w') g) * (a ↑(Φ.rt (w + w') h) * (u.2 j : k) + (a ↑(Φ.rt w h) * (u.1 : k)) * y j h) +
          (a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))) * y j g
      rw [(hy j).coc g h, map_mul (Φ.rt (w + w')), map_mul (Φ.rt w), Units.val_mul, Units.val_mul,
        map_mul a, map_mul a, hsplit g, hsplit h]
      ring
  let ρ : Representation (ZMod (l ^ 1)) Γ (A × (J → V)) := mkRep (l ^ 1) T h1 hm
  have hker : ∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ∀ u, T g u = u := by
    intro g hg hyg
    have hr : ∀ v : ℤ × ℤ, a ↑(Φ.rt v g) = 1 := by
      intro v
      rw [hA, hg 0, hg 1, hg 2]
      simp
    intro u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w g) * (u.1 : k) = u.1
      rw [hr, one_mul]
    · funext j
      apply Subtype.ext
      show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = u.2 j
      rw [Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g = u.2 j
      rw [hr, hr, hyg]
      ring
  let p : (A × (J → V)) →+ k :=
    { toFun := fun u => (u.1 : k), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : J → (A × (J → V)) →+ k := fun j =>
    { toFun := fun u => (u.2 j : k), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let m0 : A × (J → V) := (1, 0)
  refine ⟨A × (J → V), inferInstance, iM, inferInstance, ⊥, ⟨rfl⟩, ρ, p, q, m0, ?_, fun g hg hyg => LinearMap.ext (hker g hg hyg), ?_, ?_, ?_, ?_⟩
  · unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro m
    let U : Set Γ := (⋂ i, (fun g => a (Φ.χ i g)) ⁻¹' {1}) ∩ ⋂ j, y j ⁻¹' {0}
    have hU : U ∈ nhds (1 : Γ) := by
      apply IsOpen.mem_nhds
      · exact (isOpen_iInter_of_finite fun i => (hχ i).isOpen_fiber 1).inter
          (isOpen_iInter_of_finite fun j => (hy j).lc.isOpen_fiber 0)
      · refine ⟨Set.mem_iInter.2 fun i => ?_, Set.mem_iInter.2 fun j => ?_⟩
        · simp
        · exact hy1 j
    apply continuous_of_right_invariant_on_nhds_one U hU
    intro g h hh
    have hh1 : ∀ i, a (Φ.χ i h) = 1 := fun i => Set.mem_iInter.1 hh.1 i
    have hh2 : ∀ j, y j h = 0 := fun j => Set.mem_iInter.1 hh.2 j
    show T (g * h) m = T g m
    rw [hm, hker h hh1 hh2 m]
  · intro g u
    rfl
  · intro j g u
    show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = _
    rw [Submodule.coe_add, cs, cs]
    show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g =
      a ↑(Φ.rt (w + w') g) * (u.2 j : k) + y j g * a ↑(Φ.rt w g) * (u.1 : k)
    ring
  · intro h
    have := congrArg (fun u : A × (J → V) => (u.1 : k)) h
    simp [m0] at this
  · intro u hu hne
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul] at hne ⊢
    intro hp
    apply hne
    rw [map_nsmul] at hp
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      change ((c.val • (1 : A) : A) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hp
    · funext j
      apply Subtype.ext
      change ((c.val • (0 : V) : V) : k) = 0
      rw [smul_zero]
      rfl
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupRaw :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → Φ.Ok a → ∀ 𝒩 : Set Γ → Prop, Φ.Gys l 𝒩 → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ N', 𝒩 N' ∧ ∃ (x : Γ → k) (m : Φ.ι → k), (Φ.wN N').Coc a w x ∧ Φ.LocTriv a w x m ∧ (∃ g, a (Φ.rt w g) = 1 ∧ x g ≠ 0) ∧
        ∀ j, ∃ z, (Φ.wN N').Cup a w w' x (y j) z m := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ hfin hok 𝒩 hG w w' J _ y hy
  obtain ⟨M, i1, i2, i3, i4, i5, ρ, p, q, m0, hc, hN, hp, hq, hm0, hpm⟩ :=
    Gys.extRep Φ a l hfin hok.lc w w' J y hy
  obtain ⟨N', hN', c, hcZ, hc0, hloc, g, hg1, hcg, hspan⟩ :=
    hG M ρ hc (fun g hg => hN g (hok.kill g hg) (fun j => (hy j).kill g hg)) m0 hm0
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle ρ c).1 hcZ
  have hlc : IsLocallyConstant c := (IsLocallyConstant.iff_continuous c).2 hcont
  have hrt : ∀ u, (Φ.wN N').rt u = Φ.rt u := fun u => rfl
  choose mm hmm using hloc
  have hpg : p (c g) ≠ 0 := hpm _ hspan hcg
  refine ⟨N', hN', fun s => p (c s), fun v => -p (mm v), ?_, ?_, ?_, ?_⟩
  · refine ⟨hlc.comp p, ?_, ?_⟩
    · intro s t
      rw [hrt, hcoc, map_add (f := _), hp]
    · intro s hs
      simp [hc0 s hs]
  · intro v s hs
    show p (c s) = -p (mm v) - a ↑((Φ.rt w) s) * -p (mm v)
    rw [hmm v s hs, map_sub, hp]
    ring
  · refine ⟨g, ?_, hpg⟩
    have h := hp g (c g)
    rw [hg1] at h
    change p (c g) = _ at h
    have h2 : (a ↑((Φ.rt w) g) - 1) * p (c g) = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hpg
  · intro j
    refine ⟨fun s => q j (c s), hlc.comp (q j), ?_, ?_, ?_⟩
    · intro s t
      simp only [hrt]
      rw [hcoc, map_add (f := _), hq]
      ring
    · intro s hs
      simp [hc0 s hs]
    · intro v
      refine ⟨-q j (mm v), fun s hs => ?_⟩
      simp only [hrt]
      rw [hmm v s hs, map_sub, hq]
      ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.DataAl
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.dataAl :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nM p.r →
      ∃ x : Γ → R, Φ.Coc a (-wAl) x ∧ x Φ.g0 = 0 ∧ Φ.LocTriv a (-wAl) x (fun v => p.n v 1 0) ∧ ∀ g, p.r g 1 0 = x g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hp hs
  have h12 : ∀ g, p.r g 1 2 = 0 := fun g => hs g 1 2 (by decide) (by decide)
  have h13 : ∀ g, p.r g 1 3 = 0 := fun g => hs g 1 3 (by decide) (by decide)
  have hd := hp.res.diag
  have hu : ∀ g, a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) * a (Φ.χ 0 g) = 1 := fun g => by
    rw [← map_mul, Units.inv_mul, map_one]
  have hrt : ∀ g, a (Φ.rt (-wAl) g) = a (Φ.χ 1 g) * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O) := fun g => by
    rw [← map_mul, ← Units.val_mul]
    congr 2
    simp [Fr.rt, wAl]
  have hlc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => by
    refine IsLocallyConstant.desc _ (Ideal.Quotient.mk ((⊥ : Ideal R) ^ 1)) (hp.cont i j 1) ?_
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, pow_one]
  refine ⟨fun g => p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · refine (hlc 1 0).mul ?_
    have e : (fun g => a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) = Ring.inverse ∘ fun g => p.r g 0 0 := by
      funext g
      simp only [Function.comp, hd]
      exact (Ring.inverse_unit (Units.map (a : O →* R) (Φ.χ 0 g))).symm
    rw [e]
    exact (hlc 0 0).comp _
  · intro g h
    have e : p.r (g * h) 1 0 = p.r g 1 0 * a (Φ.χ 0 h) + a (Φ.χ 1 g) * p.r h 1 0 := by
      rw [map_mul, Matrix.mul_apply, Fin.sum_univ_four, h12, h13, hd, hd]; ring
    rw [e, hrt, map_mul, mul_inv, Units.val_mul, map_mul]
    linear_combination (p.r g 1 0 * a (((Φ.χ 0 g)⁻¹ : Oˣ) : O)) * hu h
  · intro g hg
    simp [hp.pair.kill g hg]
  · have : p.r Φ.g0 1 0 = 0 := hp.pair.nrm (by decide)
    simp [this]
  · intro v s hsv
    obtain ⟨l1, l2, l3⟩ := hp.pair.low v
    have hinv : p.n v * adj (p.n v) = 1 := by
      rw [IsGSp, one_smul] at l1
      exact mul_eq_one_comm.mp l1
    have hU := hp.pair.flag v s hsv
    have hc := hp.res.char v s hsv 0
    unfold PD.ψ at hc
    have key : p.n v * (adj (p.n v) * p.r s * p.n v) = p.r s * p.n v := by
      rw [← mul_assoc, ← mul_assoc, hinv, one_mul]
    generalize adj (p.n v) * p.r s * p.n v = U at hU hc key
    have k := congrFun (congrFun key 1) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four, hU 1 0 (by decide), hU 2 0 (by decide),
      hU 3 0 (by decide), hc, h12, h13, hd, l2, l2] at k
    rw [hrt]
    beta_reduce
    linear_combination (-a (((Φ.χ 0 s)⁻¹ : Oˣ) : O)) * k + p.n v 1 0 * hu s
  · intro g
    beta_reduce
    rw [mul_assoc, hu, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupNorm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem rt_val {O Γ k : Type} [CommRing O] [Group Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (w : ℤ × ℤ) (g : Γ) :
    a (Φ.rt w g) = (a (Φ.χ 0 g) * (a (Φ.χ 1 g))⁻¹) ^ w.1 * (a (Φ.χ 0 g) * (a (Φ.χ 2 g))⁻¹) ^ w.2 := by
  have h : ∀ u : Oˣ, a (u : O) = ((Units.map (a : O →* k) u : kˣ) : k) := fun _ => rfl
  have e : Φ.rt w g = (Φ.χ 0 g * (Φ.χ 1 g)⁻¹) ^ w.1 * (Φ.χ 0 g * (Φ.χ 2 g)⁻¹) ^ w.2 := rfl
  rw [e, h, h (Φ.χ 0 g), h (Φ.χ 1 g), h (Φ.χ 2 g)]
  simp only [map_mul, map_zpow, map_inv, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]

private theorem rt_lc {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k)
    (h : Φ.Ok a) (w : ℤ × ℤ) : IsLocallyConstant fun g => a (Φ.rt w g) := by
  simp only [rt_val]
  exact (((h.lc 0).mul ((h.lc 1).comp (·⁻¹))).comp (· ^ w.1)).mul (((h.lc 0).mul ((h.lc 2).comp (·⁻¹))).comp (· ^ w.2))

private theorem rt_kill {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k)
    (h : Φ.Ok a) (w : ℤ × ℤ) (g : Γ) (hg : g ∈ Φ.N) : a (Φ.rt w g) = 1 := by
  simp [rt_val, h.kill g hg]

theorem UpperTheory.V.Ws.Gys.cupNorm :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k), Φ.Ok a → ∀ (w w' : ℤ × ℤ), a (Φ.rt w Φ.g0) ≠ 1 → a (Φ.rt (w + w') Φ.g0) ≠ 1 → ∀ (J : Type) (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j) ∧ y j Φ.g0 = 0) →
      ∀ (x : Γ → k) (m : Φ.ι → k), Φ.Coc a w x → Φ.LocTriv a w x m → (∀ j, ∃ z, Φ.Cup a w w' x (y j) z m) →
        ∃ (x' : Γ → k) (m' : Φ.ι → k), Φ.Coc a w x' ∧ x' Φ.g0 = 0 ∧ Φ.LocTriv a w x' m' ∧ (∀ g, a (Φ.rt w g) = 1 → x' g = x g) ∧
          ∀ j, ∃ z, Φ.Cup a w w' x' (y j) z m' ∧ z Φ.g0 = 0 := by
  intro O Γ k _ _ _ _ Φ a hok w w' h1 h2 J y hy x m hx hm hz
  have n1 : 1 - a (Φ.rt w Φ.g0) ≠ 0 := sub_ne_zero.2 h1.symm
  have n2 : 1 - a (Φ.rt (w + w') Φ.g0) ≠ 0 := sub_ne_zero.2 h2.symm
  have hmul : ∀ (u : ℤ × ℤ) (g h : Γ), a (Φ.rt u (g * h)) = a (Φ.rt u g) * a (Φ.rt u h) := fun u g h => by
    rw [map_mul, Units.val_mul, map_mul]
  have hadd : ∀ g : Γ, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  obtain ⟨m1, hm1⟩ : ∃ m1 : k, x Φ.g0 = m1 - a (Φ.rt w Φ.g0) * m1 :=
    ⟨x Φ.g0 / (1 - a (Φ.rt w Φ.g0)), by field_simp⟩
  have c := fun t : k => (IsLocallyConstant.const t : IsLocallyConstant fun _ : Γ => t)
  refine ⟨fun g => x g - (m1 - a (Φ.rt w g) * m1), fun v => m v - m1, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, fun j => ?_⟩
  · exact hx.lc.sub ((c m1).sub ((rt_lc Φ a hok w).mul (c m1)))
  · intro g h
    rw [hx.coc, hmul]; ring
  · intro g hg
    rw [hx.kill g hg, rt_kill Φ a hok w g hg]; ring
  · exact sub_eq_zero.2 hm1
  · intro v s hs
    beta_reduce
    rw [hm v s hs]; ring
  · intro g hg
    beta_reduce
    rw [hg]; ring
  · obtain ⟨z, hz⟩ := hz j
    obtain ⟨hyj, hy0⟩ := hy j
    obtain ⟨o1, ho1⟩ : ∃ o1 : k, z Φ.g0 = o1 - a (Φ.rt (w + w') Φ.g0) * o1 :=
      ⟨z Φ.g0 / (1 - a (Φ.rt (w + w') Φ.g0)), by field_simp⟩
    refine ⟨fun g => z g - (o1 - a (Φ.rt (w + w') g) * o1 - y j g * a (Φ.rt w g) * m1), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hz.lc.sub (((c o1).sub ((rt_lc Φ a hok _).mul (c o1))).sub ((hyj.lc.mul (rt_lc Φ a hok w)).mul (c m1)))
    · intro g h
      rw [hz.coc, hyj.coc, hmul, hmul, hadd g, hadd h]; ring
    · intro g hg
      rw [hz.kill g hg, hyj.kill g hg, rt_kill Φ a hok _ g hg]; ring
    · intro v
      obtain ⟨o, ho⟩ := hz.loc v
      refine ⟨o - o1, fun s hs => ?_⟩
      rw [ho s hs]; ring
    · beta_reduce
      rw [ho1, hy0]; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SuppMMono
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Gys

section

variable {R : Type} [CommRing R]

private theorem gsp_uD (d : Fin 4 → R) (ν : R) (h : ∀ i, d i * d i.rev = ν) (x y t : R) :
    IsGSp ν (uQ x y t * Matrix.diagonal d) := by
  have h0 : d 0 * d 3 = ν := h 0
  have h1 : d 1 * d 2 = ν := h 1
  have hM : uQ x y t * Matrix.diagonal d =
      !![d 0, 0, 0, 0; x * d 0, d 1, 0, 0; y * d 0, 0, d 2, 0; t * d 0, y * d 1, -x * d 2, d 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uQ, Matrix.mul_diagonal]
  unfold IsGSp
  rw [hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj, sgn, Matrix.mul_apply, Fin.sum_univ_four, Fin.rev] <;>
    first | exact h0 | exact h1 | ring1 | linear_combination h0 | linear_combination h1

private theorem suppM_mul {S : Finset (ℤ × ℤ)} {X : M4 R} (h : SuppM S X) (d : Fin 4 → R) :
    SuppM S (X * Matrix.diagonal d) := by
  intro i j hij hw
  simp [Matrix.mul_diagonal, h i j hij hw]

private theorem suppM_mono {S S' : Finset (ℤ × ℤ)} (hS : S ⊆ S') {X : M4 R} (h : SuppM S X) : SuppM S' X :=
  fun i j h1 h2 => h i j h1 fun h3 => h2 (hS h3)

end

section

variable {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)

private theorem chi1 (g : Γ) : a (Φ.χ 1 g) = a (Φ.rt (-wAl) g) * a (Φ.χ 0 g) := by
  simp only [Fr.rt, wAl, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg, zpow_one, zpow_zero, mul_one, mul_inv_rev, inv_inv]
  rw [← map_mul]
  congr 1
  simp [Units.ext_iff]

private theorem chi2 (g : Γ) : a (Φ.χ 2 g) = a (Φ.rt (-wPs) g) * a (Φ.χ 0 g) := by
  simp only [Fr.rt, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg, zpow_one, zpow_zero, one_mul, mul_inv_rev, inv_inv]
  rw [← map_mul]
  congr 1
  simp [Units.ext_iff]

private theorem chi3 (h : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (g : Γ) :
    a (Φ.χ 3 g) = a (Φ.rt (-wAl) g) * a (Φ.rt (-wPs) g) * a (Φ.χ 0 g) := by
  have h0 : Φ.χ 0 g * Φ.χ 3 g = Φ.ν g := h 0 g
  have h1 : Φ.χ 1 g * Φ.χ 2 g = Φ.ν g := h 1 g
  have key : Φ.χ 3 g = Φ.rt (-wAl) g * Φ.rt (-wPs) g * Φ.χ 0 g := by
    simp only [Fr.rt, wAl, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero,
      zpow_neg, zpow_one, zpow_zero, mul_one, one_mul]
    rw [eq_inv_mul_of_mul_eq h0, ← h1]
    simp only [mul_inv_rev, inv_inv]
    simp only [mul_assoc]
    rw [inv_mul_cancel, mul_one, mul_left_comm]
  rw [key]
  simp

end

end UpperTheory.V.Ws.Gys

private theorem exists_hom_M4_eq_uQ_mul_diagonal_of_cup {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R]
    (Φ : Fr O Γ) (a : O →+* R) (hΦ : Φ.Ok a) (x y z : Γ → R) (m : Φ.ι → R)
    (hx : Φ.Coc a (-wAl) x) (hy : Φ.Coc a (-wPs) y) (hz : Φ.Cup a (-wAl) (-wPs) x y z m) :
    ∃ r : Γ →* M4 R, ∀ g, r g =
      uQ (x g) (y g) (2 * z g - x g * y g) * Matrix.diagonal (fun i => a ↑(Φ.χ i g)) := by
  have x1 : x 1 = 0 := by
    have h := hx.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h
  have y1 : y 1 = 0 := by
    have h := hy.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h
  have z1 : z 1 = 0 := by
    have h := hz.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h - y 1 * x1
  refine ⟨{ toFun := fun g => uQ (x g) (y g) (2 * z g - x g * y g) * Matrix.diagonal (fun i => a ↑(Φ.χ i g)),
            map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · simp [x1, y1, z1, uQ_zero]
  · intro g h
    rw [mul_assoc, ← mul_assoc (Matrix.diagonal _),
      diag_mul_uQ (fun i => a ↑(Φ.χ i g)) _ _ (UpperTheory.V.Ws.Gys.chi1 Φ a g) (UpperTheory.V.Ws.Gys.chi2 Φ a g)
        (UpperTheory.V.Ws.Gys.chi3 Φ a hΦ.mul g),
      mul_assoc (uQ _ _ _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal, ← mul_assoc, uQ_mul]
    rw [hx.coc, hy.coc, hz.coc, Fr.rt_add, Units.val_mul, map_mul]
    congr 1
    · congr 1 <;> ring
    · congr 1
      funext i
      simp [map_mul]

private theorem adj_uQ_eq_uQ_neg {R : Type} [CommRing R] (p q u : R) : adj (uQ p q u) = uQ (-p) (-q) (-u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, uQ, sgn, Fin.rev]

private theorem adj_uQ_conj_uQ_mul_diagonal_eq_diagonal {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)
    (hmul : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (s : Γ) (x y z p q u : R)
    (hx : x = p - a ↑(Φ.rt (-wAl) s) * p) (hy : y = q - a ↑(Φ.rt (-wPs) s) * q)
    (hz : z = u - a ↑(Φ.rt (-wAl + -wPs) s) * u - y * a ↑(Φ.rt (-wAl) s) * p) :
    adj (uQ p q (2 * u - p * q)) * (uQ x y (2 * z - x * y) * Matrix.diagonal (fun i => a ↑(Φ.χ i s))) *
      uQ p q (2 * u - p * q) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
  rw [adj_uQ_eq_uQ_neg, mul_assoc, mul_assoc,
    diag_mul_uQ (fun i => a ↑(Φ.χ i s)) _ _ (UpperTheory.V.Ws.Gys.chi1 Φ a s) (UpperTheory.V.Ws.Gys.chi2 Φ a s)
      (UpperTheory.V.Ws.Gys.chi3 Φ a hmul s),
    ← mul_assoc, ← mul_assoc, uQ_mul, uQ_mul]
  rw [Fr.rt_add, Units.val_mul, map_mul] at hz
  subst hz
  subst hx
  subst hy
  have e : ∀ A B C : R, A = 0 → B = 0 → C = 0 →
      uQ A B C * Matrix.diagonal (fun i => a ↑(Φ.χ i s)) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
    intro A B C hA hB hC
    rw [hA, hB, hC, uQ_zero, one_mul]
  apply e <;> ring

theorem UpperTheory.V.Ws.Gys.ob :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R), Φ.Ok a → (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v ∧ ∀ i, a (Φ.χ i s) = 1) → ∀ (x y z : Γ → R) (m n : Φ.ι → R),
      Φ.Coc a (-wAl) x → x Φ.g0 = 0 → Φ.LocTriv a (-wAl) x m → Φ.Coc a (-wPs) y → y Φ.g0 = 0 → Φ.LocTriv a (-wPs) y n →
      Φ.Cup a (-wAl) (-wPs) x y z m → z Φ.g0 = 0 →
        ∃ s : PD Φ.ι Γ R, Φ.IsRes a s ∧ s.In qQ ∧ (∀ g, s.r g 1 0 = x g * a (Φ.χ 0 g)) ∧ (∀ v, s.n v 1 0 = m v) ∧
          (∀ g, s.r g 2 0 = y g * a (Φ.χ 0 g)) ∧ ∀ v, s.n v 2 0 = n v := by
  intro O Γ R _ _ _ _ Φ a hΦ hMu x y z m n hx hx0 hxl hy hy0 hyl hz hz0
  choose o ho using hz.loc
  obtain ⟨r, hr⟩ := exists_hom_M4_eq_uQ_mul_diagonal_of_cup Φ a hΦ x y z m hx hy hz
  have hconj : ∀ v, ∀ s ∈ Φ.Gv v, adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s *
      uQ (m v) (n v) (2 * o v - m v * n v) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
    intro v s hs
    rw [hr]
    exact adj_uQ_conj_uQ_mul_diagonal_eq_diagonal Φ a hΦ.mul s _ _ _ _ _ _ (hxl v s hs) (hyl v s hs) (ho v s hs)
  have hlc : ∀ i j, IsLocallyConstant fun g => r g i j := by
    intro i j
    simp only [hr, Matrix.mul_diagonal]
    apply IsLocallyConstant.mul
    · fin_cases i <;> fin_cases j <;> simp [uQ] <;>
        first
        | exact IsLocallyConstant.const _
        | exact hx.lc
        | exact hy.lc
        | exact hx.lc.neg
        | exact ((IsLocallyConstant.const 2).mul hz.lc).sub (hx.lc.mul hy.lc)
    · exact hΦ.lc j
  refine ⟨⟨r, fun v => uQ (m v) (n v) (2 * o v - m v * n v)⟩,
    ⟨⟨?mult, ?kill, ?nrm, ?low, ?flag, ?mu⟩, ⟨?diag, ?char, ?shape⟩, ?cont⟩, ?inn, ?e1, ?e2, ?e3, ?e4⟩
  case mult =>
    intro g
    dsimp only
    rw [hr]
    apply UpperTheory.V.Ws.Gys.gsp_uD
    intro i
    show a ↑(Φ.χ i g) * a ↑(Φ.χ i.rev g) = a ↑(Φ.ν g)
    rw [← map_mul, ← Units.val_mul, hΦ.mul]
  case kill =>
    intro g hg
    dsimp only
    rw [hr, hx.kill g hg, hy.kill g hg, hz.kill g hg]
    simp [hΦ.kill g hg, uQ_zero]
  case nrm =>
    dsimp only
    rw [hr, hx0, hy0, hz0]
    simpa [uQ_zero] using Matrix.isDiag_diagonal (fun i => a ↑(Φ.χ i Φ.g0))
  case low =>
    intro v
    exact isLow_uQ _ _ _
  case flag =>
    intro v s hs
    dsimp only
    rw [hconj v s hs]
    intro i j hij
    exact Matrix.diagonal_apply_ne _ hij.ne'
  case mu =>
    intro v s hs i
    obtain ⟨hg, h1⟩ := hMu v s hs
    show (adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s * uQ (m v) (n v) (2 * o v - m v * n v)) i i = 1
    rw [hconj v s hg]
    simp [h1 i]
  case diag =>
    intro g i
    dsimp only
    rw [hr]
    fin_cases i <;> simp [uQ, Matrix.mul_diagonal]
  case char =>
    intro v s hs i
    show (adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s * uQ (m v) (n v) (2 * o v - m v * n v)) i i = _
    rw [hconj v s hs]
    simp
  case shape =>
    left
    constructor
    · intro g
      show SuppM nP (r g)
      rw [hr]
      exact UpperTheory.V.Ws.Gys.suppM_mono (by decide)
        (UpperTheory.V.Ws.Gys.suppM_mul (suppM_uQ _ _ _) _)
    · intro v
      exact suppM_uQ _ _ _
  case cont =>
    intro i j N
    exact (hlc i j).comp _
  case inn =>
    constructor
    · intro g
      show SuppM qQ (r g)
      rw [hr]
      exact UpperTheory.V.Ws.Gys.suppM_mul (suppM_uQ _ _ _) _
    · intro v
      exact suppM_uQ _ _ _
  case e1 =>
    intro g
    show r g 1 0 = _
    rw [hr]
    simp [uQ, Matrix.mul_diagonal]
  case e2 =>
    intro v
    simp [uQ]
  case e3 =>
    intro g
    show r g 2 0 = _
    rw [hr]
    simp [uQ, Matrix.mul_diagonal]
  case e4 =>
    intro v
    simp [uQ]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.RootCharactersNeOneAtBasepoint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem map_mul_inv_ne_one_of_isUnit_map_sub {O k : Type} [CommRing O] [Field k] (a : O →+* k) (u v : Oˣ)
    (h : IsUnit (a ↑u - a ↑v)) : a ↑(u * v⁻¹) ≠ 1 := by
  intro h1
  have h2 : a ↑(u * v⁻¹) * a ↑v = 1 * a ↑v := by rw [h1]
  rw [Units.val_mul, ← map_mul, mul_assoc, Units.inv_mul, mul_one, one_mul] at h2
  exact h.ne_zero (sub_eq_zero.2 h2)

theorem UpperTheory.V.Ws.Gys.rootCharacters_ne_one_at_basepoint :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k), Φ.Ok a → a (Φ.rt (-wAl) Φ.g0) ≠ 1 ∧ a (Φ.rt (-wPs) Φ.g0) ≠ 1 ∧ a (Φ.rt (-wAl + -wPs) Φ.g0) ≠ 1 := by
  intro O Γ k _ _ _ _ Φ a hΦ
  have e1 : Φ.rt (-wAl) Φ.g0 = Φ.χ 1 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    simp [Fr.rt, wAl]
  have e2 : Φ.rt (-wPs) Φ.g0 = Φ.χ 2 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    simp [Fr.rt, wPs]
  have hm : Φ.χ 1 Φ.g0 * Φ.χ 2 Φ.g0 = Φ.χ 0 Φ.g0 * Φ.χ 3 Φ.g0 := by
    have h1 := hΦ.mul 1 Φ.g0
    have h0 := hΦ.mul 0 Φ.g0
    have r1 : Fin.rev (1 : Fin 4) = 2 := by decide
    have r0 : Fin.rev (0 : Fin 4) = 3 := by decide
    rw [r1] at h1
    rw [r0] at h0
    rw [h1, h0]
  have e3 : Φ.rt (-wAl + -wPs) Φ.g0 = Φ.χ 3 Φ.g0 * (Φ.χ 0 Φ.g0)⁻¹ := by
    rw [Fr.rt_add, e1, e2, mul_mul_mul_comm, hm, mul_comm (Φ.χ 0 Φ.g0), mul_assoc, mul_inv_cancel_left]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 1 0 (by decide))
  · rw [e2]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 2 0 (by decide))
  · rw [e3]
    exact map_mul_inv_ne_one_of_isUnit_map_sub a _ _ (hΦ.dist 3 0 (by decide))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CupSwap
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupSwap :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (w w' : ℤ × ℤ) (x y z : Γ → R) (m n : Φ.ι → R), Φ.Coc a w x → Φ.LocTriv a w x m → Φ.Coc a w' y → Φ.LocTriv a w' y n →
      Φ.Cup a w w' x y z m → Φ.Cup a w' w y x (x * y - z) n := by
  intro O Γ R _ _ _ _ Φ a w w' x y z m n hx hm hy hn hz
  have e : ∀ g, a (Φ.rt (w + w') g) = a (Φ.rt w g) * a (Φ.rt w' g) := fun g => by
    rw [Fr.rt_add, Units.val_mul, map_mul]
  refine ⟨?_, fun g h => ?_, fun g hg => ?_, fun v => ?_⟩
  · exact (hx.lc.comp₂ hy.lc (· * ·)).comp₂ hz.lc (· - ·)
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, hx.coc, hy.coc, hz.coc, e]
    ring
  · simp only [Pi.sub_apply, Pi.mul_apply]
    rw [hx.kill g hg, hz.kill g hg, zero_mul, sub_zero]
  · obtain ⟨o, ho⟩ := hz.loc v
    refine ⟨m v * n v - o, fun s hs => ?_⟩
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [add_comm w' w, ho s hs, e, hm v s hs, hn v s hs]
    ring
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cupEx (P : CohomologyHyp) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (T : Tower D) (hT : T.Fit) (k : Type) [Field k] (a : c.O →+* k) (ha : ∀ x ∈ maximalIdeal c.O, a x = 0)
    (W : Finset ℕ) (hW : ∀ w ∈ W, w.Prime ∧ T.Splits w) (w w' : ℤ × ℤ) (h1 : a ((T.fr W).rt w T.g0) ≠ 1)
    (h2 : a ((T.fr W).rt (w + w') T.g0) ≠ 1) (J : Type) [Finite J] (y : J → G T.F Ω → k)
    (hy : ∀ j, (T.fr W).Coc a w' (y j) ∧ y j T.g0 = 0) :
    ∃ W' : Finset ℕ, W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (∀ j, (T.fr W').Coc a w' (y j)) ∧
      ∃ (x : G T.F Ω → k) (m : T.ι → k), (T.fr W').Coc a w x ∧ x T.g0 = 0 ∧ (T.fr W').LocTriv a w x m ∧ (∃ g, x g ≠ 0) ∧
        ∀ j, ∃ z, (T.fr W').Cup a w w' x (y j) z m ∧ z T.g0 = 0 := by
  obtain ⟨hc, hf⟩ := Gys.coefFacts c k a ha
  have hD : D.Good := hT.2.elim (fun h => h.1.1) fun h => h.1.1
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨N', hN, x, m, hx, hm, ⟨g, g1, g2⟩, hz⟩ := Gys.cupRaw (T.fr W) a l hf (ok W) _ (Gys.gysT P D T hD W hW) w w' J y
    fun j => (hy j).1
  have hs := hN.sub
  obtain ⟨W', s1, s2, rfl⟩ := hN
  have hy' : ∀ j, (T.fr W').Coc a w' (y j) := fun j => ⟨(hy j).1.lc, (hy j).1.coc, fun g hg => (hy j).1.kill g (hs hg)⟩
  obtain ⟨x', m', b1, b2, b3, b4, b5⟩ := Gys.cupNorm (T.fr W') a (ok W') w w' h1 h2 J y (fun j => ⟨hy' j, (hy j).2⟩) x m hx hm hz
  exact ⟨W', s1, s2, hy', x', m', b1, b2, b3, ⟨g, (b4 g g1).symm ▸ g2⟩, b5⟩

theorem UpperTheory.V.Ws.Gys.mu_of {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)
    {p : PD Φ.ι Γ R} (hp : Φ.IsRes a p) (h : ∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) :
    ∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v ∧ ∀ i, a (Φ.χ i s) = 1 :=
  fun v s hs => ⟨h v s hs, fun i => (hp.res.char v s (h v s hs) i).symm.trans (hp.pair.mu v s hs i)⟩

theorem UpperTheory.V.Ws.Gys.gysinPs_of :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → Supp nM p.r →
      ∃ (W' : Finset ℕ) (s : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ s.In qQ ∧ s.SameAl p ∧ Ent s.r (-wPs) := by
  intro P Ω _ _ _ l _ c D T hT k _ a ha W hW p hp hs
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨-, r2, r3⟩ := Gys.rootCharacters_ne_one_at_basepoint (T.fr W) a (ok W)
  obtain ⟨x, x1, x2, x3, x4⟩ := Gys.dataAl (T.fr W) a p hp hs
  obtain ⟨W', s1, s2, hx, y, n, y1, y2, y3, ⟨g, hg⟩, hz⟩ := Gys.cupEx P D T hT k a ha W hW (-wPs) (-wAl) r2
    (by rw [add_comm]; exact r3) Unit (fun _ => x) fun _ => ⟨x1, x2⟩
  obtain ⟨z, z1, z2⟩ := hz ()
  have hmu := Gys.mu_of (T.fr W) a hp fun v s hs => hs.1
  obtain ⟨s, a1, a2, a3, a4, a5, -⟩ := Gys.ob (T.fr W') a (ok W') hmu x y (y * x - z) _ n (hx ()) x2 x3 y1 y2 y3
    (Gys.cupSwap (T.fr W') a _ _ y x z n _ y1 y3 (hx ()) x3 z1) (by
      show y T.g0 * x T.g0 - z T.g0 = 0
      rw [y2, z2, zero_mul, sub_zero])
  exact ⟨W', s, s1, s2, a1, a2, ⟨fun g => (a3 g).trans (x4 g).symm, a4⟩, g, 2, 0, by decide,
    a5 g ▸ mul_ne_zero hg (((T.fr W').χ 0 g).isUnit.map a).ne_zero⟩
