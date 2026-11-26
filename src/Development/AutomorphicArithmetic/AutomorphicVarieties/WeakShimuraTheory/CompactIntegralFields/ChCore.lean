module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ConstOfFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ValuationCharacters.ValLtIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.IncLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.HomOfDer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FibLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GysinPsOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.DiagGsp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PlaceMove
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LevBasis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.ChCore
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem UpperTheory.V.Ws.ch_num {x y : WithBot ℕ∞} {a b c N : ℕ} (h1 : x ≤ y + (a : ℕ)) (h2 : y + (b : ℕ) ≤ (c : ℕ))
    (h : c + a < N + b) : x < N := by
  refine h1.trans_lt ?_
  induction y using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h2 (by norm_cast)
    | coe y =>
      have h3 : y + b ≤ c := by exact_mod_cast h2
      exact_mod_cast (by omega : y + a < N)

private theorem UpperTheory.V.Ws.ch_core {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} {l : ℕ} [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ} (hS : Φ.Std l a)
    (X : Space Φ a) (J : Ideal X.B) (U : Φ.ι → Set Γ) (hU : ∀ v, ∀ s ∈ U v, s ∈ Φ.Gv v) {d C dv N : ℕ}
    (hB : Φ.Bounds ((residue Λ).comp a) d C) (hN1 : d + 20 * C + 1 < N)
    (hN2 : 2 * d + 1 + (2 + 4 * Nat.card Φ.ι) < N + dv)
    (hnn : ∀ v i j, i ≠ j → ∀ q : Ideal X.B, q.IsPrime → J ≤ q → (maximalIdeal Λ).map (algebraMap Λ X.B) ≤ q →
      (∀ s ∈ U v, X.ψ v i s - X.ψ v j s ∈ q) → ringKrullDim (X.B ⧸ q) + dv ≤ (2 * d + 1 : ℕ))
    (hp1 : ∀ (k : Type) [Field k] [Finite k] [Algebra Λ k] (y : X.A →ₐ[Λ] PowerSeries k),
      (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
      (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
      (∀ v i j, i ≠ j → ∃ s ∈ U v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
      Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
      X.LocZero J (y : X.A →+* PowerSeries k))
    {c : PD Φ.ι Γ (ResidueField Λ)} (hc : Φ.IsRes ((residue Λ).comp a) c) (hg : Φ.Good ((residue Λ).comp a) c)
    {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R) (hdef : Φ.IsDef a c (X.P.map (f : X.A →+* R)))
    {P Q : Ideal R} (hPQ : Ch.Adj R (N + 1) P Q) (hP : J ≤ P.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) :
    J ≤ Q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A)) := by
  classical
  haveI := hS.char
  let φ : X.B →+* R := (f : X.A →+* R).comp (algebraMap X.B X.A)
  have hφ : ∀ t : Λ, φ (algebraMap Λ X.B t) = algebraMap Λ R t := fun t => by
    show f (algebraMap X.B X.A _) = _
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  obtain ⟨ϖ, hϖ⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Λ)).1
  have hm : ∀ q : Ideal R, algebraMap Λ R ϖ ∈ q → ∀ t ∈ maximalIdeal Λ, algebraMap Λ R t ∈ q := fun q hq t ht => by
    rw [hϖ] at ht
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    rw [map_mul]
    exact q.mul_mem_left _ hq
  have hϖm : algebraMap Λ R ϖ ∈ maximalIdeal R :=
    map_nonunit _ _ (show ϖ ∈ maximalIdeal Λ by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
  let A : {S // S ∈ redTypes} → Ideal R := fun S => redIdeal S.1 (X.P.map (f : X.A →+* R)).r
  let B : {t : Φ.ι × Fin 4 × Fin 4 // t.2.1 ≠ t.2.2} → Ideal R := fun t =>
    J.map φ ⊔ Ideal.span {algebraMap Λ R ϖ} ⊔ Ideal.span ((fun s => φ (X.ψ t.1.1 t.1.2.1 s - X.ψ t.1.1 t.1.2.2 s)) '' U t.1.1)
  haveI : Finite {S // S ∈ redTypes} := (List.finite_toSet redTypes).to_subtype
  obtain ⟨p, hp, hIp, hdim, hϖp, hA, hBp⟩ := Ch.nice _ hϖm N (by omega) A B
    (fun S => (red Φ l a hS d C hB c hc hg R _ hdef S.1 S.2).trans_lt (by exact_mod_cast hN1))
    (fun t q hq hle hr => ch_num
      (fib Φ l a hS X c hc R f hdef q (Ch.irr hS.ok hc hdef.1
        ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.Quotient.mk q)) q
        (fun x hx => Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx))
        fun S hS => hr ⟨S, hS⟩))
      (hnn t.1.1 _ _ t.2 (q.comap φ) (Ideal.comap_isPrime _ _)
        (Ideal.map_le_iff_le_comap.1 (le_sup_left.trans (le_sup_left.trans hle)))
        (Ideal.map_le_iff_le_comap.2 fun u hu => by
          show φ (algebraMap Λ X.B u) ∈ q
          rw [hφ]
          exact hm q (hle (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))) u hu)
        fun s hs => hle (Ideal.mem_sup_right (Ideal.subset_span ⟨s, hs, rfl⟩))) hN2) _ hPQ.2.2
  obtain ⟨K, _, _, _, j, hj, hj0⟩ := Ch.curve l Λ R p hp hdim (hm p hϖp)
  have hJp : ∀ b ∈ J, φ b ∈ p := fun b hb => hIp (Ideal.mem_sup_left (hP hb))
  haveI : Q.IsPrime := hPQ.2.1.1.1
  refine hp1 K (j.comp f) (fun b hb => hj0 _ ?_) (fun b hb => (hj _).2 (hJp b hb)) (fun v i i' hi => ?_)
    (Ch.irr hS.ok hc hdef.1 ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K))).comp (j : R →+* PowerSeries K)) p
      (fun x hx => (hj x).1 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 hx)) fun S hS => hA ⟨S, hS⟩)
    _ (Ideal.comap_isPrime _ _) fun s hs => (hj _).2 (hIp (Ideal.mem_sup_right hs))
  · show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hb
  · by_contra hn
    push Not at hn
    refine hBp ⟨(v, i, i'), hi⟩ (sup_le (sup_le (Ideal.map_le_iff_le_comap.2 hJp)
      ((Ideal.span_singleton_le_iff_mem _).2 hϖp)) (Ideal.span_le.2 ?_))
    rintro _ ⟨s, hs, rfl⟩
    refine (hj _).1 ?_
    show (j.comp f) (algebraMap X.B X.A (X.ψ v i s - X.ψ v i' s)) = 0
    rw [map_sub, map_sub, X.ψ_map v i s (hU v s hs), X.ψ_map v i' s (hU v s hs), hn s hs, sub_self]

theorem UpperTheory.V.Ws.ch :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O) (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PM ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C → 30 * (C + 1) * (C + 1) ≤ T.d →
      ∀ x : X.A →ₐ[c'.O] ResidueField c'.O, (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) → (T.fr ∅).Good ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x) := by
  intro hC Ω _ _ _ l _ c D T hF hD ι c' h X J hPM C hB hd x hx hg ⟨q₀, hq₀, hq₀x, hq₀J⟩ q hq hqx
  haveI : Finite (ResidueField c'.O) := (UpperTheory.V.abelian₂.dvr_finite l c'.O).2.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  haveI : TotallyDisconnectedSpace (G T.F Ω) := inferInstanceAs (TotallyDisconnectedSpace (Ω ≃ₐ[T.F] Ω))
  have hS := (std hC D T hF ∅ c' h).1 (Finset.notMem_empty 0)
  obtain ⟨R, _, _, _, f, hdef, hfl, hres⟩ := cmplEx (T.fr ∅) l (inc h) hS X x hx
  obtain ⟨a, b, π, e, hπ, hk, hab⟩ := x1 hC D T hF hD c' h _ hx R _ hdef
  obtain ⟨dv, hdv⟩ := chDv D T
  have hg' : Nat.card T.ι ≤ C := hB.card
  have hdv' : 30 * (C + 1) ≤ dv := by
    by_contra hn
    have h1 : dv * Nat.card T.ι ≤ 30 * (C + 1) * C := Nat.mul_le_mul (by omega) hg'
    nlinarith
  have hd' : 30 * (C + 1) ≤ T.d := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hd
  obtain ⟨N, hN⟩ : ∃ N, N + 2 * Nat.card T.ι = 2 * T.d + 1 := ⟨2 * T.d + 1 - 2 * Nat.card T.ι, by omega⟩
  have hker : RingHom.ker x = (maximalIdeal R).comap (f : X.A →+* R) := by
    ext z
    rw [RingHom.mem_ker, ← hres]
    exact res_eq_zero_iff c'.O R (f z)
  obtain ⟨P, hP, rfl⟩ := Ch.flat_min _ hfl hq₀ (hker ▸ hq₀x)
  obtain ⟨Q, hQ, rfl⟩ := Ch.flat_min _ hfl hq (hker ▸ hqx)
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap] at hq₀J ⊢
  have hch := Ch.chain c'.O (D := N + 1) π e hπ hk (by omega) hP hQ
  clear hq hqx hQ
  induction hch with
  | refl => exact hq₀J
  | tail _ hPQ ih =>
    exact ch_core hS X J T.U1 (fun v s hs => Ine_le_Dec _ hs.1) (dv := dv) hB (by omega)
      (by show _ + (2 + 4 * Nat.card T.ι) < _; omega)
      (fun v i j hij q h1 h2 h3 h4 => nn hC D T hF hD ι c' h X J hPM v i j hij q h1 h2 h3 h4 dv hdv) hPM.p1 hx hg f hdef hPQ ih
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinAl
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.DataPs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lc_of_cont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {f : Γ → R} (h : UpperTheory.V.Alg.AdicCont ⊥ f) :
    IsLocallyConstant f := by
  refine IsLocallyConstant.desc _ _ (h 1) ?_
  intro x y hxy
  rw [Ideal.Quotient.eq, pow_one, Ideal.mem_bot, sub_eq_zero] at hxy
  exact hxy

theorem UpperTheory.V.Ws.Gys.dataPs :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R) (p : PD Φ.ι Γ R), Φ.IsRes a p → Supp nP p.r →
      ∃ y : Γ → R, Φ.Coc a (-wPs) y ∧ y Φ.g0 = 0 ∧ Φ.LocTriv a (-wPs) y (fun v => p.n v 2 0) ∧ ∀ g, p.r g 2 0 = y g * a (Φ.χ 0 g) := by
  intro O Γ R _ _ _ _ Φ a p hR hS
  have hc : ∀ i j, IsLocallyConstant fun g => p.r g i j := fun i j => lc_of_cont (hR.cont i j)
  have hd := hR.res.diag
  have hinv : ∀ g, Ring.inverse (p.r g 0 0) = a ↑((Φ.χ 0 g)⁻¹) := by
    intro g
    rw [hd g 0]
    have hu : a ↑(Φ.χ 0 g) = ↑(Units.map a.toMonoidHom (Φ.χ 0 g)) := rfl
    rw [hu, Ring.inverse_unit]
    rfl
  have hone : ∀ g, a ↑(Φ.χ 0 g) * a ↑((Φ.χ 0 g)⁻¹) = 1 := by
    intro g
    rw [← map_mul, Units.mul_inv, map_one]
  have he : ∀ g, Φ.rt (-wPs) g = Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    intro g
    simp [Fr.rt, wPs]
  refine ⟨fun g => p.r g 2 0 * Ring.inverse (p.r g 0 0), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (hc 2 0).mul ((hc 0 0).comp Ring.inverse)
  · intro g h
    have z1 : p.r g 2 1 = 0 := hS g 2 1 (by decide) (by decide)
    have z3 : p.r g 2 3 = 0 := hS g 2 3 (by decide) (by decide)
    show p.r (g * h) 2 0 * Ring.inverse (p.r (g * h) 0 0) =
      p.r g 2 0 * Ring.inverse (p.r g 0 0) + a ↑(Φ.rt (-wPs) g) * (p.r h 2 0 * Ring.inverse (p.r h 0 0))
    rw [hinv (g * h), hinv g, hinv h, he g]
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_four, z1, z3, zero_mul, add_zero, hd, mul_inv,
      Units.val_mul]
    linear_combination (p.r g 2 0 * a ↑((Φ.χ 0 g)⁻¹)) * hone h
  · intro g hg
    show p.r g 2 0 * Ring.inverse (p.r g 0 0) = 0
    rw [hR.pair.kill g hg, Matrix.one_apply_ne (by decide), zero_mul]
  · show p.r Φ.g0 2 0 * Ring.inverse (p.r Φ.g0 0 0) = 0
    rw [hR.pair.nrm (by decide : (2 : Fin 4) ≠ 0), zero_mul]
  · intro v s hs
    have hn := hR.pair.low v
    have hna0 : adj (p.n v) * p.n v = 1 := by
      have h1 := hn.1
      simpa [IsGSp] using h1
    have hna : p.n v * adj (p.n v) = 1 := mul_eq_one_comm.mp hna0
    have hX := hR.pair.flag v s hs
    have hch : (adj (p.n v) * p.r s * p.n v) 0 0 = a ↑(Φ.χ 0 s) := hR.res.char v s hs 0
    have key : p.r s * p.n v = p.n v * (adj (p.n v) * p.r s * p.n v) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hna, Matrix.one_mul]
    have k20 := congrFun (congrFun key 2) 0
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four] at k20
    rw [hS s 2 1 (by decide) (by decide), hS s 2 3 (by decide) (by decide), hd s 2, hn.2.1 0,
      hX 1 0 (by decide), hX 2 0 (by decide), hX 3 0 (by decide), hch] at k20
    show p.r s 2 0 * Ring.inverse (p.r s 0 0) = p.n v 2 0 - a ↑(Φ.rt (-wPs) s) * p.n v 2 0
    rw [hinv, he s, Units.val_mul, map_mul]
    linear_combination (a ↑((Φ.χ 0 s)⁻¹)) * k20 + (p.n v 2 0) * hone s
  · intro g
    show p.r g 2 0 = p.r g 2 0 * Ring.inverse (p.r g 0 0) * a ↑(Φ.χ 0 g)
    rw [hinv]
    linear_combination (-(p.r g 2 0)) * hone g
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.gysinAl :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p p' : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → (T.fr W).IsRes a p' → p.In nP → p'.In nP →
      ∃ (W' : Finset ℕ) (s s' : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ (T.fr W').IsRes a s' ∧
        s.In qQ ∧ s'.In qQ ∧ s.SamePs p ∧ s'.SamePs p' ∧ s.SameAl s' ∧ Ent s.r (-wAl) := by
  intro P Ω _ _ _ l _ c D T hT k _ a ha W hW p p' hp hp' hs hs'
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨r1, -, r3⟩ := Gys.rootCharacters_ne_one_at_basepoint (T.fr W) a (ok W)
  obtain ⟨y, y1, y2, y3, y4⟩ := Gys.dataPs (T.fr W) a p hp hs.1
  obtain ⟨y', y1', y2', y3', y4'⟩ := Gys.dataPs (T.fr W) a p' hp' hs'.1
  obtain ⟨W', s1, s2, hy, x, m, x1, x2, x3, ⟨g, hg⟩, hz⟩ := Gys.cupEx P D T hT k a ha W hW (-wAl) (-wPs) r1 r3 Bool
    (fun b => cond b y y') fun b => by cases b; exacts [⟨y1', y2'⟩, ⟨y1, y2⟩]
  obtain ⟨z, z1, z2⟩ := hz true
  obtain ⟨z', z1', z2'⟩ := hz false
  have hmu := Gys.mu_of (T.fr W) a hp fun v s hs => hs.1
  obtain ⟨s, a1, a2, a3, a4, a5, a6⟩ := Gys.ob (T.fr W') a (ok W') hmu x y z m _ x1 x2 x3 (hy true) y2 y3 z1 z2
  obtain ⟨s', b1, b2, b3, b4, b5, b6⟩ := Gys.ob (T.fr W') a (ok W') hmu x y' z' m _ x1 x2 x3 (hy false) y2' y3' z1' z2'
  exact ⟨W', s, s', s1, s2, a1, b1, a2, b2, ⟨fun g => (a5 g).trans (y4 g).symm, a6⟩, ⟨fun g => (b5 g).trans (y4' g).symm, b6⟩,
    ⟨fun g => (a3 g).trans (b3 g).symm, fun v => (a4 v).trans (b4 v).symm⟩, g, 1, 0, by decide,
    a3 g ▸ mul_ne_zero hg (((T.fr W').χ 0 g).isUnit.map a).ne_zero⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RestrQ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem muIne {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) {s : G F Ω}
    (hs : s ∈ muOf l (Dec (F := F) A)) : s ∈ Ine (F := F) A := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  obtain ⟨h1, a, h2⟩ := hs
  exact Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a)
    (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h2)

private theorem cont_resQ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] :
    Continuous (resQ F) := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  exact (galEmbTop ℚ F Ω).1.continuous

private theorem low_desc {A V : Type} [CommRing A] [CommRing V] [IsLocalRing V] (f : A →+* V) (hf : Function.Injective f)
    [IsLocalHom f] (ν : V) (hν : IsUnit ν) (X n₀ : M4 A) (hX : IsGSp ν (X.map f)) (h0 : IsLow (n₀.map f))
    (hs : SuppM nP ((X.map f).map (residue V))) (hd : ∀ i, IsUnit (((X.map f).map (residue V)) i i))
    (h0' : IsLow ((n₀.map f).map (residue V))) (hq : SuppM qQ ((n₀.map f).map (residue V))) :
    ∃ n : M4 A, IsLow n ∧ IsUp (adj n * X * n₀) := by
  have hG : ∀ (μ : A) (Y : M4 A), IsGSp (f μ) (Y.map f) → IsGSp μ Y := fun μ Y h => by
    unfold IsGSp at h ⊢
    rw [adj_map, ← Matrix.map_mul] at h
    ext i j
    apply hf
    have := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at this
    rw [this]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hμ : f ((adj X * X) 0 0) = ν := by
    have h := hX
    unfold IsGSp at h
    rw [adj_map, ← Matrix.map_mul] at h
    simpa using congrFun (congrFun h 0) 0
  obtain ⟨⟨u1, u2⟩, -⟩ := Rq.shapeQ _ _ _ hs hd h0' hq
  rw [← Matrix.map_mul, ← Matrix.map_mul] at u1 u2
  simp only [Matrix.map_apply, ← map_mul, ← map_sub] at u1 u2
  refine Rq.luG A ((adj X * X) 0 0) X n₀ (IsUnit.of_map f _ (hμ ▸ hν)) (hG _ _ (hμ ▸ hX))
    ⟨hG 1 _ (by rw [map_one]; exact h0.1), fun i => hf ?_, fun i j hij => hf ?_⟩
    (IsUnit.of_map f _ (IsUnit.of_map (residue V) _ u1)) (IsUnit.of_map f _ (IsUnit.of_map (residue V) _ u2))
  · rw [map_one]; exact h0.2.1 i
  · rw [map_zero]; exact h0.2.2 i j hij

private theorem low_map {A V : Type} [CommRing A] [CommRing V] (f : A →+* V) {n : M4 A} (h : IsLow n) : IsLow (n.map f) :=
  ⟨by simpa using isGSp_map f h.1, fun i => by rw [Matrix.map_apply, h.2.1, map_one],
    fun i j hij => by rw [Matrix.map_apply, h.2.2 i j hij, map_zero]⟩

private theorem up_map {A V : Type} [CommRing A] [CommRing V] (f : A →+* V) {n X m : M4 A} (h : IsUp (adj n * X * m)) :
    IsUp (adj (n.map f) * X.map f * m.map f) := fun i j hij => by
  rw [adj_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, h i j hij, map_zero]

theorem UpperTheory.V.Ws.restrQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T₀ T : Tower D, T₀.Fit → T₀.Le T → ∀ (𝔞 : Amb l) (P : PD Unit (G ℚ Ω) 𝔞.V), QPair D T₀.pr (resQ T₀.F T₀.g0) 𝔞 P →
      LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) (P.map (residue 𝔞.V)) →
      ∃ P' : PD T.ι (G T.F Ω) 𝔞.V, 𝔞.Small P' ∧ (T.fr ∅).IsPair (𝔞.a c) P' ∧ P'.r = P.r.comp (resQ T.F) ∧
        T.OverQ (P.map (residue 𝔞.V)) (P'.map (residue 𝔞.V)) ∧ (T.fr ∅).IsRes (𝔞.red c) (P'.map (residue 𝔞.V)) ∧
        ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), P'.ψ v i s = 𝔞.a c (D.ps i (resQ T.F s)) := by
  intro Ω _ _ _ l hl c D hD T₀ T hF hLe 𝔞 P hP hS
  have hOk : T.Ok := (leFit D hD T₀ T hLe).1 hF.1
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hP.small
  haveI := hf.loc
  choose g hg hgD hgI using fun v : T.ι => Rq.placeMove T.F l hl.out (T.pl v) (D.pl l) (T.ovl v) (hD.pl_over l hl.out)
  have hν : ∀ x, IsUnit (𝔞.a c (D.th x)) := fun x => (D.th x).isUnit.map _
  have hd : ∀ x i, IsUnit ((((P₁.map f).map (residue 𝔞.V)).r x) i i) := fun x i => by
    rw [hS.res.res.diag]
    exact (Units.isUnit _).map _
  choose n hn hb using fun v : T.ι => low_desc f hf.inj _ (hν (g v)) (P₁.r (g v)) (P₁.n ()) (hP.pair.mult (g v))
    (hP.pair.low ()) (hS.supp (g v)) (hd (g v)) (hS.res.pair.low ()) hS.flag
  let Q : PD T.ι (G T.F Ω) A := ⟨P₁.r.comp (resQ T.F), n⟩
  have key : ∀ v, ∀ s ∈ Dec (F := T.F) (T.pl v), IsUp (adj ((Q.map f).n v) * (Q.map f).r s * (Q.map f).n v) ∧
      ∀ i, (Q.map f).ψ v i s = (P₁.map f).ψ () i ((g v)⁻¹ * resQ T.F s * g v) := fun v s hs =>
    Rq.conjFlag _ _ ((P₁.map f).r (g v)) ((P₁.map f).r ((g v)⁻¹ * resQ T.F s * g v)) ((P₁.map f).r (resQ T.F s)) _ _
      (hν (g v)) (hP.pair.mult (g v)) (hP.pair.low ()) (low_map f (hn v)) (up_map f (hb v))
      (by rw [← map_mul, ← map_mul, mul_assoc, mul_inv_cancel_left]) (hP.pair.flag () _ (hgD v s hs))
  have hconj : ∀ (χ : G ℚ Ω →* c.Oˣ) (x y : G ℚ Ω), χ (x⁻¹ * y * x) = χ y := fun χ x y => by
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  have hI : ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), (Q.map f).ψ v i s = 𝔞.a c (D.ps i (resQ T.F s)) := fun v i s hs => by
    rw [(key v s (Ine_le_Dec _ hs)).2, hP.inert _ (hgI v s hs), hconj]
  have hpair : (T.fr ∅).IsPair (𝔞.a c) (Q.map f) := by
    refine ⟨fun x => hP.pair.mult (resQ T.F x), Rq.killQ D hD T hOk _ _ _ (P₁.map f).r hP.pair.kill, ?_,
      fun v => low_map f (hn v), fun v s hs => (key v s hs).1, fun v s hs i => ?_⟩
    · obtain ⟨j, hj⟩ := hLe.g0
      show ((P₁.map f).r (resQ T.F T.g0)).IsDiag
      have h := hP.pair.nrm
      change ((P₁.map f).r (resQ T₀.F T₀.g0)).IsDiag at h
      rw [hj, map_pow, ← h.diagonal_diag, Matrix.diagonal_pow]
      exact Matrix.isDiag_diagonal _
    · refine (hI v i s (muIne T.F l _ (T.ovl v) hs)).trans ?_
      rw [Rq.muPs D hD T hOk _ s hs i, Units.val_one, map_one]
  have hb' : ∀ v, IsUp (adj (((Q.map f).map (residue 𝔞.V)).n v) * ((P₁.map f).map (residue 𝔞.V)).r (g v) *
      ((P₁.map f).map (residue 𝔞.V)).n ()) := fun v => up_map (residue 𝔞.V) (up_map f (hb v))
  have hp' := hpair.map (residue 𝔞.V)
  refine ⟨Q.map f, ⟨A, _, _, inferInstance, f, Q, hf, fun i j N => (hc i j N).comp_continuous (cont_resQ T.F), rfl⟩, hpair, rfl,
    ⟨rfl, fun v => ⟨(), g v, hg v, hb' v⟩⟩, ⟨hp', ⟨fun x i => ?_, fun v s hs i => ?_, Or.inl ⟨fun x => hS.supp _, fun v => ?_⟩⟩,
      fun i j N => (hS.res.cont i j N).comp_continuous (cont_resQ T.F)⟩, hI⟩
  · show _ = 𝔞.red c (chi D T.pr i (resQ T.F x))
    rw [hLe.pr]
    exact hS.res.res.diag (resQ T.F x) i
  · show _ = 𝔞.red c (chi D T.pr i (resQ T.F s))
    refine (PD.map_ψ (Q.map f) (residue 𝔞.V) v i s).trans ?_
    rw [(key v s hs).2, ← PD.map_ψ, hLe.pr, ← hconj (chi D T₀.pr i) (g v)]
    exact hS.res.res.char () _ (hgD v s hs) i
  · exact (Rq.shapeQ _ _ _ (hS.supp (g v)) (hd (g v)) (hS.res.pair.low ()) hS.flag).2 _ (hp'.low v) (hb' v)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.GysinPs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.gysinPs :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → Supp nM p.r →
      ∃ (W' : Finset ℕ) (s : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ s.In qQ ∧ s.SameAl p ∧ Ent s.r (-wPs) :=
  UpperTheory.V.Ws.Gys.gysinPs_of
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallCont
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem cont_of_adic {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedRing K] (I : Ideal R)
    (y : R →+* K) (a : ℝ) (ha1 : a < 1) (hy : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n)
    (f : Γ → R) (hf : AdicCont I f) : Continuous fun g => y (f g) := by
  have ha0 : 0 ≤ a := by simpa using hy 1 0 (Ideal.zero_mem _)
  rw [Metric.continuous_iff']
  intro g0 ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε ha1
  have hopen := (hf N).isOpen_fiber ((Ideal.Quotient.mk (I ^ N)) (f g0))
  filter_upwards [hopen.mem_nhds rfl] with g hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hy N _ (Ideal.Quotient.eq.mp hg)) hN

theorem UpperTheory.V.Ws.smallCont :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ {ι Γ : Type} [Group Γ] [TopologicalSpace Γ]
          (P : PD ι Γ 𝔞.V), 𝔞.Small P → Continuous (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) P.r) := by
  intro l _ 𝔞 e he ι Γ _ _ P hP
  obtain ⟨A, _, _, _, f, P₁, hf, hc, rfl⟩ := hP
  obtain ⟨inj, loc, -, -, -⟩ := hf
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  let y : A →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp (𝔞.toK.comp f)
  have hV : ∀ v : 𝔞.V, ‖e (v : 𝔞.K)‖ ≤ 1 := fun v => (he.2 _).mp v.2
  have hle : ∀ x : A, ‖y x‖ ≤ 1 := fun x => hV (f x)
  have hlt : ‖y ϖ‖ < 1 := by
    refine lt_of_le_of_ne (hle ϖ) fun h1 => hϖ.not_isUnit ?_
    have hne : (f ϖ : 𝔞.K) ≠ 0 := by
      intro h0
      have h0' : f ϖ = 0 := Subtype.ext h0
      exact hϖ.ne_zero (inj (by rw [h0', map_zero]))
    have h1' : ‖e (f ϖ : 𝔞.K)‖ = 1 := h1
    have hinv : ((f ϖ : 𝔞.K))⁻¹ ∈ 𝔞.V := by
      rw [he.2, map_inv₀, norm_inv, h1', inv_one]
    have hu : IsUnit (f ϖ) := IsUnit.of_mul_eq_one (⟨_, hinv⟩ : 𝔞.V) (Subtype.ext (mul_inv_cancel₀ hne))
    haveI := loc
    exact (isUnit_map_iff f ϖ).mp hu
  have hpow : ∀ n, ∀ x ∈ maximalIdeal A ^ n, ‖y x‖ ≤ ‖y ϖ‖ ^ n := by
    intro n x hx
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [map_mul, map_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (hle c)
  refine continuous_matrix fun i j => ?_
  have hc' : AdicCont (maximalIdeal A) fun g => P₁.r g i j := by
    unfold PD.Cont at hc
    exact hc i j
  exact cont_of_adic (maximalIdeal A) y _ hlt hpow (fun g => P₁.r g i j) hc'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.FrobIn
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobInPowCong
theorem UpperTheory.Reformulated.B.Qf16.frobIn_pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω)
    {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω inst A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [h]
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hb n)) hab
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem frobIn_pow_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω} (ha : A.valuation a ≤ 1)
    (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) : A.valuation (a ^ m - b ^ m) < 1 :=
  _root_.UpperTheory.Reformulated.B.Qf16.frobIn_pow_cong A ha hb h m

private theorem frobIn_dec_le {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω}
    {g : G K Ω} (hg : g ∈ Dec (F := K) A) {x : Ω} (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem frobIn_isFrob_pow {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) :
    IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (frobIn_dec_le ih.1 hx)
    have h2 := frobIn_pow_cong A (frobIn_dec_le ih.1 hx) (b := x ^ q ^ n)
      (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

theorem UpperTheory.V.Ws.frobIn :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G ℚ Ω)) (M : ℕ),
          IsOpen (U : Set (G ℚ Ω)) → M ≠ 0 → ∃ (p : ℕ) (A : ValuationSubring Ω) (f : ℕ) (σ : G ℚ Ω), p.Prime ∧ ¬ p ∣ M ∧
            A.valuation (p : Ω) < 1 ∧ 0 < f ∧ σ ∈ U ∧ IsFrob A (p ^ f) σ ∧ ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) ^ f := by
  intro Ω _ _ _ l hl U M hU hM
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (M + l + 1)
  have hpM : ¬ p ∣ M := fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM) h
    omega
  have hlp : p ≠ l := by omega
  obtain ⟨hex, hfr, -, hco, -, -, -, -, hpl, -⟩ := ML.placeBasic Ω
  obtain ⟨A, hA⟩ := hex p hp
  obtain ⟨φ, hφ⟩ := hfr A p hp hA
  obtain ⟨w, hw, -, -⟩ := hpl A p hp hA
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => by
    refine hco _ p l ((Nat.coprime_primes hp hl.out).2 hlp) hA ?_
    have h1 := (hw ((l : ℕ) : 𝓞 ℚ)).2 h
    have e : algebraMap ℚ Ω (((l : ℕ) : 𝓞 ℚ) : ℚ) = (l : Ω) := by simp
    rw [e] at h1
    exact h1
  have h : ((cycZ ℚ Ω l φ : ℤ_[l]ˣ) : ℤ_[l]) = (p : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.1 fun n => ?_
    rw [cycZ_toZModPow_eq hlw hw (q := p) hφ.2 n]
  haveI : IsGalois ℚ Ω := inferInstance
  haveI : Finite (G ℚ Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  obtain ⟨f, hf, -, hfU⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (H := U) Subgroup.index_ne_zero_of_finite φ
  refine ⟨p, A, f, φ ^ f, hp, hpM, hA, hf, hfU, frobIn_isFrob_pow hφ f, ?_⟩
  rw [map_pow, Units.val_pow_eq_pow_val, h]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.WtChar
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.WeightCharacterKernel

private theorem open_ker {Ω K : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Field K] [TopologicalSpace K] [T2Space K]
    [ContinuousMul K] (δ : G ℚ Ω →* Kˣ) (hc : Continuous fun g => (δ g : K)) (N : ℕ) (hN : N ≠ 0)
    (h : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) A, δ g ^ N = 1) : IsOpen (δ.ker : Set (G ℚ Ω)) := by
  classical
  have hpow : ∀ g, δ g ^ N = 1 := by
    intro g
    by_contra hg
    obtain ⟨a, ha⟩ : ∃ a : K, a = ((δ g ^ N : Kˣ) : K) := ⟨_, rfl⟩
    have ha1 : a ≠ 1 := fun h1 => hg (Units.val_eq_one.mp (ha ▸ h1))
    have hUo : IsOpen ((fun x => (δ x : K) ^ N) ⁻¹' ({a}ᶜ : Set K)) :=
      isOpen_compl_singleton.preimage (hc.pow N)
    have h1U : (1 : G ℚ Ω) ∈ ((fun x => (δ x : K) ^ N) ⁻¹' ({a}ᶜ : Set K)) := by
      simpa [eq_comm] using ha1
    obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
    have hsup : W.toSubgroup ⊔ ((powMonoidHom N).comp δ).ker = ⊤ := by
      refine B3.minkowski Ω _ inferInstance (Subgroup.isOpen_mono le_sup_left W.isOpen) ?_
      intro B x hx
      apply Subgroup.mem_sup_right
      simpa using h B x hx
    have hg' : g ∈ W.toSubgroup ⊔ ((powMonoidHom N).comp δ).ker := hsup ▸ Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hg'
    have hz' : δ z ^ N = 1 := by simpa using hz
    have heq : (δ y : K) ^ N = a := by
      rw [ha, ← hyz, map_mul, mul_pow, hz', mul_one, Units.val_pow_eq_pow_val]
    exact (hW hy) heq
  have hfin : ({x : K | x ^ N = 1} \ {1}).Finite := by
    refine (Finset.finite_toSet (Polynomial.nthRoots N (1 : K)).toFinset).subset ?_
    intro x hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hN)).mpr hx.1
  have hopen : IsOpen ((fun g => (δ g : K)) ⁻¹' ({x : K | x ^ N = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hc
  convert hopen using 1
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h1
    simp [h1]
  · intro h2
    have hN1 : (δ g : K) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hpow g, Units.val_one]
    exact Units.val_eq_one.mp (by by_contra hne; exact h2 ⟨hN1, hne⟩)

end UpperTheory.V.Ws.WeightCharacterKernel

open UpperTheory.V.Ws.WeightCharacterKernel in
theorem UpperTheory.V.Ws.wtChar :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good →
          ∀ (κ : G ℚ Ω →* PadicAlgCl l) (n : ℕ), Continuous κ → D.UnrT κ 1 → (∀ p ∈ D.Sb, ∀ g ∈ D.Ip p ⊓ D.ψ.ker, κ g = 1) →
          (∀ s ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker, κ s = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l s : ℤ_[l]) ^ n) →
          ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ g ∈ U, κ g = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ n := by
  intro Ω _ _ _ l _ c D hD κ n hκc hU hSb hl
  classical
  have hF := facts D hD
  have hrb : IsOpen (D.rbar.ker : Set (G ℚ Ω)) := hF.2.2.2.2.2.2.2.2.2.2.2.1
  have hom : IsOpen (D.om.ker : Set (G ℚ Ω)) := hF.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hps : IsOpen (D.ψ.ker : Set (G ℚ Ω)) := hD.psi_open
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℕ, M ≠ 0 ∧ ∀ g : G ℚ Ω, g ^ M ∈ D.rbar.ker ⊓ D.ψ.ker ⊓ D.om.ker := by
    have ho : IsOpen ((D.rbar.ker ⊓ D.ψ.ker ⊓ D.om.ker : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
      simpa only [Subgroup.coe_inf] using (hrb.inter hps).inter hom
    have := Subgroup.quotient_finite_of_isOpen _ ho
    exact ⟨_, Subgroup.index_ne_zero_of_finite, fun g => Subgroup.pow_index_mem _ g⟩
  have two : ∀ (B : ValuationSubring Ω) (p q : ℕ), p.Prime → q.Prime → p ≠ q →
      B.valuation (p : Ω) < 1 → ¬ B.valuation (q : Ω) < 1 := by
    intro B p q hp hq hpq h1 h2
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
    have hab' : (a : Ω) * p + (b : Ω) * q = 1 := by
      have := congrArg (Int.cast : ℤ → Ω) hab
      push_cast at this
      exact this
    have ha : B.valuation (a : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (intCast_mem B a)
    have hb : B.valuation (b : Ω) ≤ 1 := (B.valuation_le_one_iff _).mpr (intCast_mem B b)
    have e1 : B.valuation ((a : Ω) * p) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) h1
    have e2 : B.valuation ((b : Ω) * q) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hb) h2
    have := B.valuation.map_add ((a : Ω) * p) ((b : Ω) * q)
    rw [hab', map_one] at this
    exact absurd this (not_le.mpr (max_lt e1 e2))
  have halg : Continuous fun x : ℤ_[l] => algebraMap ℤ_[l] (PadicAlgCl l) x := by
    have e : ∀ x : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l]) :=
      fun x => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ x
    simp_rw [e]
    exact (continuous_algebraMap ℚ_[l] _).comp continuous_subtype_val
  let cU : G ℚ Ω →* (PadicAlgCl l)ˣ :=
    (Units.map (algebraMap ℤ_[l] (PadicAlgCl l)).toMonoidHom).comp (cycZ ℚ Ω l)
  have hcU : ∀ g, ((cU g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) := by
    intro g
    rfl
  let δ : G ℚ Ω →* (PadicAlgCl l)ˣ := κ.toHomUnits * (cU ^ n)⁻¹
  have hδ : ∀ g, δ g = κ.toHomUnits g * (cU g ^ n)⁻¹ := fun g => by simp [δ]
  have hker : ∀ g, δ g = 1 ↔ κ g = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l]) ^ n := by
    intro g
    rw [hδ, mul_inv_eq_one, Units.ext_iff, Units.val_pow_eq_pow_val, hcU, MonoidHom.coe_toHomUnits]
  have hval : ∀ g, ((δ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) = κ g * ((cU g⁻¹ : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ n := by
    intro g
    rw [hδ, map_inv, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits]
  have hcont : Continuous fun g => ((δ g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := by
    simp_rw [hval, hcU]
    exact hκc.mul (((halg.comp (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))).comp continuous_inv).pow n)
  have hδ1 : ∀ h, κ h = 1 → cycZ ℚ Ω l h = 1 → δ h = 1 := by
    intro h h1 h2
    rw [hker, h1, h2]
    simp
  have hN : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) A, δ g ^ M = 1 := by
    intro A g hg
    by_cases hA : Raw.Away D.T A
    · rw [← map_pow]
      have hgM : g ^ M ∈ Ine (F := ℚ) A := Subgroup.pow_mem _ hg M
      have hr : g ^ M ∈ D.rbar.ker := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hM g)).1).1
      refine hδ1 _ (hU A hA _ hgM hr) ?_
      have hlA : ¬ A.valuation (l : Ω) < 1 := hA l (by unfold Raw.T; simp)
      exact (places ℚ Ω l A).2.2.2 hlA hgM
    · have hA' : ∃ p ∈ D.T, A.valuation (p : Ω) < 1 := by
        unfold Raw.Away at hA
        push_neg at hA
        exact hA
      obtain ⟨p, hpT, hpA⟩ := hA'
      have hpT' : p = l ∨ p ∈ D.Sb := by
        unfold Raw.T at hpT
        simpa using hpT
      have hp : p.Prime := by
        rcases hpT' with rfl | hpS
        · exact Fact.out
        · exact (hF.1 p hpS).1
      obtain ⟨x, hx⟩ := (B3.placesQ Ω).2.2 p (D.pl p) A hp (hD.pl_over p hp) hpA
      have hconj : δ g ^ M = δ ((x⁻¹ * g * x) ^ M) := by
        rw [map_pow, map_mul, map_mul, map_inv]
        congr 1
        rw [mul_comm (δ x)⁻¹ (δ g), mul_assoc, inv_mul_cancel, mul_one]
      rw [hconj]
      have hI : (x⁻¹ * g * x) ^ M ∈ Ine (F := ℚ) (D.pl p) := Subgroup.pow_mem _ (hx g hg) M
      have hm := hM (x⁻¹ * g * x)
      have hψ : (x⁻¹ * g * x) ^ M ∈ D.ψ.ker := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hm).1).2
      have ho : (x⁻¹ * g * x) ^ M ∈ D.om.ker := (Subgroup.mem_inf.mp hm).2
      rcases hpT' with rfl | hpS
      · exact (hker _).mpr (hl _ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hI, hψ⟩, ho⟩))
      · refine hδ1 _ (hSb p hpS _ (Subgroup.mem_inf.mpr ⟨hI, hψ⟩)) ?_
        have hne : p ≠ l := (hF.1 p hpS).2.1
        have hnl : ¬ (D.pl p).valuation (l : Ω) < 1 := two (D.pl p) p l hp Fact.out hne (hD.pl_over p hp)
        exact (places ℚ Ω l (D.pl p)).2.2.2 hnl hI
  refine ⟨δ.ker, open_ker δ hcont M hM0 hN, fun g hg => (hker g).mp hg⟩
end
