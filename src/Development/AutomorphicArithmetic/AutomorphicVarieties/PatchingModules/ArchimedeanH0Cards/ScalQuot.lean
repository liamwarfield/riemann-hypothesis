module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.scal_quot {R R' V : Type} [CommRing R] [CommRing R'] [AddCommGroup V]
    [Module R V] [Module R' V] (Z B : Submodule R V) (Z' B' : Submodule R' V)
    (hZ : ∀ v, v ∈ Z ↔ v ∈ Z') (hB : ∀ v, v ∈ B ↔ v ∈ B') :
    ∃ e : (Z ⧸ B.comap Z.subtype) ≃+ (Z' ⧸ B'.comap Z'.subtype),
      ∀ (z : Z) (z' : Z'), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  let f : Z ≃+ Z' :=
    { toFun := fun z => ⟨z.1, (hZ _).1 z.2⟩
      invFun := fun z => ⟨z.1, (hZ _).2 z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hf : (B.comap Z.subtype).toAddSubgroup.map (f : Z →+ Z') = (B'.comap Z'.subtype).toAddSubgroup := by
    ext z'
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hB _).1 hz
    · intro hz
      exact ⟨f.symm z', (hB _).2 hz, rfl⟩
  refine ⟨QuotientAddGroup.congr _ _ f hf, fun z z' h => ?_⟩
  have : z' = f z := Subtype.ext h.symm
  subst this
  rfl

theorem UpperTheory.V.Pa.B2.scal :
    ∀ (A G : Type) [CommRing A] [Group G] [TopologicalSpace G] (M : FRep A G) (N : ℕ) [Module (ZMod N) M.X], ContAction (GlobalTheory.Published.zmodRep N M.ρ) ∧ Nonempty (H0 M.ρ ≃+ H0 (GlobalTheory.Published.zmodRep N M.ρ)) ∧ (∃ e : H1 M.ρ ≃+ H1 (GlobalTheory.Published.zmodRep N M.ρ), ∀ (z : Z1 M.ρ) (z' : Z1 (GlobalTheory.Published.zmodRep N M.ρ)), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z') ∧ ∃ e : H2 M.ρ ≃+ H2 (GlobalTheory.Published.zmodRep N M.ρ), ∀ (z : Z2 M.ρ) (z' : Z2 (GlobalTheory.Published.zmodRep N M.ρ)), z.1 = z'.1 → e (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  intro A G _ _ _ M N _
  refine ⟨M.cont, ⟨?_⟩, ?_, ?_⟩
  · exact
      { toFun := fun z => ⟨z.1, z.2⟩
        invFun := fun z => ⟨z.1, z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
  · exact UpperTheory.V.Pa.B2.scal_quot _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  · exact UpperTheory.V.Pa.B2.scal_quot _ _ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV
namespace UpperTheory.V.Pa.B2

variable {l : ℕ} [Fact l.Prime] {L : Loc} (G : Glob l L)

def inV (v : L.Vl) : (plOf G).ι := Sum.inl v

def inU (u : L.St) : (plOf G).ι := Sum.inr u

end UpperTheory.V.Pa.B2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.H2RightExactModLOfH3Subsingleton
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

section

variable {k G M : Type} [CommRing k] [Group G] [AddCommGroup M] [Module k M]

end

private theorem dn_two_apply' {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (rho : Representation R G M) (F : (Fin 2 → G) → M) (g : Fin 3 → G) :
    dn rho 2 F g = rho (g 0) (F ![g 1, g 2]) - F ![g 0 * g 1, g 2] + F ![g 0, g 1 * g 2] - F ![g 0, g 1] := by
  have e0 : (fun i : Fin 2 => g i.succ) = ![g 1, g 2] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x y : G => x * y) g = ![g 0 * g 1, g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e2 : Fin.contractNth 1 (fun x y : G => x * y) g = ![g 0, g 1 * g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e3 : Fin.contractNth 2 (fun x y : G => x * y) g = ![g 0, g 1] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.sum_univ_zero, e0, e1]
  norm_num
  rw [e2, e3]
  abel

private theorem dn_three_apply {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M]
    (rho : Representation R G M) (F : (Fin 3 → G) → M) (g : Fin 4 → G) :
    dn rho 3 F g = rho (g 0) (F ![g 1, g 2, g 3]) - F ![g 0 * g 1, g 2, g 3] + F ![g 0, g 1 * g 2, g 3]
      - F ![g 0, g 1, g 2 * g 3] + F ![g 0, g 1, g 2] := by
  have e0 : (fun i : Fin 3 => g i.succ) = ![g 1, g 2, g 3] := by
    funext i; fin_cases i <;> rfl
  have e1 : Fin.contractNth 0 (fun x y : G => x * y) g = ![g 0 * g 1, g 2, g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e2 : Fin.contractNth 1 (fun x y : G => x * y) g = ![g 0, g 1 * g 2, g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e3 : Fin.contractNth 2 (fun x y : G => x * y) g = ![g 0, g 1, g 2 * g 3] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  have e4 : Fin.contractNth 3 (fun x y : G => x * y) g = ![g 0, g 1, g 2] := by
    funext i; fin_cases i <;> simp [Fin.contractNth] <;> rfl
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_succ, Fin.sum_univ_zero, e0, e1]
  norm_num
  rw [e2, e3, e4]
  abel

theorem UpperTheory.V.Pa.B2.H2_right_exact_mod_l_of_H3_subsingleton :
    ∀ (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], (∀ (A : Type) [CommRing A] (M : FRep A G), (∀ m : M.X, l • m = 0) → Subsingleton (Hn M.ρ 3)) → SecondCohomologyRightExactModL l G := by
  intro l G _ _ _ h A _ M M' hl u hu hs
  intro x
  obtain ⟨c', rfl⟩ := Submodule.Quotient.mk_surjective _ x
  set s := Function.surjInv hs with hs_def
  have us : ∀ y, u (s y) = y := Function.surjInv_eq hs
  let c : G × G → M.X := fun p => s (c'.1 p)
  have hc : Continuous c := (continuous_of_discreteTopology (f := s)).comp c'.2.1
  let N : Submodule A M.X := LinearMap.ker u
  have hN : ∀ g : G, ∀ m ∈ N, M.ρ g m ∈ N := by
    intro g m hm
    simp only [N, LinearMap.mem_ker] at hm ⊢
    rw [hu, hm, map_zero]
  let ρK : Representation A G N :=
    { toFun := fun g => (M.ρ g).restrict (hN g)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro g g'
        ext m
        simp }
  have hcont : ContAction ρK :=
    continuous_induced_rng.2 (M.cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let K : FRep A G := FRep.mk N ρK hcont
  have hKl : ∀ m : K.X, l • m = 0 := by
    intro m
    exact Subtype.ext (hl m.1)
  have hsub := h A K hKl
  let C : (Fin 2 → G) → M.X := fun x => c (x 0, x 1)
  have hfN : ∀ g : Fin 3 → G, dn M.ρ 2 C g ∈ N := by
    intro g
    simp only [N, LinearMap.mem_ker]
    rw [dn_two_apply']
    simp only [C, c, map_sub, map_add (f := _), hu, us]
    simpa using c'.2.2 (g 0) (g 1) (g 2)
  let f : (Fin 3 → G) → N := fun g => ⟨dn M.ρ 2 C g, hfN g⟩
  have key : ∀ t : Fin 3 → G, ((f t : N) : M.X) =
      M.ρ (t 0) (c (t 1, t 2)) - c (t 0 * t 1, t 2) + c (t 0, t 1 * t 2) - c (t 0, t 1) := by
    intro t
    simp [f, dn_two_apply', C]
  have hρK : ∀ (a : G) (m : N), ((ρK a m : N) : M.X) = M.ρ a m := fun a m => rfl
  have hmul : ∀ (a b : G) (m : M.X), M.ρ a (M.ρ b m) = M.ρ (a * b) m := by
    intro a b m
    simp [map_mul]
  have fcont : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f) = fun t : Fin 3 → G =>
        M.ρ (t 0) (c (t 1, t 2)) - c (t 0 * t 1, t 2) + c (t 0, t 1 * t 2) - c (t 0, t 1) := funext key
    rw [e]
    have c0 := continuous_apply (A := fun _ : Fin 3 => G) 0
    have c1 := continuous_apply (A := fun _ : Fin 3 => G) 1
    have c2 := continuous_apply (A := fun _ : Fin 3 => G) 2
    exact (((M.cont.comp (c0.prodMk (hc.comp (c1.prodMk c2)))).sub
      (hc.comp ((c0.mul c1).prodMk c2))).add (hc.comp (c0.prodMk (c1.mul c2)))).sub
      (hc.comp (c0.prodMk c1))
  have fcyc : dn ρK 3 f = 0 := by
    funext g
    apply Subtype.ext
    rw [dn_three_apply]
    simp only [Submodule.coe_add, Submodule.coe_sub, hρK, key, Pi.zero_apply, ZeroMemClass.coe_zero,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_sub, map_add, hmul]
    simp only [mul_assoc]
    abel
  have fmem : f ∈ Zn K.ρ 3 := by
    refine Submodule.mem_inf.2 ⟨fcont, ?_⟩
    exact LinearMap.mem_ker.2 fcyc
  have h0 : (Submodule.Quotient.mk ⟨f, fmem⟩ : Hn K.ρ 3) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
  change f ∈ Submodule.map (dn ρK 2) (Cn ρK 2) at h0
  obtain ⟨b, hb, hbf⟩ := h0
  have hbc : Continuous b := hb
  have hv : Continuous fun p : G × G => ![p.1, p.2] := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  let c2 : G × G → M.X := fun p => c p - (b ![p.1, p.2] : M.X)
  have hc2 : c2 ∈ Z2 M.ρ := by
    refine ⟨hc.sub (continuous_subtype_val.comp (hbc.comp hv)), ?_⟩
    intro g g' g''
    have e := congrArg Subtype.val (congrFun hbf ![g, g', g''])
    rw [dn_two_apply'] at e
    simp only [Submodule.coe_add, Submodule.coe_sub, hρK, key, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at e
    simp only [c2, map_sub]
    calc _ = (M.ρ g (c (g', g'')) - c (g * g', g'') + c (g, g' * g'') - c (g, g'))
          - (M.ρ g (b ![g', g''] : M.X) - (b ![g * g', g''] : M.X) + (b ![g, g' * g''] : M.X)
            - (b ![g, g'] : M.X)) := by abel
      _ = 0 := by rw [e, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨c2, hc2⟩, ?_⟩
  simp only [mapH2, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  funext p
  show u (c2 p) = c'.1 p
  simp only [c2, c, map_sub, us, LinearMap.mem_ker.1 (b _).2, sub_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.DegSplit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem deg_split (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 (Lp L))) (w : HeightOneSpectrum (𝓞 L))
    (hA : IsPlaceOver A v) (hw : IsPlaceOver A w) (hv : ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal)
    (hsp : Dec (F := Lp L) A ≤ (resP L Ω).range) : locDeg w = locDeg v := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have hlw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
    have h1 := (hA ((l : ℕ) : 𝓞 (Lp L))).mpr hv
    apply (hw ((l : ℕ) : 𝓞 L)).mp
    simpa using h1
  obtain ⟨j, hj⟩ := (UpperTheory.V.Loc.decEmb (F := L) (Ω := Ω) (v := l)).1 A w hw hlw
  subst hj
  obtain ⟨-, φL, -, hφL, hrL, -, -, hiL⟩ := (UpperTheory.V.Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j
  obtain ⟨-, φP, -, hφP, hrP, -, -, hiP⟩ := (UpperTheory.V.Loc.decEmb (F := Lp L) (Ω := Ω) (v := l)).2 j
  rw [← hiL w hw, ← hiP v hA]
  congr 1
  ext σ
  constructor
  · intro hσ
    apply (hrP σ).mpr
    intro x
    rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
    exact (hrL σ).mp hσ _
  · intro hσ
    apply (hrL σ).mpr
    intro x
    obtain ⟨g, rfl⟩ := hσ
    obtain ⟨k, hk⟩ := hsp g.2
    rw [hφP]
    congr 1
    rw [← hk]
    exact k.commutes x

theorem UpperTheory.V.Pa.B2.arSum :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∑ v : (locOf r).Vl, locDeg (s.w (Subtype.val v)) = Module.finrank ℚ (Lp L) := by
  intro l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r
  have key : ∀ v : (locOf r).Vl, locDeg (s.w (Subtype.val v)) = locDeg (Subtype.val v) := fun v =>
    deg_split l L Ω (s.A v.1) v.1 (s.w v.1) (s.hA _) (s.hw _) v.2 (s.split _ (Or.inl v.2))
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  letI : Fintype {v : HeightOneSpectrum (𝓞 (Lp L)) // ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal} := (locOf r).finV
  have h := GlobalTheory.Proof.LocalDegreeSum.sum_locDeg (Lp L) l
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.AmMaps
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem quotient_multiplication_exact {R : Type} [CommRing R] [IsDomain R] (u v w : R) (hv : v ≠ 0)
    (hw : w = v * u) :
    ∃ (f : (R ⧸ Ideal.span {u}) →ₗ[R] (R ⧸ Ideal.span {w}))
      (g : (R ⧸ Ideal.span {w}) →ₗ[R] (R ⧸ Ideal.span {v})),
      Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧
      (∀ x, f (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (v * x)) ∧
      (∀ x, g (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x) := by
  subst hw
  have h1 : Ideal.span {u} ≤ Submodule.comap (LinearMap.mulLeft R v) (Ideal.span {v * u}) := by
    intro x hx
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    show v * (t * u) ∈ Ideal.span {v * u}
    rw [Ideal.mem_span_singleton]
    exact ⟨t, by ring⟩
  have h2 : Ideal.span {v * u} ≤ Submodule.comap (LinearMap.id : R →ₗ[R] R) (Ideal.span {v}) := by
    rw [Submodule.comap_id]
    exact Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right v u)
  let f := Submodule.mapQ (Ideal.span {u}) (Ideal.span {v * u}) (LinearMap.mulLeft R v) h1
  let g := Submodule.mapQ (Ideal.span {v * u}) (Ideal.span {v}) (LinearMap.id : R →ₗ[R] R) h2
  have hf : ∀ x, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (v * x) := fun x => rfl
  have hg : ∀ x, g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => rfl
  refine ⟨f, g, ?_, ?_, ?_, fun x => rfl, fun x => rfl⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      rw [hf, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at ha
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      exact (mul_dvd_mul_iff_left hv).mp ha
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [hg, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨Submodule.Quotient.mk t, hf t⟩
      · rintro ⟨a, ha⟩
        induction a using Submodule.Quotient.induction_on with
        | H t =>
          rw [hf, Submodule.Quotient.eq, Ideal.mem_span_singleton] at ha
          obtain ⟨s, hs⟩ := ha
          exact ⟨t - u * s, by linear_combination -hs⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, hg x⟩

theorem UpperTheory.V.Pa.B2.amMaps :
    ∀ (K : Type) [Field K] (e m : ℕ), e ≤ m → ∃ (f : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m - e)}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m})) (g : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ e})) (k : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ e}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m})) (r : (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) →ₗ[PowerSeries K] (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m - e)})), Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g ∧ Function.Injective k ∧ Function.Exact k r ∧ Function.Surjective r ∧ ∀ y, f (r y) = (PowerSeries.X : PowerSeries K) ^ e • y := by
  intro K _ e m h
  have hX : (PowerSeries.X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  obtain ⟨f, g, hfi, hfg, hgs, hf, -⟩ :=
    quotient_multiplication_exact ((PowerSeries.X : PowerSeries K) ^ (m - e)) (PowerSeries.X ^ e) (PowerSeries.X ^ m)
      (pow_ne_zero _ hX) (by rw [← pow_add, Nat.add_sub_cancel' h])
  obtain ⟨k, r, hki, hkr, hrs, -, hr⟩ :=
    quotient_multiplication_exact ((PowerSeries.X : PowerSeries K) ^ e) (PowerSeries.X ^ (m - e)) (PowerSeries.X ^ m)
      (pow_ne_zero _ hX) (by rw [← pow_add, Nat.sub_add_cancel h])
  refine ⟨f, g, k, r, hfi, hfg, hgs, hki, hkr, hrs, fun y => ?_⟩
  induction y using Submodule.Quotient.induction_on with
  | H x => exact (congrArg f (hr x)).trans (hf x)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.MapConj
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerSide
theorem UpperTheory.Reformulated.B.Qf12.lift_ex :
    ∀ {A M Q Q' : Type} [inst : CommRing A] [inst_1 : AddCommGroup M]
    [inst_2 : AddCommGroup Q] [inst_3 : AddCommGroup Q'] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module A Q]
    [inst_6 : _root_.Module A Q'] (π : M →ₗ[A] Q),
    Function.Surjective (⇑π : M → Q) →
      ∀ (g : M →ₗ[A] Q'),
        (∀ (m : M), (π : M → Q) m = (0 : Q) → (g : M → Q') m = (0 : Q')) →
          ∃ (q : Q →ₗ[A] Q'), ∀ (m : M), (q : Q → Q') ((π : M → Q) m) = (g : M → Q') m := by
  intro A M Q Q' _ _ _ _ _ _ _ π hπ g hg
  have hle : LinearMap.ker π ≤ LinearMap.ker g := fun m hm =>
    LinearMap.mem_ker.mpr (hg m (LinearMap.mem_ker.mp hm))
  refine ⟨((LinearMap.ker π).liftQ g hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun m => ?_⟩
  have h : (π.quotKerEquivOfSurjective hπ).symm (π m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]
end

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem map_conj {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] {n : ℕ}
    (u : X →ₗ[A] X') (P Q : Matrix (Fin n) (Fin n) A) (M : Matrix (Fin n) (Fin n) X) :
    (P.map (algebraMap A X) * M * Q.map (algebraMap A X)).map u =
      P.map (algebraMap A X') * M.map u * Q.map (algebraMap A X') := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  rw [mul_comm _ (algebraMap A X _), mul_comm _ (algebraMap A X' _), ← Algebra.smul_def, ← Algebra.smul_def,
    ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul]

private def odMap {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (n a : ℕ)
    (u : X →ₗ[A] X') : Od A X n a →ₗ[A] Od A X' n a where
  toFun M := ⟨(M : Matrix (Fin n) (Fin n) X).map u, fun i j => ⟨fun e => by
    have := (M.2 i j).1 e
    rw [Submodule.mem_bot] at this ⊢
    rw [Matrix.map_apply, this, map_zero], fun _ => Submodule.mem_top⟩⟩
  map_add' M N := by ext i j; simp
  map_smul' c M := by ext i j; simp

private theorem lift_ex {A M Q Q' : Type} [CommRing A] [AddCommGroup M] [AddCommGroup Q]
    [AddCommGroup Q'] [Module A M] [Module A Q] [Module A Q'] (π : M →ₗ[A] Q)
    (hπ : Function.Surjective π) (g : M →ₗ[A] Q') (hk : ∀ m, π m = 0 → g m = 0) :
    ∃ q : Q →ₗ[A] Q', ∀ m, q (π m) = g m :=
  _root_.UpperTheory.Reformulated.B.Qf12.lift_ex π hπ g hk

theorem UpperTheory.V.Pa.B2.odHom :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X' : Type) [CommRing X'] [Algebra x.A X'] (D D' : Dat x.A (plOf G)) (o : IsOd h x X D) (o' : IsOd h x X' D') (u : X →ₗ[x.A] X'), ∃ f : D.Hom D', Induced o o' u f := by
  intro l _ L G G0 h n x X _ _ X' _ _ D D' o o' u
  let f : D.M.X →ₗ[x.A] D'.M.X := o'.e.symm.toLinearMap ∘ₗ odMap n x.a u ∘ₗ o.e.toLinearMap
  have hf : ∀ m, (o'.e (f m) : Matrix (Fin n) (Fin n) X') = (o.e m : Matrix (Fin n) (Fin n) X).map u := fun m => by
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have h0 : ∀ (g : G.G₀) m, f (D.M.ρ g m) = D'.M.ρ g (f m) := fun g m => by
    apply o'.e.injective
    apply Subtype.ext
    rw [hf, o.act, o'.act, hf]
    exact map_conj u _ _ _
  have hc : ∀ m, f (D.M.ρ G.c m) = D'.M.ρ G.c (f m) := fun m => by
    apply o'.e.injective
    apply Subtype.ext
    rw [hf, o.actc, o'.actc, hf]
    ext i j
    simp
  have hall : ∀ (g : G.Γ) m, f (D.M.ρ g m) = D'.M.ρ g (f m) := fun g m => by
    rcases Int.units_eq_one_or (G.η g) with e | e
    · exact h0 ⟨g, e⟩ m
    · have hm : g * G.c ∈ G.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, e, G.η_c]; simp
      have eg : g * G.c * G.c = g := by rw [mul_assoc, G.c_sq, mul_one]
      have e1 := h0 ⟨g * G.c, hm⟩ (D.M.ρ G.c m)
      rw [hc, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul] at e1
      simpa only [eg] using e1
  have hk : ∀ w m, D.π w m = 0 → (D'.π w ∘ₗ f) m = 0 := by
    rintro (v | w) m hm
    · rw [LinearMap.comp_apply, o'.kerV]
      intro i j hij
      have e := congrFun (congrFun (map_conj u (((x.w v)⁻¹ : GL (Fin n) x.A) : Matrix (Fin n) (Fin n) x.A)
        (x.w v : Matrix (Fin n) (Fin n) x.A) (o.e m : Matrix (Fin n) (Fin n) X)) i) j
      rw [hf]
      refine e.symm.trans ?_
      have := (o.kerV v m).1 hm i j hij
      rw [Matrix.map_apply]
      exact (congrArg u this).trans (map_zero u)
    · have : m = 0 := o.kerU w (hm.trans (map_zero _).symm)
      rw [this, map_zero]
  choose q hq using fun w => lift_ex (D.π w) (D.surj w) (D'.π w ∘ₗ f) (hk w)
  exact ⟨⟨f, q, hall, hq⟩, hf⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CohAxIso
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

noncomputable section

namespace UpperTheory.V.Pa.B2

section Pull

variable {A Γ Γ' : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']

private def pull (p : Γ →* Γ') (hp : Continuous p) (M : FRep A Γ') : FRep A Γ where
  X := M.X
  ρ := M.ρ.comp p
  cont := M.cont.comp (hp.prodMap continuous_id)

variable (p : Γ ≃* Γ') (hp : Continuous p) (hq : Continuous p.symm) (M : FRep A Γ')

private def r1 : H1 M.ρ →ₗ[A] H1 (pull p.toMonoidHom hp M).ρ :=
  pairH1DecompositionMap M.ρ (pull p.toMonoidHom hp M).ρ p.toMonoidHom hp LinearMap.id continuous_id fun _ _ => rfl

private def r2 : H2 M.ρ →ₗ[A] H2 (pull p.toMonoidHom hp M).ρ :=
  compatiblePairH2 M.ρ (pull p.toMonoidHom hp M).ρ p.toMonoidHom hp LinearMap.id continuous_id fun _ _ => rfl

private theorem back (g : Γ') (m : M.X) : (pull p.toMonoidHom hp M).ρ (p.symm g) m = M.ρ g m := by
  show M.ρ (p.toMonoidHom (p.symm g)) m = M.ρ g m
  simp

include hq in
private theorem restriction_one_bijective : Function.Bijective (r1 p hp M) := by
  let s : H1 (pull p.toMonoidHom hp M).ρ →ₗ[A] H1 M.ρ :=
    pairH1DecompositionMap (pull p.toMonoidHom hp M).ρ M.ρ p.symm.toMonoidHom hq LinearMap.id continuous_id
      fun g m => back p hp M g m
  refine Function.bijective_iff_has_inverse.mpr ⟨s, fun x => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r1, pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (p.apply_symm_apply g)
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r1, pairH1DecompositionMap, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (p.symm_apply_apply g)

include hq in
private theorem restriction_two_bijective : Function.Bijective (r2 p hp M) := by
  let s : H2 (pull p.toMonoidHom hp M).ρ →ₗ[A] H2 M.ρ :=
    compatiblePairH2 (pull p.toMonoidHom hp M).ρ M.ρ p.symm.toMonoidHom hq LinearMap.id continuous_id
      fun g m => back p hp M g m
  refine Function.bijective_iff_has_inverse.mpr ⟨s, fun x => ?_, fun x => ?_⟩
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r2, compatiblePairH2, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (Prod.ext (p.apply_symm_apply g.1) (p.apply_symm_apply g.2))
  · obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [s, r2, compatiblePairH2, Submodule.mapQ_apply]
    congr 1
    ext g
    exact congrArg z.1 (Prod.ext (p.symm_apply_apply g.1) (p.symm_apply_apply g.2))

private theorem card_H0_pullback_eq : Nat.card (H0 (pull p.toMonoidHom hp M).ρ) = Nat.card (H0 M.ρ) := by
  have e : H0 (pull p.toMonoidHom hp M).ρ = H0 M.ρ := by
    ext m
    simp only [H0, Representation.mem_invariants]
    constructor
    · intro h g
      rw [← back p hp M g m]
      exact h _
    · intro h g
      exact h (p g)
  rw [e]
  rfl

include hp hq in
private theorem finH_iso (l : ℕ) (h : FinH l Γ) : FinH l Γ' := by
  intro A _ M hl
  obtain ⟨h1, h2⟩ := h A (pull p.toMonoidHom hp M) hl
  exact ⟨Finite.of_equiv _ (Equiv.ofBijective _ (restriction_one_bijective p hp hq M)).symm,
    Finite.of_equiv _ (Equiv.ofBijective _ (restriction_two_bijective p hp hq M)).symm⟩

include hp hq in
private theorem onto_iso (l : ℕ) (h : SecondCohomologyRightExactModL l Γ) : SecondCohomologyRightExactModL l Γ' := by
  intro A _ M M' hl u hu hs y
  have hu' : ∀ (g : Γ) (m : (pull p.toMonoidHom hp M).X),
      u ((pull p.toMonoidHom hp M).ρ g m) = (pull p.toMonoidHom hp M').ρ g (u m) :=
    fun g m => hu (p g) m
  have key : ∀ x, r2 p hp M' (mapH2 M.ρ M'.ρ u continuous_of_discreteTopology hu x) =
      mapH2 (pull p.toMonoidHom hp M).ρ (pull p.toMonoidHom hp M').ρ u continuous_of_discreteTopology hu'
        (r2 p hp M x) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [r2, compatiblePairH2, mapH2, Submodule.mapQ_apply]
    rfl
  obtain ⟨x', hx'⟩ := h A (pull p.toMonoidHom hp M) (pull p.toMonoidHom hp M') hl u hu' hs (r2 p hp M' y)
  obtain ⟨x, rfl⟩ := (restriction_two_bijective p hp hq M).2 x'
  refine ⟨x, (restriction_two_bijective p hp hq M').1 ?_⟩
  rw [key, hx']

end Pull

section Gl

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (e : G.Hom G') {A : Type} [CommRing A]

private theorem pl_φ (w : (plOf G).ι) (g : (plOf G).G w) : e.p ((plOf G).φ w g) = (plOf G').φ w g := by
  cases w with
  | inl v => exact e.φ v g
  | inr u => exact e.φu u g

private def pullD (D : Dat A (plOf G')) : Dat A (plOf G) where
  M := pull e.p e.cont D.M
  Q w := D.Q w
  π w := D.π w
  surj w := D.surj w
  equiv w g m := by
    have h := D.equiv w g m
    rw [← pl_φ e w g] at h
    exact h

end Gl

end UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.cohAxIso :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G' : Glob l L) (e : G.Hom G') (d : ℕ) (dv : L.Vl → ℕ), Function.Injective e.p → CohAx G d dv → CohAx G' d dv := by
  intro l _ L G G' e d dv hinj hG
  haveI : T2Space G'.Γ := inferInstance
  let q : G.Γ ≃* G'.Γ := MulEquiv.ofBijective e.p ⟨hinj, e.surj⟩
  have hq : Continuous q := e.cont
  have hqs : Continuous q.symm :=
    (Continuous.homeoOfEquivCompactToT2 (f := q.toEquiv) e.cont).symm.continuous
  refine ⟨hG.sum, finH_iso q hq hqs l hG.fin, hG.finV, hG.finU, onto_iso q hq hqs l hG.onto, ?_,
    hG.leV, hG.leU, hG.ur, ?_⟩
  · obtain ⟨c, hc, hf⟩ := hG.ge
    refine ⟨fun i => e.p (c i), fun i => ⟨by rw [e.η]; exact (hc i).1, by rw [← map_mul, (hc i).2, map_one]⟩, ?_⟩
    intro A _ M hl
    have h := hf A (pull q.toMonoidHom hq M) hl
    rw [card_H0_pullback_eq] at h
    rw [Nat.card_congr (Equiv.ofBijective _ (restriction_two_bijective q hq hqs M)),
      Nat.card_congr (Equiv.ofBijective _ (restriction_one_bijective q hq hqs M))]
    exact h
  · intro A _ D hl
    have h := hG.ck A (pullD e D) hl
    have hc : ∀ x, D.loc2 x = (pullD e D).loc2 (r2 q hq D.M x) := by
      intro x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      funext w
      simp only [Dat.loc2, LinearMap.pi_apply, r2, compatiblePairH2, Submodule.mapQ_apply]
      congr 1
      ext y
      show D.π w (z.1 ((plOf G').φ w y.1, (plOf G').φ w y.2)) =
        D.π w (z.1 (e.p ((plOf G).φ w y.1), e.p ((plOf G).φ w y.2)))
      rw [pl_φ e w y.1, pl_φ e w y.2]
    have hr : (pullD e D).loc2.range = D.loc2.range := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨x0, rfl⟩ := (restriction_two_bijective q hq hqs D.M).2 x
        exact ⟨x0, hc x0⟩
      · rintro ⟨x, rfl⟩
        exact ⟨r2 q hq D.M x, (hc x).symm⟩
    have h1 : Nat.card (pullD e D).Ck2 = Nat.card D.Ck2 := by
      show Nat.card (_ ⧸ (pullD e D).loc2.range) = Nat.card (_ ⧸ D.loc2.range)
      rw [hr]
      rfl
    rw [← h1]
    refine h.trans (le_of_eq (Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)))
    constructor
    · intro hf g m
      obtain ⟨g0, rfl⟩ := e.surj g
      rw [e.ε]
      exact hf g0 m
    · intro hf g m
      have := hf (e.p g) m
      rw [e.ε] at this
      exact this
end
end
