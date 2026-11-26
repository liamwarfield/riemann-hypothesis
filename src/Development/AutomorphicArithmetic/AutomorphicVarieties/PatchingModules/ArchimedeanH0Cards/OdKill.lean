module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.EvIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.odKill_char (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] :
    (l : K) = 0 := by
  obtain ⟨q, hq⟩ := CharP.exists K
  haveI := hq
  have hx : (q : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (CharP.char_ne_zero_of_finite K q)
  have h1 := congrArg (algebraMap ℤ_[l] K) (PadicInt.unitCoeff_spec hx)
  rw [map_natCast, CharP.cast_eq_zero, map_mul, map_pow, map_natCast] at h1
  have hu : algebraMap ℤ_[l] K (PadicInt.unitCoeff hx : ℤ_[l]) ≠ 0 :=
    ((PadicInt.unitCoeff hx).isUnit.map (algebraMap ℤ_[l] K)).ne_zero
  exact pow_eq_zero_iff'.mp ((mul_eq_zero.mp h1.symm).resolve_left hu) |>.1

theorem UpperTheory.V.Pa.B2.odKill :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (D : Dat x.A (plOf G)), IsOd h x X D → (∀ m : D.M.X, l • m = 0) ∧ (∀ w, ∀ m : (D.Q w).X, l • m = 0) ∧ ∀ u, ∀ g ∈ L.Ju u, ∀ m : (D.Q (inU G u)).X, (D.Q (inU G u)).ρ g m = m := by
  intro l _ L G G0 h n x X _ _ D hD
  have hlA : (l : x.A) = 0 := by
    show (l : PowerSeries x.K) = 0
    rw [← map_natCast (algebraMap x.K (PowerSeries x.K)) l, odKill_char l x.K, map_zero]
  refine ⟨fun m => ?_, fun w m => ?_, fun u g hg m => ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]
  · rw [← Nat.cast_smul_eq_nsmul x.A, hlA, zero_smul]
  · obtain ⟨m', rfl⟩ := D.surj (inU G u) m
    refine (D.equiv (inU G u) g m').symm.trans ?_
    congr 1
    let g' : G.G₀ := G.φu u g
    have hp : h.p₀ g' = G0.φu u g := Subtype.ext (by exact h.φu u g)
    have hmem : h.p₀ g' ∈ G0.frame.Iu u := by
      rw [hp]
      exact Subgroup.mem_map_of_mem _ hg
    have h1 : x.ρ (h.p₀ g') = 1 := x.ine u _ hmem
    have h2 : x.ρ (h.p₀ g'⁻¹) = 1 := by rw [map_inv h.p₀, map_inv x.ρ, h1, inv_one]
    apply hD.e.injective
    apply Subtype.ext
    show ((hD.e (D.M.ρ (g' : G.Γ) m')) : Matrix (Fin n) (Fin n) X) = hD.e m'
    rw [hD.act g' m']
    show ((x.ρ (h.p₀ g') : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) * _ *
      ((x.ρ (h.p₀ g'⁻¹) : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) = _
    rw [h1, h2, Units.val_one]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardOfAddEquiv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.card_of_addEquiv {X Y : Type} {_ : Add X} {_ : Add Y} (e : X ≃+ Y) :
    Nat.card X = Nat.card Y ∧ (Finite Y → Finite X) :=
  ⟨Nat.card_congr e.toEquiv, fun _ => Finite.of_injective e e.injective⟩

theorem UpperTheory.V.Pa.B2.arLoc :
    CohP → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (B : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver B v → FinH l (Dec (F := F) B) ∧ SecondCohomologyRightExactModL l (Dec (F := F) B) ∧ ((((l : ℕ) : 𝓞 F) ∈ v.asIdeal → LocE l (Dec (F := F) B) (locDeg v)) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → LocE l (Dec (F := F) B) 0)) := by
  intro hP F Ω _ _ _ _ _ l _ B v hB
  have key : ∀ (A : Type) [CommRing A] (M : FRep A (Dec (F := F) B)), (∀ m : M.X, l • m = 0) →
      (Finite (H1 M.ρ) ∧ Finite (H2 M.ρ)) ∧
      ((((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
        Nat.card (H1 M.ρ) = Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ locDeg v) ∧
       (((l : ℕ) : 𝓞 F) ∉ v.asIdeal →
        Nat.card (H1 M.ρ) = Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ 0)) := by
    intro A _ M hl
    letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (fun m => by rw [pow_one]; exact hl m)
    obtain ⟨hc, ⟨e0⟩, ⟨e1, -⟩, ⟨e2, -⟩⟩ := scal A _ M (l ^ 1)
    have hf := hP.lf F Ω l 1 M.X B (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) v one_pos hB hc
    have he := hP.le F Ω l 1 M.X B (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) v one_pos hB hc
    have c0 : Nat.card (H0 M.ρ) = Nat.card (H0 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e0).1
    have c1 : Nat.card (H1 M.ρ) = Nat.card (H1 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e1).1
    have c2 : Nat.card (H2 M.ρ) = Nat.card (H2 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
      (card_of_addEquiv e2).1
    rw [c0, c1, c2, pow_zero, mul_one]
    have f1 : Finite (H1 M.ρ) := (card_of_addEquiv e1).2 hf.2.1
    have f2 : Finite (H2 M.ρ) := (card_of_addEquiv e2).2 hf.2.2.1
    exact ⟨⟨f1, f2⟩, he⟩
  refine ⟨fun A _ M hl => (key A M hl).1, H2_right_exact_mod_l_of_H3_subsingleton l _ fun A _ M hl => ?_,
    fun h A _ M hl => (key A M hl).2.1 h, fun h A _ M hl => (key A M hl).2.2 h⟩
  exact (GlobalTheory.Published.cohDimTwoLocal_of_localFiniteness hP.lf).of_nsmul l 1
    (fun m => by rw [pow_one]; exact hl m) M.ρ hB M.cont 3 le_rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ContOfKer
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem cont_of_ker {A Γ M : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module A M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation A Γ M)
    (hk : ∀ᶠ g in nhds (1 : Γ), ∀ m, ρ g m = m) : ContAction ρ := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  rw [ContinuousAt, nhds_discrete M, Filter.tendsto_pure]
  have hg : ∀ᶠ g in nhds p.1, ∀ m, ρ g m = ρ p.1 m := by
    have ht : Filter.Tendsto (fun g => p.1⁻¹ * g) (nhds p.1) (nhds 1) := by
      simpa using (continuous_const_mul p.1⁻¹).tendsto p.1
    filter_upwards [ht.eventually hk] with g hg m
    calc ρ g m = ρ p.1 (ρ (p.1⁻¹ * g) m) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ p.1 m := by rw [hg m]
  have hm : ∀ᶠ q : Γ × M in nhds p, q.2 = p.2 := by
    have h0 : ∀ᶠ m in nhds p.2, m = p.2 := by
      rw [nhds_discrete, Filter.eventually_pure]
    exact (continuous_snd.tendsto p).eventually h0
  filter_upwards [(continuous_fst.tendsto p).eventually hg, hm] with q h1 h2
  rw [h1, h2]

private theorem ev_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (m : ℕ) (hm : algebraMap x.A X (x.t ^ m) = 0) :
    ∀ᶠ g in nhds (1 : F.G₀), x.ρX X g = 1 := by
  have key : ∀ a b : x.A, Ideal.Quotient.mk (IsLocalRing.maximalIdeal (PowerSeries x.K) ^ m) a =
      Ideal.Quotient.mk _ b → algebraMap x.A X a = algebraMap x.A X b := by
    intro a b hab
    rw [Ideal.Quotient.eq, PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hab
    obtain ⟨c, hc⟩ := hab
    rw [← sub_eq_zero, ← map_sub, hc, map_mul, hm, zero_mul]
  have hij : ∀ i j : Fin n, ∀ᶠ g in nhds (1 : F.G₀), x.ρX X g i j = (1 : Matrix (Fin n) (Fin n) X) i j := by
    intro i j
    have hl := x.cont i j m
    filter_upwards [(hl.isOpen_fiber _).mem_nhds (Set.mem_singleton _)] with g hg
    have hg' := key _ _ hg
    simp only [NP.ρX, Matrix.map_apply]
    rw [hg']
    simp [mat, Matrix.one_apply]
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (hij i)] with g hg
  exact Matrix.ext hg

private theorem tri_X {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) (g : F.Gv v) :
    (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v).BlockTriangular id := by
  intro i j hij
  have h := (x.tri v g).1 i j hij
  simp only [NP.wiX, NP.ρX, NP.wX, mat, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
  rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, ← Units.val_mul, ← Units.val_mul, h, map_zero]

private theorem w_wi {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) : x.wX X v * x.wiX X v = 1 := by
  simp only [NP.wX, NP.wiX]
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

private def triSub {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n : ℕ}
    (V : Submodule A (Matrix (Fin n) (Fin n) X)) (a b : Matrix (Fin n) (Fin n) X) : Submodule A V where
  carrier := {Z | (a * (Z : Matrix (Fin n) (Fin n) X) * b).BlockTriangular id}
  zero_mem' := by
    intro i j _
    simp
  add_mem' := by
    intro Z Z' h h' i j hij
    have e1 := h hij
    have e2 := h' hij
    simp only [Submodule.coe_add, mul_add, add_mul, Matrix.add_apply, e1, e2, add_zero]
  smul_mem' := by
    intro c Z h i j hij
    have e1 := h hij
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, e1, smul_zero]

theorem UpperTheory.V.Pa.B2.odEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] [Finite X], (∃ m : ℕ, algebraMap x.A X (x.t ^ m) = 0) → ∃ D : Dat x.A (plOf G), Nonempty (IsOd h x X D) := by
  intro l _ L G G0 h n x X _ _ _ hX
  obtain ⟨m, hm⟩ := hX
  obtain ⟨-, hok⟩ := okX l L G G0 h n x X 1
  obtain ⟨rep, hrep⟩ := adEx l G.frame x.A X n (fun g => x.ρX X (h.p₀ g))
    (fun g => algebraMap x.A X ((1 : G.Γ →* x.A) g)) (Od x.A X n x.a) hok
  have hact : ∀ (g : G.G₀) (Z : Od x.A X n x.a),
      ((rep g Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) =
        x.ρX X (h.p₀ g) * Z * x.ρX X (h.p₀ g⁻¹) := by
    intro g Z
    rw [hrep.1 g Z]
    simp
  have hc : ∀ Z : Od x.A X n x.a, ((rep G.c Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) = -(Z : Matrix (Fin n) (Fin n) X)ᵀ := by
    intro Z
    rw [hrep.2 Z]
    simp
  letI : TopologicalSpace (Od x.A X n x.a) := ⊥
  haveI : DiscreteTopology (Od x.A X n x.a) := ⟨rfl⟩
  haveI : Finite (Od x.A X n x.a) := inferInstance
  have hp : Continuous h.p₀ := continuous_induced_rng.2 (h.cont.comp continuous_subtype_val)
  have hcont : ContAction rep := by
    apply cont_of_ker
    have E := ev_one x X m hm
    have E1 : ∀ᶠ g in nhds (1 : G.G₀), x.ρX X (h.p₀ g) = 1 := by
      have := (hp.tendsto 1).eventually (by simpa using E)
      exact this
    have E2 : ∀ᶠ g in nhds (1 : G.G₀), x.ρX X (h.p₀ g⁻¹) = 1 := by
      have ht : Filter.Tendsto (fun g : G.G₀ => g⁻¹) (nhds 1) (nhds 1) := by
        simpa using (continuous_inv.tendsto (1 : G.G₀))
      exact ht.eventually E1
    have E3 := E1.and E2
    rw [show (1 : G.G₀) = ⟨1, G.η.ker.one_mem⟩ from rfl, nhds_subtype_eq_comap, Filter.eventually_comap] at E3
    filter_upwards [E3, G.η_open.mem_nhds G.η.ker.one_mem] with g hg hker Z
    obtain ⟨h1, h2⟩ := hg ⟨g, hker⟩ rfl
    apply Subtype.ext
    have := hact ⟨g, hker⟩ Z
    rw [h1, h2, Matrix.one_mul, Matrix.mul_one] at this
    exact this
  let M : FRep x.A G.Γ := ⟨Od x.A X n x.a, rep, hcont⟩
  let N : (plOf G).ι → Submodule x.A M.X :=
    Sum.elim (fun v => triSub (Od x.A X n x.a) (x.wiX X v) (x.wX X v)) (fun _ => ⊥)
  have hN : ∀ (w : (plOf G).ι) (g : (plOf G).G w), N w ≤ Submodule.comap (M.ρ ((plOf G).φ w g)) (N w) := by
    intro w g
    cases w with
    | inl v =>
      change L.Gv v at g
      intro Z hZ
      have hZ' : (x.wiX X v * (Z : Matrix (Fin n) (Fin n) X) * x.wX X v).BlockTriangular id := hZ
      show (x.wiX X v * ((rep ((G.φ v g : G.G₀) : G.Γ) Z : Od x.A X n x.a) : Matrix (Fin n) (Fin n) X) * x.wX X v).BlockTriangular id
      have e1 : h.p₀ (G.φ v g) = G0.frame.φ v g := Subtype.ext (h.φ v g)
      have e2 : h.p₀ (G.φ v g)⁻¹ = G0.frame.φ v g⁻¹ := by
        rw [map_inv h.p₀, e1]
        exact (map_inv (G0.frame.φ v) g).symm
      rw [hact, e1, e2]
      have hww := w_wi x X v
      have heq : x.wiX X v * (x.ρX X (G0.frame.φ v g) * (Z : Matrix (Fin n) (Fin n) X) * x.ρX X (G0.frame.φ v g⁻¹)) * x.wX X v =
          (x.wiX X v * x.ρX X (G0.frame.φ v g) * x.wX X v) * (x.wiX X v * (Z : Matrix (Fin n) (Fin n) X) * x.wX X v) *
            (x.wiX X v * x.ρX X (G0.frame.φ v g⁻¹) * x.wX X v) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (x.wX X v) (x.wiX X v), hww, Matrix.one_mul,
          ← Matrix.mul_assoc (x.wX X v) (x.wiX X v), hww, Matrix.one_mul]
      rw [heq]
      exact ((tri_X x X v g).mul hZ').mul (tri_X x X v g⁻¹)
    | inr u =>
      intro Z hZ
      have hZ0 : Z = 0 := (Submodule.mem_bot _).1 hZ
      simp [N, hZ0]
  refine ⟨Dat.ofSub (plOf G) M N hN, ⟨⟨LinearEquiv.refl _ _, fun g m => hact g m, fun m => hc m, ?_, ?_⟩⟩⟩
  · intro v m
    exact (Submodule.Quotient.mk_eq_zero (N (Sum.inl v)) (x := (m : M.X))).trans
      ⟨fun hb i j hij => hb hij, fun hb i j hij => hb i j hij⟩
  · intro u a b hab
    have hab' := (Submodule.Quotient.eq (N (Sum.inr u)) (x := (a : M.X)) (y := b)).1 hab
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hab')
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArGlob
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arGlob :
    CohP → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Set (HeightOneSpectrum (𝓞 F))), l ≠ 2 → S.Finite → (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → FinH l (GS Ω S) ∧ SecondCohomologyRightExactModL l (GS Ω S) := by
  intro hP F Ω _ _ _ _ _ l _ S hl hS hab
  obtain ⟨T, rfl⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S = ↑T := ⟨hS.toFinset, by simp⟩
  have key : ∀ (A : Type) [CommRing A] (M : FRep A (GS Ω (T : Set (HeightOneSpectrum (𝓞 F))))),
      (∀ m : M.X, l • m = 0) → Finite (H1 M.ρ) ∧ Finite (H2 M.ρ) ∧ Subsingleton (Hn M.ρ 3) := by
    intro A _ M hM
    letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (by simpa using hM)
    obtain ⟨hc, -, ⟨e1, -⟩, ⟨e2, -⟩⟩ := UpperTheory.V.Pa.B2.scal A _ M (l ^ 1)
    obtain ⟨-, h1, h2, h3⟩ := hP.gf F Ω l 1 M.X T (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) one_pos
      (fun v hv => hab v hv) hc
    exact ⟨Finite.of_equiv _ e1.symm.toEquiv, Finite.of_equiv _ e2.symm.toEquiv,
      GlobalTheory.Published.subsingleton_Hn_of_action_eq M.ρ (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)
        (fun _ _ => rfl) 3 (by omega) (h3 hl 3 le_rfl)⟩
  exact ⟨fun A _ M hM => ⟨(key A M hM).1, (key A M hM).2.1⟩,
    UpperTheory.V.Pa.B2.H2_right_exact_mod_l_of_H3_subsingleton l _ fun A _ M hM => (key A M hM).2.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArchH0Card
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem UpperTheory.V.Pa.B2.ge_real (hE : GlobalEulerChar) (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F]
    [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Set (HeightOneSpectrum (𝓞 F)))
    (hf : S.Finite) (hS : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S)
    (c : InfinitePlace F → G F Ω) (hc : ∀ w, IsCCAt w (c w))
    (A : Type) [CommRing A] (M : FRep A (GS Ω S)) (hM : ∀ m : M.X, l • m = 0) :
    Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ Module.finrank ℚ F =
      Nat.card (H1 M.ρ) * ∏ w, Nat.card {m : M.X // M.ρ (toGS Ω S (c w)) m = m} := by
  classical
  obtain ⟨S, rfl⟩ := hf.exists_finset_coe
  letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (by simpa using hM)
  obtain ⟨hρ, -, ⟨e1, -⟩, e2, -⟩ := UpperTheory.V.Pa.B2.scal A _ M (l ^ 1)
  have h := hE F Ω l 1 M.X S (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) one_pos (fun v hv => hS v hv) hρ c fun w _ => hc w
  rw [archH0Card, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero, mul_one,
    Finset.filter_true_of_mem fun w _ => IsTotallyReal.isReal w] at h
  have c0 : Nat.card (H0 M.ρ) = Nat.card (H0 (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [c0, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]
  exact h

theorem UpperTheory.V.Pa.B2.arGE :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n), ∃ c : Fin (Module.finrank ℚ (Lp L)) → (globOf r V).Γ, (∀ i, (globOf r V).η (c i) = -1 ∧ c i * c i = 1) ∧ ∀ (A : Type) [CommRing A] (M : FRep A (globOf r V).Γ), (∀ m : M.X, l • m = 0) → Nat.card (H0 M.ρ) * Nat.card (H2 M.ρ) * Nat.card M.X ^ Module.finrank ℚ (Lp L) = Nat.card (H1 M.ρ) * ∏ i, Nat.card {m : M.X // M.ρ (c i) m = m} := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 V O _ _ _ _ _ n r
  obtain ⟨h1, h2⟩ := UpperTheory.V.Pa.ccEx l L Ω
  choose c hc using h1
  have hcard : Fintype.card (InfinitePlace (Lp L)) = Module.finrank ℚ (Lp L) := by
    rw [IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  let e : Fin (Module.finrank ℚ (Lp L)) ≃ InfinitePlace (Lp L) := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => toGS Ω V.S' (c (e i)), fun i => ?_, fun A _ M hM => ?_⟩
  · obtain ⟨j, hj, -⟩ := hc (e i)
    obtain ⟨a1, a2, -⟩ := h2 _ ⟨j, hj⟩
    refine ⟨(Int.units_eq_one_or (V.η (toGS Ω V.S' (c (e i))))).resolve_left fun h => a2 ((V.hη _).1 h), ?_⟩
    exact (map_mul (toGS Ω V.S') _ _).symm.trans (by rw [a1, map_one]; rfl)
  · have h := UpperTheory.V.Pa.B2.ge_real hP.ge (Lp L) Ω l V.S' V.fin (fun v hv => V.sub (Or.inl hv)) c hc A M hM
    rw [← Equiv.prod_comp e] at h
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArUr
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardKerRangeAlt
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem card_ker_range {A V W : Type} [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (f : V →ₗ[A] W) : Nat.card V = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]

private def Zu {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (M : FRep A G) (J : Subgroup G) :
    Submodule A (G → M.X) where
  carrier := {z | z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0}
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨add_mem a1 b1, fun g hg => by rw [Pi.add_apply, a2 g hg, b2 g hg, add_zero]⟩
  smul_mem' := by
    rintro c a ⟨a1, a2⟩
    exact ⟨Submodule.smul_mem _ c a1, fun g hg => by rw [Pi.smul_apply, a2 g hg, smul_zero]⟩

private theorem card_Zu {l : ℕ} [Fact l.Prime] {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (h : UnrCount l G J) (M : FRep A G) (hl : ∀ m : M.X, l • m = 0) (hJ : ∀ g ∈ J, ∀ m, M.ρ g m = m) :
    Finite (Zu M J) ∧ Nat.card (Zu M J) = Nat.card M.X := by
  have hLC : LC M.ρ := by
    intro m
    rw [IsLocallyConstant.iff_continuous]
    exact M.cont.comp (continuous_id.prodMk continuous_const)
  have hJ' : ∀ g ∈ J, M.ρ g = 1 := fun g hg => LinearMap.ext (hJ g hg)
  obtain ⟨hfin, hcard⟩ := h A M.X M.ρ hLC hl hJ'
  have hset : ((Zu M J : Submodule A (G → M.X)) : Set (G → M.X)) =
      {z | z ∈ Zl M.ρ ∧ ∀ g ∈ J, z g = 0} := by
    ext z
    show (z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0) ↔ _
    rw [mem_Z1_iff_cocycle, Set.mem_setOf_eq, mem_Zl, IsLocallyConstant.iff_continuous]
  have e : (Zu M J) ≃ {z | z ∈ Zl M.ρ ∧ ∀ g ∈ J, z g = 0} := Set.equivOfEq hset
  refine ⟨?_, ?_⟩
  · haveI := hfin.to_subtype
    exact Finite.of_equiv _ e.symm
  · rw [Nat.card_congr e, Nat.card_coe_set_eq, hcard]

private def kerRep {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (M M' : FRep A G) (u : M.X →ₗ[A] M'.X)
    (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m)) : FRep A G where
  X := LinearMap.ker u
  ρ := Representation.subrepresentation M.ρ (LinearMap.ker u) (fun g m hm => by
    show u (M.ρ g m) = 0
    rw [hu, LinearMap.mem_ker.1 hm, map_zero])
  cont := Continuous.subtype_mk (M.cont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _

private theorem comp_mem_Zu_of_equivariant {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M M' : FRep A G) (u : M.X →ₗ[A] M'.X) (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m))
    (z : G → M.X) (hz : z ∈ Zu M J) : (fun g => u (z g)) ∈ Zu M' J := by
  have hz' : z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0 := hz
  have hzc := (mem_Z1_iff_cocycle _ _).1 hz'.1
  show (fun g => u (z g)) ∈ Z1 M'.ρ ∧ ∀ g ∈ J, (fun g => u (z g)) g = 0
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · exact (continuous_of_discreteTopology (f := u)).comp hzc.1
  · intro g h
    simp only [hzc.2 g h, map_add (f := _), hu]
  · intro g hg
    simp only [hz'.2 g hg, map_zero]

private theorem d0_mem_Zu_of_trivial_on {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M : FRep A G) (hJ : ∀ g ∈ J, ∀ m, M.ρ g m = m) (m : M.X) : d0 M.ρ m ∈ Zu M J := by
  have hd : ∀ g, d0 M.ρ m g = M.ρ g m - m := fun g => rfl
  show d0 M.ρ m ∈ Z1 M.ρ ∧ ∀ g ∈ J, d0 M.ρ m g = 0
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · have hc : Continuous fun g => M.ρ g m := M.cont.comp (continuous_id.prodMk continuous_const)
    exact (hc.sub continuous_const).congr (fun g => (hd g).symm)
  · intro g h
    rw [hd, hd, hd, map_sub, map_mul, Module.End.mul_apply]
    abel
  · intro g hg
    rw [hd, hJ g hg, sub_self]

private theorem ker_restrict_mem_Zu_of_comp_zero {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] {J : Subgroup G}
    (M M' : FRep A G) (u : M.X →ₗ[A] M'.X) (hu : ∀ g m, u (M.ρ g m) = M'.ρ g (u m))
    (z : G → M.X) (hz : z ∈ Zu M J) (hk : ∀ g, u (z g) = 0) :
    (fun g => (⟨z g, LinearMap.mem_ker.2 (hk g)⟩ : LinearMap.ker u)) ∈ Zu (kerRep M M' u hu) J := by
  have hz' : z ∈ Z1 M.ρ ∧ ∀ g ∈ J, z g = 0 := hz
  have hzc := (mem_Z1_iff_cocycle _ _).1 hz'.1
  show _ ∈ Z1 (kerRep M M' u hu).ρ ∧ _
  refine ⟨(mem_Z1_iff_cocycle _ _).2 ⟨?_, ?_⟩, ?_⟩
  · exact hzc.1.subtype_mk _
  · intro g h
    exact Subtype.ext (hzc.2 g h)
  · intro g hg
    exact Subtype.ext (hz'.2 g hg)

theorem UpperTheory.V.Pa.B2.urOf :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), UnrCount l G J → UrAx l J := by
  intro l _ G _ _ _ J h
  unfold UrAx
  intro A _ M hl hJ
  have memZu : ∀ {N : FRep A G} {z : G → N.X}, z ∈ Zu N J ↔ z ∈ Z1 N.ρ ∧ ∀ g ∈ J, z g = 0 :=
    Iff.rfl
  obtain ⟨hfin, hcZ⟩ := card_Zu h M hl hJ
  refine ⟨?_, ?_⟩
  · have hZ : Zu M J ≤ Z1 M.ρ := fun z hz => (memZu.1 hz).1
    have hres : ∀ w : Z1 M.ρ, resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk (restrictCocycles1 M.ρ J.subtype continuous_subtype_val w) := fun w => rfl
    let φ0 : Zu M J →ₗ[A] H1 M.ρ := (Submodule.mkQ _) ∘ₗ Submodule.inclusion hZ
    have hφ0 : ∀ z, φ0 z ∈ H1ur M.ρ J := by
      intro z
      rw [H1ur, LinearMap.mem_ker]
      show resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk (Submodule.inclusion hZ z)) = 0
      rw [hres]
      have hz0 : restrictCocycles1 M.ρ J.subtype continuous_subtype_val (Submodule.inclusion hZ z) = 0 :=
        Subtype.ext (funext fun x => (memZu.1 z.2).2 x x.2)
      rw [hz0, Submodule.Quotient.mk_zero]
    let φ : Zu M J →ₗ[A] H1ur M.ρ J := φ0.codRestrict _ hφ0
    let d : M.X →ₗ[A] Zu M J := (d0 M.ρ).codRestrict _ (d0_mem_Zu_of_trivial_on M hJ)
    have hsurj : Function.Surjective φ := by
      rintro ⟨c, hc⟩
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      rw [H1ur, LinearMap.mem_ker] at hc
      change resH1 M.ρ J.subtype continuous_subtype_val (Submodule.Quotient.mk w) = 0 at hc
      rw [hres, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hc
      obtain ⟨m, hm⟩ := hc
      have hwJ : ∀ g ∈ J, w.1 g = 0 := by
        intro g hg
        have hh := hm ⟨g, hg⟩
        simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hJ g hg, sub_self] at hh
        exact hh
      refine ⟨⟨w.1, memZu.2 ⟨w.2, hwJ⟩⟩, ?_⟩
      apply Subtype.ext
      rfl
    have hker : LinearMap.ker d = H0 M.ρ := by
      ext m
      rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
      constructor
      · intro hm g
        have hh : M.ρ g m - m = 0 := congrArg (fun z : Zu M J => z.1 g) hm
        exact sub_eq_zero.1 hh
      · intro hm
        apply Subtype.ext
        funext g
        exact (sub_eq_zero.2 (hm g) : M.ρ g m - m = 0)
    have hrange : LinearMap.range d = LinearMap.ker φ := by
      ext z
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨m, rfl⟩
        apply Subtype.ext
        show (Submodule.Quotient.mk (Submodule.inclusion hZ (d m)) : H1 M.ρ) = 0
        apply (Submodule.Quotient.mk_eq_zero (Submodule.comap (Z1 M.ρ).subtype (B1 M.ρ))).2
        show d0 M.ρ m ∈ B1 M.ρ
        exact (mem_coboundaries1 _ _).2 ⟨m, fun g => rfl⟩
      · intro hz
        have hz2 : (Submodule.Quotient.mk (Submodule.inclusion hZ z) : H1 M.ρ) = 0 :=
          congrArg Subtype.val hz
        have hB : z.1 ∈ B1 M.ρ :=
          (Submodule.Quotient.mk_eq_zero (Submodule.comap (Z1 M.ρ).subtype (B1 M.ρ))).1 hz2
        obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hB
        exact ⟨m, Subtype.ext (funext fun g => (hm g).symm)⟩
    have hrφ : Nat.card (LinearMap.range φ) = Nat.card (H1ur M.ρ J) := by
      rw [LinearMap.range_eq_top.2 hsurj]
      exact Nat.card_congr Submodule.topEquiv.toEquiv
    haveI := hfin
    have e1 := card_ker_range d
    have e2 := card_ker_range φ
    rw [hker, hrange] at e1
    rw [hrφ, hcZ, e1] at e2
    have hpos : 0 < Nat.card (LinearMap.ker φ) := Nat.card_pos
    rw [mul_comm] at e2
    exact (Nat.eq_of_mul_eq_mul_left hpos e2).le
  · intro M' u hu hsu y' hy' hy'J
    have hl' : ∀ m : M'.X, l • m = 0 := by
      intro m
      obtain ⟨x, rfl⟩ := hsu m
      rw [← map_nsmul, hl, map_zero]
    have hJ' : ∀ g ∈ J, ∀ m : M'.X, M'.ρ g m = m := by
      intro g hg m
      obtain ⟨x, rfl⟩ := hsu m
      rw [← hu, hJ g hg]
    obtain ⟨hfin', hcZ'⟩ := card_Zu h M' hl' hJ'
    let K := kerRep M M' u hu
    have hlK : ∀ m : K.X, l • m = 0 := fun m => Subtype.ext (hl m.1)
    have hJK : ∀ g ∈ J, ∀ m : K.X, K.ρ g m = m := fun g hg m => Subtype.ext (hJ g hg m.1)
    obtain ⟨-, hcZK⟩ := card_Zu h K hlK hJK
    let ψ : Zu M J →ₗ[A] Zu M' J := ((u.compLeft G) ∘ₗ (Zu M J).subtype).codRestrict _
      (fun z => comp_mem_Zu_of_equivariant M M' u hu z.1 z.2)
    let ι : Zu K J →ₗ[A] Zu M J := (((LinearMap.ker u).subtype.compLeft G) ∘ₗ (Zu K J).subtype).codRestrict _
      (fun w => comp_mem_Zu_of_equivariant K M (LinearMap.ker u).subtype (fun g m => rfl) w.1 w.2)
    have hιinj : Function.Injective ι := by
      intro a b hab
      apply Subtype.ext
      funext g
      exact Subtype.ext (congrArg (fun z : Zu M J => z.1 g) hab)
    have hιr : LinearMap.range ι = LinearMap.ker ψ := by
      ext z
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨w, rfl⟩
        apply Subtype.ext
        funext g
        exact LinearMap.mem_ker.1 (w.1 g).2
      · intro hz
        have hk : ∀ g, u (z.1 g) = 0 := fun g => congrArg (fun y : Zu M' J => y.1 g) hz
        exact ⟨⟨_, ker_restrict_mem_Zu_of_comp_zero M M' u hu z.1 z.2 hk⟩, Subtype.ext rfl⟩
    have hcM : Nat.card M.X = Nat.card K.X * Nat.card M'.X := by
      have e := card_ker_range u
      rw [LinearMap.range_eq_top.2 hsu, Nat.card_congr Submodule.topEquiv.toEquiv] at e
      exact e
    have e2 := card_ker_range ψ
    rw [← hιr, Nat.card_congr (LinearEquiv.ofInjective ι hιinj).symm.toEquiv, hcZ, hcZK, hcM] at e2
    have hposK : 0 < Nat.card K.X := Nat.card_pos
    have hrψ : Nat.card (LinearMap.range ψ) = Nat.card (Zu M' J) := by
      rw [hcZ']
      exact (Nat.eq_of_mul_eq_mul_left hposK e2).symm
    haveI := hfin'
    have htop : (LinearMap.range ψ).toAddSubgroup = ⊤ := AddSubgroup.eq_top_of_card_eq _ hrψ
    have hmem : (⟨y', memZu.2 ⟨hy', hy'J⟩⟩ : Zu M' J) ∈ LinearMap.range ψ := by
      have hh : (⟨y', memZu.2 ⟨hy', hy'J⟩⟩ : Zu M' J) ∈ (LinearMap.range ψ).toAddSubgroup := by
        rw [htop]
        exact AddSubgroup.mem_top _
      exact hh
    obtain ⟨z, hz⟩ := LinearMap.mem_range.1 hmem
    exact ⟨z.1, (memZu.1 z.2).1, (memZu.1 z.2).2, fun g => congrArg (fun y : Zu M' J => y.1 g) hz⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arUr :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (u : (locOf r).St), UrAx l ((locOf r).Ju u) := by
  intro _ l _ L Ω _ _ _ _ _ _ s V0 _ O _ _ _ _ _ n r u
  exact UpperTheory.V.Pa.B2.urOf l _ _ (UpperTheory.V.Pa.unrLoc l L Ω s V0 O n r u)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.H0LocalCardBoundedOfClsKerLeKer
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem kill_low {X : Type} [CommRing X] {n : ℕ} (Z : Matrix (Fin n) (Fin n) X) (d : X)
    (H : ∀ i j, j < i → ∃ B B' : Matrix (Fin n) (Fin n) X, (∀ i j, j < i → B i j = 0) ∧ (∀ i j, j < i → B' i j = 0) ∧
      (B * Z * B') i j = Z i j ∧ B i i * B' j j - 1 ∣ d) (k : ℕ) :
    ∀ i j : Fin n, j < i → n + (j : ℕ) ≤ k + i → d ^ k * Z i j = 0 := by
  induction k with
  | zero =>
    intro i j _ hk
    have := i.isLt
    omega
  | succ k ih =>
    intro i j hij hk
    obtain ⟨B, B', hB, hB', heq, hdvd⟩ := H i j hij
    obtain ⟨c, hc⟩ := hdvd
    have key : d ^ k * (B * Z * B') i j = d ^ k * (B i i * Z i j * B' j j) := by
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
      · intro a _ ha
        rcases lt_or_gt_of_ne ha with h | h
        · simp [hB i a h]
        · have h1 := Fin.lt_iff_val_lt_val.mp h
          have h2 := Fin.lt_iff_val_lt_val.mp hij
          have hz := ih a j (lt_trans hij h) (by omega)
          calc d ^ k * (B i a * Z a j * B' j j) = B i a * (d ^ k * Z a j) * B' j j := by ring
            _ = 0 := by rw [hz]; ring
      · simp
      · intro b _ hb
        apply Finset.sum_eq_zero
        intro a _
        rcases lt_or_gt_of_ne hb with h | h
        · rcases lt_or_ge a i with ha | ha
          · simp [hB i a ha]
          · have hba : b < a := lt_of_lt_of_le (lt_trans h hij) ha
            have h1 := Fin.lt_iff_val_lt_val.mp h
            have h2 := Fin.le_iff_val_le_val.mp ha
            have hz := ih a b hba (by omega)
            calc d ^ k * (B i a * Z a b * B' b j) = B i a * (d ^ k * Z a b) * B' b j := by ring
              _ = 0 := by rw [hz]; ring
        · simp [hB' b j h]
      · simp
    rw [heq] at key
    linear_combination (d ^ k * Z i j) * hc - c * key

private theorem fin_quot (K : Type) [Field K] [Finite K] (s : ℕ) :
    Finite (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ s}) := by
  classical
  haveI : Finite (Polynomial.degreeLT K s) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv K s).toEquiv.symm
  refine Finite.of_surjective (fun q : Polynomial.degreeLT K s =>
    Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ s}) ((q : Polynomial K) : PowerSeries K)) ?_
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨⟨PowerSeries.trunc s p, Polynomial.mem_degreeLT.mpr (PowerSeries.degree_trunc_lt p s)⟩, ?_⟩
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro m hm
  simp [PowerSeries.coeff_trunc, hm]

private theorem fin_quot' (K : Type) [Field K] [Finite K] (a : PowerSeries K) (ha : a ≠ 0) :
    Finite (PowerSeries K ⧸ Ideal.span {a}) := by
  have hu : IsUnit (PowerSeries.divXPowOrder a) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact isUnit_iff_ne_zero.mpr (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr ha)
  have hspan : Ideal.span {a} = Ideal.span {(PowerSeries.X : PowerSeries K) ^ a.order.toNat} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    have h := associated_mul_unit_left ((PowerSeries.X : PowerSeries K) ^ a.order.toNat) _ hu
    rwa [PowerSeries.X_pow_order_mul_divXPowOrder] at h
  rw [hspan]
  exact fin_quot K _

private theorem ann_card {A : Type} [CommRing A] (I : Ideal A) [Finite (A ⧸ I)] (a : A) [Finite (A ⧸ Ideal.span {a})] :
    Nat.card {y : A ⧸ I // algebraMap A (A ⧸ I) a * y = 0} ≤ Nat.card (A ⧸ Ideal.span {a}) := by
  classical
  let f : (A ⧸ I) →ₗ[A] (A ⧸ I) := LinearMap.lsmul A (A ⧸ I) a
  have e1 : Nat.card {y : A ⧸ I // algebraMap A (A ⧸ I) a * y = 0} = Nat.card (LinearMap.ker f) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      simp [f, LinearMap.mem_ker, Algebra.smul_def])
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 : Nat.card ((A ⧸ I) ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have h5 : Nat.card (LinearMap.ker f) = Nat.card ((A ⧸ I) ⧸ LinearMap.range f) := by
    have h6 := h1.symm.trans h2
    rw [h3, mul_comm] at h6
    exact Nat.eq_of_mul_eq_mul_left hpos h6
  let g : A →ₗ[A] (A ⧸ I) ⧸ LinearMap.range f :=
    (LinearMap.range f).mkQ ∘ₗ Algebra.linearMap A (A ⧸ I)
  have hg : Ideal.span {a} ≤ LinearMap.ker g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    simp only [g, LinearMap.comp_apply, Submodule.mkQ_apply, Algebra.linearMap_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨1, by simp [f, Algebra.smul_def]⟩
  have hs : Function.Surjective ((Ideal.span {a}).liftQ g hg) := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective m
    exact ⟨Submodule.Quotient.mk b, by rw [Submodule.liftQ_apply]; rfl⟩
  rw [e1, h5]
  exact Nat.card_le_card_of_surjective _ hs

private theorem low_ann {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) :
    ∃ a : x.A, a ≠ 0 ∧ ∀ (X : Type) [CommRing X] [Algebra x.A X] (v : F.Vl) (M : Matrix (Fin n) (Fin n) X),
      (∀ g i j, j < i → (x.wiX X v * (x.ρX X (F.φ v g) * M * x.ρX X (F.φ v g)⁻¹ - M) * x.wX X v) i j = 0) →
      ∀ i j, j < i → algebraMap x.A X a * (x.wiX X v * M * x.wX X v) i j = 0 := by
  classical
  have hne : ∀ (v : F.Vl) (i j : Fin n), i ≠ j → ∃ g : F.Gv v, x.ψ v i g ≠ x.ψ v j g := by
    intro v i j hij
    by_contra hc
    push_neg at hc
    exact (x.N1 v).1 i j hij (MonoidHom.ext hc)
  let fac : F.Vl → Fin n → Fin n → PowerSeries x.K := fun v i j =>
    if h : i = j then 1 else
      ((x.ψ v i (Classical.choose (hne v i j h)) : PowerSeries x.K) *
        (x.ψ v j (Classical.choose (hne v i j h))⁻¹ : PowerSeries x.K) - 1)
  have hfac : ∀ v i j, fac v i j ≠ 0 := by
    intro v i j
    simp only [fac]
    split_ifs with hij
    · exact one_ne_zero
    · rw [sub_ne_zero]
      intro h1
      apply Classical.choose_spec (hne v i j hij)
      have h2 : x.ψ v i (Classical.choose (hne v i j hij)) *
          (x.ψ v j (Classical.choose (hne v i j hij)))⁻¹ = 1 := by
        apply Units.ext
        rw [Units.val_mul, Units.val_one, ← map_inv]
        exact h1
      exact mul_inv_eq_one.mp h2
  let d0 : PowerSeries x.K := ∏ v, ∏ i, ∏ j, fac v i j
  have hd0 : d0 ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mpr fun j _ => hfac v i j
  refine ⟨d0 ^ n, pow_ne_zero n hd0, ?_⟩
  intro X _ _ v M hM i j hij
  have hw : x.wX X v * x.wiX X v = 1 := by
    show ((x.w v : Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) *
      (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)).map
        (algebraMap x.A X) = 1
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    simp
  have hBeq : ∀ g : F.Gv v, x.wiX X v * x.ρX X (F.φ v g) * x.wX X v =
      ((((x.w v)⁻¹ * x.ρ (F.φ v g) * x.w v : GL (Fin n) (PowerSeries x.K)) :
        Matrix (Fin n) (Fin n) (PowerSeries x.K))).map (algebraMap x.A X) := by
    intro g
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  have hup : ∀ (g : F.Gv v) (i' j' : Fin n), j' < i' →
      (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v) i' j' = 0 := by
    intro g i' j' h
    rw [hBeq g, Matrix.map_apply, (x.tri v g).1 i' j' h, map_zero]
  have hdg : ∀ (g : F.Gv v) (i' : Fin n),
      (x.wiX X v * x.ρX X (F.φ v g) * x.wX X v) i' i' = algebraMap x.A X (x.ψ v i' g) := by
    intro g i'
    rw [hBeq g, Matrix.map_apply, (x.tri v g).2 i']
  have H : ∀ i j : Fin n, j < i → ∃ B B' : Matrix (Fin n) (Fin n) X,
      (∀ i j, j < i → B i j = 0) ∧ (∀ i j, j < i → B' i j = 0) ∧
      (B * (x.wiX X v * M * x.wX X v) * B') i j = (x.wiX X v * M * x.wX X v) i j ∧
      B i i * B' j j - 1 ∣ algebraMap x.A X d0 := by
    intro i j hij
    have hij' : i ≠ j := ne_of_gt hij
    set g := Classical.choose (hne v i j hij') with hg
    refine ⟨x.wiX X v * x.ρX X (F.φ v g) * x.wX X v, x.wiX X v * x.ρX X (F.φ v g⁻¹) * x.wX X v,
      hup g, hup g⁻¹, ?_, ?_⟩
    · have hc : x.wiX X v * x.ρX X (F.φ v g) * x.wX X v * (x.wiX X v * M * x.wX X v) *
          (x.wiX X v * x.ρX X (F.φ v g⁻¹) * x.wX X v) =
          x.wiX X v * x.ρX X (F.φ v g) * (x.wX X v * x.wiX X v) * M * (x.wX X v * x.wiX X v) *
            x.ρX X (F.φ v g⁻¹) * x.wX X v := by
        simp only [Matrix.mul_assoc]
      rw [hc, hw]
      have h3 := hM g i j hij
      rw [← map_inv (F.φ v) g, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, sub_eq_zero] at h3
      rw [← h3]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    · rw [hdg g i, hdg g⁻¹ j, ← map_mul, ← map_one (algebraMap x.A X), ← map_sub]
      apply map_dvd
      have hf : fac v i j = (x.ψ v i g : PowerSeries x.K) * (x.ψ v j g⁻¹ : PowerSeries x.K) - 1 := by
        simp only [fac, dif_neg hij']
        rfl
      rw [← hf]
      exact (Finset.dvd_prod_of_mem (fun j => fac v i j) (Finset.mem_univ j)).trans
        ((Finset.dvd_prod_of_mem (fun i => ∏ j, fac v i j) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun v => ∏ i, ∏ j, fac v i j) (Finset.mem_univ v)))
  have hji := Fin.lt_iff_val_lt_val.mp hij
  have key := kill_low (x.wiX X v * M * x.wX X v) (algebraMap x.A X d0) H n i j hij (by omega)
  rw [map_pow]
  exact key

theorem UpperTheory.V.Pa.B2.H0_local_card_bounded_of_cls_ker_le_ker :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n), ∃ C : ℕ, ∀ (G : Glob l L) (h : G.Hom G0) (e : ℕ) (D : Dat x.A (plOf G)), IsOd h x (x.Am e) D → ∀ v, Nat.card (H0 (D.Q (inV G v)).ρ) ≤ Nat.card x.K ^ C := by
  intro l _ L G0 n x
  obtain ⟨a, ha, hann⟩ := low_ann x
  haveI hfa : Finite (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) := fin_quot' x.K a ha
  refine ⟨Nat.card (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) ^ (n * n), ?_⟩
  intro G h e D hD v
  haveI hfe : Finite (PowerSeries x.K ⧸ Ideal.span {(PowerSeries.X : PowerSeries x.K) ^ e}) :=
    fin_quot x.K e
  haveI hfe' : Finite (x.Am e) := hfe
  let w := inV G v
  let Zm : D.M.X → Matrix (Fin n) (Fin n) (x.Am e) := fun m =>
    x.wiX (x.Am e) v * (hD.e m : Matrix (Fin n) (Fin n) (x.Am e)) * x.wX (x.Am e) v
  have hker : ∀ m, D.π w m = 0 ↔ ∀ i j : Fin n, j < i → Zm m i j = 0 := fun m => hD.kerV v m
  have hZsub : ∀ m1 m2, Zm (m1 - m2) = Zm m1 - Zm m2 := by
    intro m1 m2
    simp only [Zm, map_sub, Submodule.coe_sub, Matrix.mul_sub, Matrix.sub_mul]
  have hannm : ∀ m, D.π w m ∈ ReciprocityTheory.Gal.H0 (D.Q w).ρ →
      ∀ i j : Fin n, j < i → algebraMap x.A (x.Am e) a * Zm m i j = 0 := by
    intro m hq i j hij
    apply hann (x.Am e) v (hD.e m : Matrix (Fin n) (Fin n) (x.Am e)) _ i j hij
    intro g i' j' hij'
    let g' : G.G₀ := G.φ v g
    have hp : h.p₀ g' = G0.frame.φ v g := Subtype.ext (by exact h.φ v g)
    have hinv : (G0.frame.φ v g)⁻¹ = h.p₀ g'⁻¹ := by rw [map_inv, hp]
    have hzero : D.π w (D.M.ρ (g' : G.Γ) m - m) = 0 := by
      rw [map_sub, sub_eq_zero]
      have h2 := D.equiv w g m
      exact h2.trans ((ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).mp hq g)
    have h1 := (hD.kerV v (D.M.ρ (g' : G.Γ) m - m)).mp hzero i' j' hij'
    rw [map_sub, Submodule.coe_sub, hD.act g' m] at h1
    rw [hinv, ← hp]
    exact h1
  have hch : ∀ q : ReciprocityTheory.Gal.H0 (D.Q w).ρ, D.π w (Classical.choose (D.surj w q)) = q :=
    fun q => Classical.choose_spec (D.surj w q)
  let S := {y : x.Am e // algebraMap x.A (x.Am e) a * y = 0}
  let φ : ReciprocityTheory.Gal.H0 (D.Q w).ρ → (Fin n → Fin n → S) := fun q i j =>
    if hij : j < i then
      ⟨Zm (Classical.choose (D.surj w q)) i j,
        hannm _ (by rw [hch q]; exact q.2) i j hij⟩
    else ⟨0, by simp⟩
  have hinj : Function.Injective φ := by
    intro q1 q2 hq
    apply Subtype.ext
    rw [← hch q1, ← hch q2, ← sub_eq_zero, ← map_sub, hker, hZsub]
    intro i j hij
    have h3 := congrArg (fun f => ((f i j : S) : x.Am e)) hq
    simp only [φ, dif_pos hij] at h3
    rw [Matrix.sub_apply, h3, sub_self]
  have hK : 1 < Nat.card x.K := Finite.one_lt_card
  calc Nat.card (ReciprocityTheory.Gal.H0 (D.Q (inV G v)).ρ) ≤ Nat.card (Fin n → Fin n → S) :=
        Nat.card_le_card_of_injective φ hinj
    _ = Nat.card S ^ (n * n) := by simp [Nat.card_fun, ← pow_mul]
    _ ≤ Nat.card (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) ^ (n * n) :=
        Nat.pow_le_pow_left (ann_card (Ideal.span {(PowerSeries.X : PowerSeries x.K) ^ e}) a) _
    _ ≤ Nat.card x.K ^ (Nat.card (PowerSeries x.K ⧸ Ideal.span {(a : PowerSeries x.K)}) ^ (n * n)) :=
        (Nat.lt_pow_self hK).le
end
