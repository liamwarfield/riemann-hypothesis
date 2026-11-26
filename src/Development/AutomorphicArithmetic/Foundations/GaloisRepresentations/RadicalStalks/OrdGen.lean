module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Point
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.KsCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.DualZeroOfSpan
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.Factor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirection

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.NotLeSpanImage
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private lemma not_le_span_image {k P : Type*} [Field k] [AddCommGroup P] [Module k P] [FiniteDimensional k P]
    (G : Submodule k P) (A : P →+ P) (q : ℕ) (hq : 0 < q) (hA : ∀ (l : k) x, A (l • x) = l ^ q • A x)
    (v : P) (hv : v ∈ G) (hv0 : v ≠ 0) (hAv : A v = 0) :
    ¬ G ≤ Submodule.span k (A '' G) := by
  intro hle
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual k P, ℓ v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 ((Module.forall_dual_apply_eq_zero_iff k v).1 h)
  let K : Submodule k P := G ⊓ LinearMap.ker ℓ
  have hKG : K < G := by
    refine lt_of_le_of_ne inf_le_left fun h => hℓ ?_
    have : v ∈ K := h ▸ hv
    exact this.2
  let b := Module.finBasis k K
  let t : Fin (Module.finrank k K) → P := fun i => A (b i : P)
  have hAK : ∀ y ∈ K, A y ∈ Submodule.span k (Set.range t) := by
    intro y hy
    have e : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : P) := by
      have h : ((∑ i, b.repr ⟨y, hy⟩ i • b i : K) : P) = y := by rw [b.sum_repr]
      rw [Submodule.coe_sum] at h
      simpa only [Submodule.coe_smul] using h.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span k (A '' G) ≤ Submodule.span k (Set.range t) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    let l : k := ℓ g / ℓ v
    have hy : g - l • v ∈ K := by
      refine ⟨G.sub_mem hg (G.smul_mem _ hv), ?_⟩
      simp [l, hℓ]
    have e : A g = A (g - l • v) := by
      rw [map_sub, hA, hAv, smul_zero, sub_zero]
    rw [SetLike.mem_coe, e]
    exact hAK _ hy
  have h1 : Module.finrank k G ≤ Module.finrank k (Submodule.span k (Set.range t)) :=
    Submodule.finrank_mono (hle.trans hspan)
  have h2 : Module.finrank k (Submodule.span k (Set.range t)) ≤ Module.finrank k K := by
    have := finrank_range_le_card (R := k) t
    simpa [Set.finrank] using this
  have h3 := Submodule.finrank_lt_finrank_of_lt hKG
  omega

private lemma sub_smul_pow (p : ℕ) [Fact p.Prime] {k P : Type*} [Field k] [CharP k p] [AddCommGroup P] [Module k P]
    (T : Module.End k P) (l : k) (n : ℕ) : (T - l • 1) ^ (p ^ n) = T ^ (p ^ n) - (l ^ (p ^ n)) • 1 := by
  have h : ((Polynomial.X - Polynomial.C l) ^ (p ^ n) : Polynomial k) =
      Polynomial.X ^ (p ^ n) - Polynomial.C (l ^ (p ^ n)) := by
    rw [sub_pow_char_pow, Polynomial.C_pow]
  have := congrArg (Polynomial.aeval T) h
  simpa [Algebra.algebraMap_eq_smul_one, smul_pow] using this

private lemma pow_card_subring {k : Type*} [Field k] (R : Subring k) [Finite R] (x : R) : x ^ Nat.card R = x := by
  classical
  letI := Fintype.ofFinite R
  letI : Field R := Fintype.fieldOfDomain R
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

private lemma eig_of_gen (p : ℕ) [Fact p.Prime] {k P : Type*} [Field k] [CharP k p] [AddCommGroup P] [Module k P]
    (T : Module.End k P) (l : k) (f : ℕ) (hf : 0 < f) (hl : l ^ (p ^ f) = l) (y : P)
    (hy : y ∈ T.maxGenEigenspace l) (hT : (T ^ (p ^ f)) y = T y) : T y = l • y := by
  obtain ⟨n, hn⟩ := Module.End.mem_maxGenEigenspace _ _ _ |>.1 hy
  set N : Module.End k P := T - l • 1 with hN
  have hq : 2 ≤ p ^ f := by
    calc 2 ≤ p := (Fact.out : p.Prime).two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf
  have hNq : (N ^ (p ^ f)) y = N y := by
    rw [hN, sub_smul_pow p, hl]
    simp [hT]
  have hit : ∀ j : ℕ, (N ^ (j * (p ^ f - 1) + 1)) y = N y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (j + 1) * (p ^ f - 1) + 1 = j * (p ^ f - 1) + p ^ f := by
        have : p ^ f - 1 + 1 = p ^ f := by omega
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc, this]
      rw [e, pow_add, Module.End.mul_apply, hNq, ← Module.End.mul_apply, ← pow_succ, ih]
  have hz : N y = 0 := by
    rw [← hit n]
    have e : n * (p ^ f - 1) + 1 = (n * (p ^ f - 1) + 1 - n) + n := by
      have : n ≤ n * (p ^ f - 1) := Nat.le_mul_of_pos_right n (by omega)
      omega
    rw [e, pow_add, Module.End.mul_apply, hn, map_zero]
  have : T y - l • y = 0 := by simpa [hN] using hz
  exact sub_eq_zero.1 this

private lemma exists_not_mem {k C P : Type*} [Field k] [IsAlgClosed k] [CommRing C] [AddCommGroup P] [Module k P]
    [FiniteDimensional k P] (ρ : C →+* Module.End k P) (χ : C →+* k) (q : ℕ) (hq : 0 < q) (A : P →+ P)
    (hsemi : ∀ (l : k) x, A (l • x) = l ^ q • A x) (hcomm : ∀ c x, A (ρ c x) = ρ c (A x))
    (hfix : ∀ c, χ c ^ q = χ c) (hinj : Function.Injective fun x : k => x ^ q) (ε a g : C)
    (hε : ρ ε * ρ ε = ρ ε) (hε1 : χ ε = 1) (hnil : ∃ e : ℕ, ρ a ^ e * ρ ε = 0)
    (annG : ∀ x, ρ g x = 0 → ∃ u v, x = ρ a u + ρ (1 - ε) v)
    (v : P) (hv0 : v ≠ 0) (hv : ∀ c, ρ c v = χ c • v) (hAv : A v = 0) :
    ∃ u ∈ ⨅ c, (ρ c).maxGenEigenspace (χ c), ρ g u ∉ (Submodule.span k (Set.range A)).map (ρ g) := by
  classical
  let U : (C → k) → Submodule k P := fun ψ => ⨅ d, (ρ d).maxGenEigenspace (ψ d)
  let G : Submodule k P := U χ
  let H : Submodule k P := ⨆ ψ : {ψ : C → k // ψ ≠ χ}, U ψ
  have hc : ∀ x y, Commute (ρ x) (ρ y) := fun x y => by
    show ρ x * ρ y = ρ y * ρ x
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps : ∀ i j m0, Set.MapsTo (ρ i) ((ρ j).maxGenEigenspace m0) ((ρ j).maxGenEigenspace m0) :=
    fun i j m0 => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) m0
  have hind : iSupIndep U :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun x => ρ x) hmaps
  have htop : ⨆ ψ, U ψ = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun x => ρ x) hmaps
      (fun i => Module.End.iSup_maxGenEigenspace_eq_top (ρ i))
  have hUH : ∀ ψ : C → k, ψ ≠ χ → U ψ ≤ H := fun ψ h =>
    le_iSup (fun ψ : {ψ : C → k // ψ ≠ χ} => U ψ) ⟨ψ, h⟩
  have hsup : G ⊔ H = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun ψ => ?_
    by_cases h : ψ = χ
    · subst h; exact le_sup_left
    · exact le_sup_of_le_right (hUH ψ h)
  have hdisj : Disjoint G H :=
    (hind χ).mono_right (iSup_le fun ψ => le_iSup₂_of_le (f := fun j (_ : j ≠ ⇑χ) => U j) ψ.1 ψ.2 le_rfl)
  have hρU : ∀ c ψ, ∀ x ∈ U ψ, ρ c x ∈ U ψ := by
    intro c ψ x hx
    simp only [U, Submodule.mem_iInf] at hx ⊢
    exact fun d => hmaps c d _ (hx d)
  have hρH : ∀ c, ∀ x ∈ H, ρ c x ∈ H := by
    intro c x hx
    have hle : H ≤ H.comap (ρ c) := iSup_le fun ψ y hy => hUH ψ.1 ψ.2 (hρU c ψ.1 y hy)
    exact hle hx
  have hAU : ∀ ψ : C → k, ∀ x ∈ U ψ, A x ∈ U (fun c => ψ c ^ q) := by
    intro ψ x hx
    simp only [U, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace] at hx ⊢
    intro d
    obtain ⟨n, hn⟩ := hx d
    refine ⟨n, ?_⟩
    have step : ∀ (n : ℕ) y, ((ρ d - (ψ d ^ q) • 1) ^ n) (A y) = A (((ρ d - ψ d • 1) ^ n) y) := by
      intro n
      induction n with
      | zero => intro y; simp
      | succ n ih =>
        intro y
        have e : (ρ d - (ψ d ^ q) • 1) (A y) = A ((ρ d - ψ d • 1) y) := by
          simp [hcomm, hsemi, map_sub]
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, e, ih]
    rw [step, hn, map_zero]
  have hAG : ∀ x ∈ G, A x ∈ G := by
    intro x hx
    have := hAU χ x hx
    have e : (fun c => χ c ^ q) = ⇑χ := funext hfix
    rwa [e] at this
  have hAH : ∀ x ∈ H, A x ∈ H := by
    intro x hx
    refine Submodule.iSup_induction (fun ψ : {ψ : C → k // ψ ≠ χ} => U ψ) (motive := fun x => A x ∈ H) hx ?_ ?_ ?_
    · intro ψ y hy
      refine hUH _ ?_ (hAU ψ.1 y hy)
      intro h
      refine ψ.2 (funext fun c => hinj ?_)
      show ψ.1 c ^ q = χ c ^ q
      rw [hfix, ← congrFun h c]
    · simp
    · intro y z hy hz
      rw [map_add (f := _)]
      exact H.add_mem hy hz
  have hεG : ∀ x ∈ G, ρ ε x = x := by
    have aux : ∀ (n : ℕ) (x : P), ((ρ ε - (1 : k) • 1) ^ n) x = 0 → ρ ε x = x := by
      intro n
      induction n with
      | zero => intro x hx; simp at hx; simp [hx]
      | succ n ih =>
        intro x hx
        rw [pow_succ, Module.End.mul_apply] at hx
        have h1 := ih _ hx
        have h2 : ρ ε (ρ ε x) = ρ ε x := by rw [← Module.End.mul_apply, hε]
        simp only [one_smul, LinearMap.sub_apply, Module.End.one_apply, map_sub, h2, sub_self] at h1
        exact sub_eq_zero.1 h1.symm
    intro x hx
    have h := (Submodule.mem_iInf _).1 hx ε
    rw [hε1] at h
    obtain ⟨n, hn⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 h
    exact aux n x hn
  have h1εG : ∀ x ∈ G, ρ (1 - ε) x = 0 := by
    intro x hx
    simp [map_sub, hεG x hx]
  let Wd : Submodule k P := Submodule.span k (A '' G)
  have hWG : Wd ≤ G := Submodule.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hAG x hx)
  have haW : ∀ x ∈ Wd, ρ a x ∈ Wd := by
    intro x hx
    have hle : Wd ≤ Wd.comap (ρ a) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      show ρ a (A y) ∈ Wd
      rw [← hcomm]
      exact Submodule.subset_span ⟨_, hρU a χ y hy, rfl⟩
    exact hle hx
  have hvG : v ∈ G := by
    refine (Submodule.mem_iInf _).2 fun c => (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, ?_⟩
    simp [hv]
  by_contra hno
  push_neg at hno
  have hS : Submodule.span k (Set.range A) ≤ Wd ⊔ H := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ G ⊔ H := hsup ▸ Submodule.mem_top
    obtain ⟨z1, h1, z2, h2, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨z1, h1, rfl⟩) (hAH z2 h2)
  have hstep : ∀ u ∈ G, ∃ w ∈ Wd, ∃ u' ∈ G, u = w + ρ a u' := by
    intro u hu
    obtain ⟨s, hs, hsu⟩ := (Submodule.mem_map).1 (hno u hu)
    obtain ⟨u', v', hx⟩ := annG (u - s) (by rw [map_sub, hsu, sub_self])
    obtain ⟨w, hw, h, hh, rfl⟩ := Submodule.mem_sup.1 (hS hs)
    have d : ∀ z : P, z ∈ G ⊔ H := fun z => hsup ▸ Submodule.mem_top
    obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Submodule.mem_sup.1 (d u')
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 (d v')
    have e0 : ρ (1 - ε) v1 = 0 := h1εG v1 hv1
    have e1 : u - w - ρ a u1 = h + ρ a u2 + ρ (1 - ε) v2 := by
      simp only [map_add (f := _), e0] at hx
      have h' := sub_eq_iff_eq_add.1 hx
      rw [h']
      abel
    have hd0 : u - w - ρ a u1 = 0 := by
      refine Submodule.disjoint_def.1 hdisj _ (G.sub_mem (G.sub_mem hu (hWG hw)) (hρU a _ u1 hu1)) ?_
      rw [e1]
      exact H.add_mem (H.add_mem hh (hρH a _ hu2)) (hρH _ _ hv2)
    refine ⟨w, hw, u1, hu1, ?_⟩
    have h' := sub_eq_zero.1 hd0
    exact sub_eq_iff_eq_add'.1 h'
  have hpow : ∀ (n : ℕ), ∀ x ∈ Wd, (ρ a ^ n) x ∈ Wd := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply]
      exact haW _ (ih x hx)
  have hiter : ∀ (n : ℕ), ∀ u ∈ G, ∃ w ∈ Wd, ∃ u' ∈ G, u = w + (ρ a ^ n) u' := by
    intro n
    induction n with
    | zero => intro u hu; exact ⟨0, Wd.zero_mem, u, hu, by simp⟩
    | succ n ih =>
      intro u hu
      obtain ⟨w, hw, u', hu', e⟩ := ih u hu
      obtain ⟨w2, hw2, u'', hu'', e2⟩ := hstep u' hu'
      refine ⟨w + (ρ a ^ n) w2, Wd.add_mem hw (hpow n _ hw2), u'', hu'', ?_⟩
      rw [pow_succ, Module.End.mul_apply, e, e2, map_add (f := _), add_assoc]
  obtain ⟨e, he⟩ := hnil
  have hGW : G ≤ Wd := by
    intro u hu
    obtain ⟨w, hw, u', hu', eq⟩ := hiter e u hu
    have h0 : (ρ a ^ e) u' = 0 := by
      have h1 : (ρ a ^ e * ρ ε) u' = 0 := by rw [he]; rfl
      rwa [Module.End.mul_apply, hεG u' hu'] at h1
    rw [eq, h0, add_zero]
    exact hw
  exact not_le_span_image G A q hq hsemi v hvG hv0 hAv hGW

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.alg2 :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ), 0 < f →
      Nat.card (C ⧸ w) = p ^ f → ∀ (π : Par p w f) (χ : C →+* k) (P : Type 1) [AddCommGroup P] [Module k P] (ρ : C → Module.End k P) (F : Submodule k P)
      (Φ : P →+ P), Lin p π χ ρ F Φ →
      ∃ x : Module.Dual k P, (∀ y, x (ρ π.ε y) = x y) ∧ (∀ z, x (ρ π.g (Φ^[f] z)) = 0) ∧ ∃ y, (∀ c, ρ c y = χ c • y) ∧ x y ≠ 0 := by
  intro p _ k _ _ _ C _ w f hf hcard π χ P _ _ ρ F Φ L
  haveI := L.fin
  let ρh : C →+* Module.End k P :=
    { toFun := ρ, map_one' := L.one, map_mul' := L.mul, map_add' := L.add
      map_zero' := by
        have h := L.add 0 0
        simpa using h }
  have hp : ρh (p : C) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap k (Module.End k P)), CharP.cast_eq_zero k p, map_zero]
  have hdvd : ∀ x : C, (p : C) ∣ x → ρh x = 0 := by
    rintro _ ⟨d, rfl⟩
    rw [map_mul, hp, zero_mul]
  have hfix : ∀ c, χ c ^ (p ^ f) = χ c := by
    have e : (C ⧸ w) ≃ χ.range :=
      ((Ideal.quotEquivOfEq L.ker.symm).trans (RingHom.quotientKerEquivRange χ)).toEquiv
    have hcard' : Nat.card χ.range = p ^ f := (Nat.card_congr e).symm.trans hcard
    haveI : Finite χ.range := Nat.finite_of_card_ne_zero (by
      rw [hcard']; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    intro c
    have h := pow_card_subring χ.range ⟨χ c, c, rfl⟩
    rw [hcard'] at h
    exact congrArg Subtype.val h
  have hinj : Function.Injective fun x : k => x ^ (p ^ f) := by
    intro x y h
    exact (iterateFrobenius k p f).injective (by simpa [iterateFrobenius_def] using h)
  let A : P →+ P :=
    { toFun := (⇑Φ)^[f], map_zero' := iterate_map_zero Φ f, map_add' := iterate_map_add Φ f }
  have hsemiN : ∀ (n : ℕ) (l : k) x, (⇑Φ)^[n] (l • x) = l ^ (p ^ n) • (⇑Φ)^[n] x := by
    intro n
    induction n with
    | zero => intro l x; simp
    | succ n ih =>
      intro l x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.semi, ← pow_mul, pow_succ]
  have hcommN : ∀ (n : ℕ) c x, (⇑Φ)^[n] (ρ c x) = ρ c ((⇑Φ)^[n] x) := by
    intro n
    induction n with
    | zero => intro c x; rfl
    | succ n ih =>
      intro c x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, L.comm]
  obtain ⟨x0, hx0F, hx0, -⟩ := L.line
  have hAv : A (ρ π.ε x0) = 0 := by
    show (⇑Φ)^[f] (ρ π.ε x0) = 0
    have e : (⇑Φ)^[f] (ρ π.ε x0) = (⇑Φ)^[f - 1] (Φ (ρ π.ε x0)) := by
      rw [← Function.iterate_succ_apply]
      congr 2
      omega
    rw [e, L.comm, (L.kerΦ x0).2 hx0F, map_zero, iterate_map_zero]
  have hε : ρh π.ε * ρh π.ε = ρh π.ε := by
    have h := hdvd _ π.idem
    rwa [map_sub, map_mul, sub_eq_zero] at h
  have hε1 : χ π.ε = 1 := by
    have h : π.ε - 1 ∈ RingHom.ker χ := L.ker ▸ π.one
    rwa [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h
  have hnil : ∃ e : ℕ, ρh π.a ^ e * ρh π.ε = 0 := by
    obtain ⟨e, he⟩ := π.nil
    refine ⟨e, ?_⟩
    have h := hdvd _ he
    rwa [map_mul, map_pow] at h
  obtain ⟨u, hu, hnot⟩ := exists_not_mem ρh χ (p ^ f) (pow_pos (Fact.out : p.Prime).pos f) A
    (fun l x => hsemiN f l x) (fun c x => hcommN f c x) hfix hinj π.ε π.a π.g hε hε1 hnil
    (fun x h => by
      obtain ⟨u, v, e⟩ := L.annG x h
      exact ⟨u, v, e⟩)
    (ρ π.ε x0) hx0 (fun c => L.eig c x0 hx0F) hAv
  have kills : ∀ x, χ x = 0 → ρh x (ρh π.g u) = 0 := by
    intro x hx
    have hxw : x ∈ w := L.ker ▸ (RingHom.mem_ker.2 hx)
    obtain ⟨u0, d1⟩ := π.gen x hxw
    have hd : (p : C) ∣ x * π.g := by
      have e : x * π.g = (π.ε * x - π.a * u0) * π.g - x * (π.ε * π.g - π.g) + u0 * (π.a * π.g) := by ring
      rw [e]
      exact dvd_add (dvd_sub (d1.mul_right _) (π.geps.mul_left _)) ((Dvd.intro _ π.prod.symm).mul_left _)
    have h := hdvd _ hd
    rw [map_mul] at h
    rw [← Module.End.mul_apply, h]
    rfl
  have eig : ∀ c, ρ c (ρ π.g u) = χ c • ρ π.g u := by
    intro c
    have hyG : ρh π.g u ∈ (ρh c).maxGenEigenspace (χ c) := by
      have hcm : Commute (ρh c) (ρh π.g) := by
        show ρh c * ρh π.g = ρh π.g * ρh c
        rw [← map_mul, ← map_mul, mul_comm]
      exact Module.End.mapsTo_maxGenEigenspace_of_comm hcm _ ((Submodule.mem_iInf _).1 hu c)
    refine eig_of_gen p (ρh c) (χ c) f hf (hfix c) _ hyG ?_
    have hw : χ (c ^ (p ^ f) - c) = 0 := by rw [map_sub, map_pow, hfix, sub_self]
    have h := kills _ hw
    rwa [map_sub, map_pow, LinearMap.sub_apply, sub_eq_zero] at h
  obtain ⟨ξ, hξ1, hξ2⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hεε : ∀ y, ρ π.ε (ρ π.ε y) = ρ π.ε y := fun y => by
    have h := congrArg (fun T : Module.End k P => T y) hε
    exact h
  have hεg : ∀ y, ρ π.ε (ρ π.g y) = ρ π.g y := fun y => by
    have h := hdvd _ π.geps
    rw [map_sub, map_mul, sub_eq_zero] at h
    exact congrArg (fun T : Module.End k P => T y) h
  refine ⟨ξ ∘ₗ ρ π.ε, fun y => ?_, fun z => ?_, ρ π.g u, eig, ?_⟩
  · simp only [LinearMap.comp_apply, hεε]
  · simp only [LinearMap.comp_apply, hεg]
    have hm : ρh π.g (A z) ∈ (Submodule.span k (Set.range A)).map (ρh π.g) :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨z, rfl⟩)
    have h := Submodule.mem_map_of_mem (f := ξ) hm
    rw [hξ2, Submodule.mem_bot] at h
    exact h
  · simp only [LinearMap.comp_apply, hεg]
    exact hξ1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OrdPull
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private theorem UpperTheory.Gal.Ord.eq_one_of_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {y' : T.left ⟶ S}
    (hy : T.hom ≫ f = y') (x₀ : Over.mk y' ⟶ G) (hx : x₀.left = (1 : T ⟶ G').left ≫ φ) : x₀ = 1 := by
  subst hy
  have h2 := h.2 T 1 1 x₀ x₀ hx hx
  have hsq : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h2, _root_.mul_one, hx]
  exact mul_eq_left.mp hsq

private theorem UpperTheory.Gal.Ord.one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {y' : T.left ⟶ S}
    (hy : T.hom ≫ f = y') : (1 : Over.mk y' ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk y').hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    exact hy
  have e := eq_one_of_left h T hy (Over.homMk ((1 : T ⟶ G').left ≫ φ) hw) rfl
  rw [← e]
  rfl

private theorem UpperTheory.Gal.Ord.killedBy_iff {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}
    (m : ObjMap o' o f) (v : Ideal (𝓞 D.F)) (T : Over S') {y' : T.left ⟶ S} (hy : T.hom ≫ f = y')
    (x : T ⟶ o'.A) (x₀ : Over.mk y' ⟶ o.A) (hx : x₀.left = x.left ≫ m.φ) :
    KilledBy o v x₀ ↔ KilledBy o' v x := by
  have key : ∀ c : D.O, (x₀ ≫ o.act.act c).left = (x ≫ o'.act.act c).left ≫ m.φ := by
    intro c
    rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, m.act c]
  unfold KilledBy
  constructor
  · intro H a ha
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [← key, H a ha]
      exact one_left m.cart T hy
    · simp only [Over.w]
  · intro H a ha
    apply eq_one_of_left m.cart T hy
    rw [key, H a ha]

theorem UpperTheory.Gal.Ord.ordPull :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F))
      (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (s₀ : Sp k ⟶ Sp R) (o₀ : Obj b N s₀), ObjMap o₀ o y → IsWOrd o₀ w (𝟙 (Sp k)) → IsWOrd o w y := by
  intro p _ D R _ b N S s o w k _ _ y s₀ o₀ m h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rw [← h4]
  have hy : (Over.mk (𝟙 (Sp k))).hom ≫ y = y := by simp
  apply Nat.card_congr
  exact
    { toFun := fun g =>
        ⟨Over.homMk (m.cart.1.lift g.1.left (𝟙 _) (by simp)) (by rw [IsPullback.lift_snd]; rfl),
          (killedBy_iff m w _ hy _ g.1 (m.cart.1.lift_fst _ _ _).symm).mp g.2⟩
      invFun := fun g =>
        ⟨Over.homMk (g.1.left ≫ m.φ) (by rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; simp),
          (killedBy_iff m w _ hy g.1 _ rfl).mpr g.2⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        simp
      right_inv := fun g => by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        apply m.cart.1.hom_ext
        · simp
        · simp }
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.NotMem
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord.ParL

variable {C : Type} [CommRing C] [IsDedekindDomain C]

private lemma cop {w J : Ideal C} (hw : w.IsMaximal) (h : ¬ w ∣ J) : IsCoprime w J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  apply h
  rw [Ideal.dvd_iff_le]
  have hle : w ≤ w ⊔ J := le_sup_left
  have heq : w = w ⊔ J := hw.eq_of_le hne hle
  rw [heq]
  exact le_sup_right

private lemma notMem {w B : Ideal C} (hw : w.IsMaximal) (hw0 : w ≠ ⊥) {a y : C}
    (ha : Ideal.span {a} = w * B) (hB : ¬ w ∣ B) (hy : y ∉ w) (m : ℕ)
    (h : y * a ^ m ∈ w ^ (m + 1)) : False := by
  have hwp : Prime w := Ideal.prime_of_isPrime hw0 hw.isPrime
  have h1 : w ^ (m + 1) ∣ Ideal.span {y * a ^ m} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, ha, mul_pow,
    pow_succ, show Ideal.span {y} * (w ^ m * B ^ m) = w ^ m * (Ideal.span {y} * B ^ m) by ring] at h1
  have hw0' : w ^ m ≠ 0 := pow_ne_zero _ hw0
  rw [mul_dvd_mul_iff_left hw0'] at h1
  rcases hwp.dvd_or_dvd h1 with h2 | h2
  · apply hy
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  · exact hB (hwp.dvd_of_dvd_pow h2)

private lemma approx {w B : Ideal C} {a : C} (ha : Ideal.span {a} = w * B) (hc : IsCoprime w B)
    (m k : ℕ) {x : C} (hx : x ∈ w ^ m) : ∃ u, x - a ^ m * u ∈ w ^ (m + k) := by
  have hc' : IsCoprime (B ^ m) (w ^ k) := (hc.symm.pow_left).pow_right
  have htop : B ^ m ⊔ w ^ k = ⊤ := Ideal.isCoprime_iff_sup_eq.mp hc'
  have hx' : x ∈ Ideal.span {a} ^ m ⊔ w ^ (m + k) := by
    rw [ha, mul_pow, pow_add, ← Ideal.mul_sup, htop, Ideal.mul_top]
    exact hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx'
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨u, rfl⟩ := hy
  refine ⟨u, ?_⟩
  have : x - a ^ m * u = z := by rw [← hyz]; ring
  rw [this]
  exact hz

private lemma divA {w B : Ideal C} (hw : w.IsMaximal) (hw0 : w ≠ ⊥) {a : C}
    (ha : Ideal.span {a} = w * B) (hc : IsCoprime w B)
    (m : ℕ) {x : C} (hx : a * x ∈ w ^ (m + 1)) : x ∈ w ^ m := by
  have h1 : w ^ (m + 1) ∣ Ideal.span {a * x} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hx
  rw [← Ideal.span_singleton_mul_span_singleton, ha, pow_succ', _root_.mul_assoc,
    mul_dvd_mul_iff_left hw0] at h1
  have h2 : w ^ m ∣ Ideal.span {x} := (hc.pow_left).dvd_of_dvd_mul_left h1
  rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2


set_option maxHeartbeats 200000 in
private lemma exPar (p : ℕ) (hp0 : (p : C) ≠ 0) {w : Ideal C} (hw : w.IsMaximal)
    (hpw : (p : C) ∈ w) (f : ℕ) (hf : 0 < f) : Nonempty (Par p w f) := by
  have hw0 : w ≠ ⊥ := by
    intro h0
    apply hp0
    rw [h0] at hpw
    exact (Submodule.mem_bot C).mp hpw
  have hwp : Prime w := Ideal.prime_of_isPrime hw0 hw.isPrime
  have hP0 : Ideal.span {(p : C)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  obtain ⟨m, B, hwB, hPB⟩ := WfDvdMonoid.max_power_factor' hP0 hwp.not_unit
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
    rcases m with _ | n
    · exfalso
      apply hwB
      rw [pow_zero, _root_.one_mul] at hPB
      rw [← hPB, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact hpw
    · exact ⟨n, rfl⟩
  have hcB : IsCoprime w B := cop hw hwB
  have hmemP : ∀ z, z ∈ w ^ (n + 1) → z ∈ B → (p : C) ∣ z := by
    intro z hz1 hz2
    rw [← Ideal.mem_span_singleton, hPB,
      Ideal.mul_eq_inf_of_coprime (Ideal.isCoprime_iff_sup_eq.mp hcB.pow_left)]
    exact Ideal.mem_inf.mpr ⟨hz1, hz2⟩
  have hPle : ∀ z, (p : C) ∣ z → z ∈ w ^ (n + 1) := by
    intro z hz
    have hz' : z ∈ w ^ (n + 1) * B := by
      rw [← hPB]
      exact Ideal.mem_span_singleton.mpr hz
    have hle : w ^ (n + 1) * B ≤ w ^ (n + 1) := Ideal.mul_le_left
    exact hle hz'
  have hcM : IsCoprime (w ^ ((n + 1) * f)) (B ^ f) := IsCoprime.pow hcB
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ ((n + 1) * f) ⊔ B ^ f by
      rw [Ideal.isCoprime_iff_sup_eq.mp hcM]
      exact Submodule.mem_top)
  have hεB : j ∈ B := Ideal.pow_le_self hf.ne' hj
  have hi' : i ∈ w ^ (n + 1) := Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right _ hf) hi
  have h1ε : 1 - j = i := by
    rw [← hij]
    ring
  have hj1 : j - 1 ∈ w ^ (n + 1) := by
    have e : j - 1 = -i := by
      rw [← h1ε]
      ring
    rw [e]
    exact neg_mem hi'
  have hεw : j - 1 ∈ w := Ideal.pow_le_self (Nat.succ_ne_zero n) hj1
  have hεnot : j ∉ w := by
    intro h
    apply hw.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : j - (j - 1) ∈ w := w.sub_mem h hεw
    rwa [sub_sub_cancel] at h2
  have hnle : ¬ w ≤ w ^ 2 := by
    intro hle
    have h1 : w * w ∣ w * 1 := by
      rw [_root_.mul_one, ← pow_two]
      exact Ideal.dvd_iff_le.mpr hle
    rw [mul_dvd_mul_iff_left hw0] at h1
    have h2 := Ideal.dvd_iff_le.mp h1
    rw [Ideal.one_eq_top, top_le_iff] at h2
    exact hw.ne_top h2
  obtain ⟨t, ht, ht2⟩ := SetLike.not_le_iff_exists.mp hnle
  have hc2 : IsCoprime (w ^ 2) (B ^ f) := IsCoprime.pow hcB
  obtain ⟨i2, hi2, j2, hj2, hij2⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ 2 ⊔ B ^ f by
      rw [Ideal.isCoprime_iff_sup_eq.mp hc2]
      exact Submodule.mem_top)
  obtain ⟨a, haw, haB, ha2⟩ : ∃ a, a ∈ w ∧ a ∈ B ^ f ∧ a ∉ w ^ 2 := by
    refine ⟨t * j2, w.mul_mem_right _ ht, Ideal.mul_mem_left _ _ hj2, ?_⟩
    intro h
    apply ht2
    have e : t = t * j2 + t * i2 := by
      rw [← mul_add, add_comm, hij2, _root_.mul_one]
    rw [e]
    exact (w ^ 2).add_mem h (Ideal.mul_mem_left _ _ hi2)
  have haBB : a ∈ B := Ideal.pow_le_self hf.ne' haB
  obtain ⟨B', hB'⟩ : w ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haw)
  have hwB' : ¬ w ∣ B' := by
    intro hd
    apply ha2
    have h2 : w ^ 2 ∣ Ideal.span {a} := by
      rw [hB', pow_two]
      exact mul_dvd_mul_left w hd
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h2
  have hcB' : IsCoprime w B' := cop hw hwB'
  have hs : (p : C) ^ f ∣ a * (1 - j) := by
    have h3 : (1 - j) * a ∈ w ^ ((n + 1) * f) * B ^ f := by
      refine Ideal.mul_mem_mul ?_ haB
      rw [h1ε]
      exact hi
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, hPB, mul_pow, ← pow_mul,
      _root_.mul_comm a]
    exact h3
  obtain ⟨s, hs'⟩ := hs
  have hprod : (p : C) ∣ a * (j * a ^ n) := by
    apply hmemP
    · have e : a * (j * a ^ n) = j * a ^ (n + 1) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow haw _)
    · exact Ideal.mul_mem_right _ _ haBB
  obtain ⟨c, hc⟩ := hprod
  have hcw : c ∉ w := by
    intro hcw
    apply notMem hw hw0 hB' hwB' hεnot (n + 1)
    have e : j * a ^ (n + 1) = (p : C) * c := by
      rw [← hc]
      ring
    rw [e, pow_succ]
    exact Ideal.mul_mem_mul (hPle _ dvd_rfl) hcw
  have hcc : IsCoprime (w ^ (n + 1)) (Ideal.span {c}) := by
    refine IsCoprime.pow_left (cop hw ?_)
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  obtain ⟨i3, hi3, j3, hj3, hij3⟩ := Submodule.mem_sup.mp
    (show (1 : C) ∈ w ^ (n + 1) ⊔ Ideal.span {c} by
      rw [Ideal.isCoprime_iff_sup_eq.mp hcc]
      exact Submodule.mem_top)
  obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hj3
  have hinv : (p : C) ∣ c' * c * j - j := by
    have e1 : c' * c = 1 - i3 := by
      rw [← hij3]
      ring
    have e : c' * c * j - j = -(i3 * j) := by
      rw [e1]
      ring
    rw [e]
    exact hmemP _ (neg_mem (Ideal.mul_mem_right _ _ hi3)) (neg_mem (Ideal.mul_mem_left _ _ hεB))
  have hidem : (p : C) ∣ j * j - j := by
    have e : j * j - j = (j - 1) * j := by ring
    rw [e]
    exact hmemP _ (Ideal.mul_mem_right _ _ hj1) (Ideal.mul_mem_left _ _ hεB)
  have hoff : ∀ (w' : Ideal C), w'.IsMaximal → (p : C) ∈ w' → w' ≠ w → j ∈ w' := by
    intro w' hw' hpw' hne
    have hle : w ^ (n + 1) * B ≤ w' := by
      rw [← hPB]
      exact (Ideal.span_singleton_le_iff_mem _).mpr hpw'
    rcases hw'.isPrime.mul_le.mp hle with h | h
    · exact absurd (hw.eq_of_le hw'.ne_top (hw'.isPrime.le_of_pow_le h)).symm hne
    · exact h hεB
  have hgeps : (p : C) ∣ j * (j * a ^ n) - j * a ^ n := by
    have e : j * (j * a ^ n) - j * a ^ n = (j * j - j) * a ^ n := by ring
    rw [e]
    exact dvd_mul_of_dvd_left hidem _
  have hnil : ∃ e, (p : C) ∣ a ^ e * j :=
    ⟨n + 1, hmemP _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow haw _))
      (Ideal.mul_mem_left _ _ hεB)⟩
  have hgen : ∀ x ∈ w, ∃ u, (p : C) ∣ j * x - a * u := by
    intro x hx
    obtain ⟨u, hu⟩ := approx hB' hcB' 1 n (by rwa [pow_one])
    refine ⟨u, hmemP _ ?_ ?_⟩
    · have e : j * x - a * u = (j - 1) * x + (x - a ^ 1 * u) := by ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hj1) ?_
      rwa [add_comm 1 n] at hu
    · exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hεB) (Ideal.mul_mem_right _ _ haBB)
  have hannA : ∀ (x : C), (p : C) ∣ a * x → ∃ u, (p : C) ∣ j * x - j * a ^ n * u := by
    intro x hx
    have hx2 : x ∈ w ^ n := divA hw hw0 hB' hcB' n (hPle _ hx)
    obtain ⟨u, hu⟩ := approx hB' hcB' n 1 hx2
    refine ⟨u, hmemP _ ?_ ?_⟩
    · have e : j * x - j * a ^ n * u = j * (x - a ^ n * u) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ hu
    · exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hεB)
        (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hεB))
  have hannG : ∀ (x : C), (p : C) ∣ j * a ^ n * x →
      ∃ u v, (p : C) ∣ x - a * u - (1 - j) * v := by
    intro x hx
    have hxw : x ∈ w := by
      by_contra hxw
      have hy : j * x ∉ w := fun h => (hw.isPrime.mem_or_mem h).elim hεnot hxw
      apply notMem hw hw0 hB' hwB' hy n
      have e : j * x * a ^ n = j * a ^ n * x := by ring
      rw [e]
      exact hPle _ hx
    obtain ⟨u, hu⟩ := hgen x hxw
    refine ⟨u, x, ?_⟩
    have e : x - a * u - (1 - j) * x = j * x - a * u := by ring
    rw [e]
    exact hu
  exact ⟨Par.mk j a (j * a ^ n) c c' s hidem hεw hoff haw hs' hc hinv hgeps hnil hgen
    hannG hannA⟩

end UpperTheory.Gal.Ord.ParL

theorem UpperTheory.Gal.Ord.par :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (w : Ideal (𝓞 F)) (f : ℕ), w.IsMaximal → (p : 𝓞 F) ∈ w → 0 < f → Nonempty (Par p w f) := by
  intro p _ F _ _ w f hw hpw hf
  exact UpperTheory.Gal.Ord.ParL.exPar p (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hw hpw f hf
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord

private theorem asIdeal_spMap {B k : Type} [CommRing B] [Field k] (φ : B →+* k) (u : Sp k) :
    ((spMap φ).base u).asIdeal = RingHom.ker φ := by
  haveI := u.isPrime
  have hu : u.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  show Ideal.comap φ u.asIdeal = RingHom.ker φ
  rw [hu, RingHom.ker_eq_comap_bot]

private theorem charP_of_eq_closedPoint {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [IsLocalRing R]
    (hpR : (p : R) ∈ IsLocalRing.maximalIdeal R) {k : Type} [Field k] (β : R →+* k) (u : Sp k)
    (h : (spMap β).base u = IsLocalRing.closedPoint R) : CharP k p := by
  have hk : RingHom.ker β = IsLocalRing.maximalIdeal R := by
    rw [← asIdeal_spMap β u, h]
    rfl
  have h0 : (p : k) = 0 := by
    have hm : (p : R) ∈ RingHom.ker β := by
      rw [hk]
      exact hpR
    rw [RingHom.mem_ker, map_natCast] at hm
    exact hm
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0

private theorem exists_absNorm_eq {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (w : Ideal (𝓞 F))
    (hw : w.IsPrime) (hp : (p : 𝓞 F) ∈ w) : w.IsMaximal ∧ ∃ f : ℕ, 0 < f ∧ Ideal.absNorm w = p ^ f := by
  have hne : w ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
  haveI : w.IsMaximal := hw.isMaximal hne
  refine ⟨inferInstance, ?_⟩
  obtain ⟨q, n, hn, hqw, hq, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow w
  have hqp : q = p := by
    by_contra hne'
    have hcop : Nat.Coprime p q := (Nat.coprime_primes Fact.out hq).mpr (Ne.symm hne')
    have h1 : (((Nat.gcd p q : ℕ) : ℤ) : 𝓞 F) ∈ w := by
      rw [Nat.gcd_eq_gcd_ab]
      push_cast
      exact w.add_mem (w.mul_mem_right _ hp) (w.mul_mem_right _ hqw)
    rw [hcop.gcd_eq_one, Nat.cast_one, Int.cast_one] at h1
    exact (Ideal.IsMaximal.ne_top inferInstance) ((Ideal.eq_top_iff_one w).mpr h1)
  exact ⟨n, hn, hqp ▸ hN⟩

end UpperTheory.Gal.Ord

theorem UpperTheory.Gal.Ord.ordGen :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → D.m = 1 → ∀ (i : Fin D.a) (w : Ideal (𝓞 D.F)), (IsLocalRing.maximalIdeal R).comap (b.t i) = w → ∀ (M : Model b N) (z : M.X), M.s.base z = IsLocalRing.closedPoint R → (∀ z' : M.X, M.s.base z' = IsLocalRing.closedPoint R → z' ⤳ z → z' = z) → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ M.X), (∀ q, y.base q = z) → IsWOrd M.univ w y := by
  intro p _ D R _ _ _ _ b N hN hNp hpR hm i w hw M z hz hmin k _ _ y hy
  haveI : Smooth M.s := @SmoothOfRelativeDimension.smooth _ _ _ _ M.smooth
  set β : R →+* k := (Spec.preimage (y ≫ M.s)).hom with hβdef
  have hyβ : y ≫ M.s = spMap β := (Spec.map_preimage (y ≫ M.s)).symm
  have hβbase : (spMap β).base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R := by
    rw [← hyβ]
    exact (congrArg M.s.base (hy _)).trans hz
  haveI hchar : CharP k p := charP_of_eq_closedPoint hpR β _ hβbase
  have hk : (p : k) = 0 := CharP.cast_eq_zero k p
  have hkerβ : RingHom.ker β = IsLocalRing.maximalIdeal R := by
    rw [← asIdeal_spMap β (IsLocalRing.closedPoint k), hβbase]
    rfl
  have hkerw : RingHom.ker (β.comp (b.t i)) = w := by
    rw [← RingHom.comap_ker, hkerβ, hw]
  have hwP : w.IsPrime := by
    rw [← hkerw]
    exact RingHom.ker_isPrime _
  have hpw : (p : 𝓞 D.F) ∈ w := by
    rw [← hkerw, RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast]
    exact hk
  obtain ⟨hwM, f, hf, hnorm⟩ := exists_absNorm_eq w hwP hpw
  obtain ⟨π⟩ := par p D.F w f hwM hpw hf
  obtain ⟨o₀, ⟨a₀⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X (Sp k) M.s (spMap β) y hyβ M.univ
  apply ordPull p D R b N M.X M.s M.univ w k y (spMap β) o₀ a₀
  have hpnt : IsWOrd o₀ w (𝟙 (Sp k)) ∨ NOo hk o₀ π :=
    UpperTheory.Gal.Ord.point p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π
  rcases hpnt with hW | hNO
  · exact hW
  exfalso
  have hLin := lin p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π
  have hcard : Nat.card (𝓞 D.F ⧸ w) = p ^ f := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact hnorm
  obtain ⟨x, hxε, hxg, y0, hy0, hxy0⟩ :=
    alg2 p k (𝓞 D.F) w f hf hcard π (β.comp (b.t i)) _ (coh o₀) (PrimitiveSubmodule o₀.A) _ hLin
  have hxFil : x ∈ Fil o₀.A := by
    rw [Fil, Submodule.mem_dualAnnihilator]
    intro c hc
    rw [← hxε c]
    have hle : Submodule.span k (Set.range fun c' => (coh o₀ π.g) ((⇑(frobDR p k hk o₀.A))^[f] c')) ≤
        LinearMap.ker x := by
      rw [Submodule.span_le]
      rintro _ ⟨c', rfl⟩
      exact hxg c'
    exact hle (hNO c hc)
  have hhom : hom o₀ π.ε x = x := by
    apply LinearMap.ext
    intro c
    exact hxε c
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.harrisTaylor_exists_deRham_pairing p D R b N hN hNp k (spMap β) o₀
  obtain ⟨g, hKS, hgx⟩ :=
    ks p D R b N hN hNp hm k hk β o₀ i w f hkerw hnorm hf π φ hφ x hxFil hhom ⟨y0, hy0, hxy0⟩
  obtain ⟨o', m', hlift⟩ := GlobalTheory.T.harrisTaylor_realise_kodairaSpencer_direction p D R b N hN hNp k (spMap β) o₀ β rfl φ hφ g hKS
  have hfst : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
    ext a
    rfl
  have hcomp : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← GlobalTheory.Cris.spMap_comp, hfst]
    show Spec.map (CommRingCat.ofHom (RingHom.id k)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨v, ⟨hv1, ⟨av⟩⟩, -⟩ := M.rep (Sp (DualNumber k)) _ o'
  have hcompv : Nonempty (ObjMap o₀ M.univ (spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v)) :=
    (GlobalTheory.T.harrisTaylorObjectPullback_comp_diagonalBundle p D R b N _ _ _ _ _ _ M.univ o' o₀ v _).1 ⟨m'⟩ ⟨av⟩
  have hyv : y = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v := by
    apply (M.rep (Sp k) (spMap β) o₀).unique ⟨hyβ, ⟨a₀⟩⟩ ⟨?_, hcompv⟩
    rw [Category.assoc, hv1, ← Category.assoc, hcomp, Category.id_comp]
  have hcl : (spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base (IsLocalRing.closedPoint k) =
      IsLocalRing.closedPoint (DualNumber k) := by
    apply PrimeSpectrum.ext
    refine (asIdeal_spMap (TrivSqZeroExt.fstHom k k k).toRingHom (IsLocalRing.closedPoint k)).trans ?_
    exact IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩))
  have hvz : v.base (IsLocalRing.closedPoint (DualNumber k)) = z := by
    rw [← hcl]
    have h1 := hy (IsLocalRing.closedPoint k)
    rw [hyv] at h1
    exact h1
  obtain ⟨σ, hσ⟩ := gen R M.X M.s z hz hmin k y β (hy _) hyβ (fun r hr => by
    have hr' : r ∈ RingHom.ker β := hkerβ ▸ hr
    exact RingHom.mem_ker.mp hr')
  obtain ⟨τ, hτ⟩ := gen R M.X M.s z hz hmin (DualNumber k) v ((algebraMap k (DualNumber k)).comp β) hvz
    (hv1.trans (GlobalTheory.Cris.spMap_comp β _).symm) (fun r hr => by
      have hr' : r ∈ RingHom.ker β := hkerβ ▸ hr
      rw [RingHom.comp_apply, RingHom.mem_ker.mp hr', map_zero])
  obtain ⟨oκ, ⟨aκ⟩⟩ := GlobalTheory.T.exists_harrisTaylorModuliObject_pullback p D R b N M.X _ M.s (M.X.fromSpecResidueField z ≫ M.s)
    (M.X.fromSpecResidueField z) rfl M.univ
  have a₀' : ObjMap o₀ M.univ (spMap σ ≫ M.X.fromSpecResidueField z) := by
    rw [hσ]
    exact a₀
  have av' : ObjMap o' M.univ (spMap τ ≫ M.X.fromSpecResidueField z) := by
    rw [hτ]
    exact av
  obtain ⟨b₀⟩ := factor p D R b N hN hNp _ _ _ M.s _ _ M.univ oκ o₀ (M.X.fromSpecResidueField z) (spMap σ)
    rfl ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.s) hσ).trans hyβ)) aκ a₀'
  obtain ⟨b'⟩ := factor p D R b N hN hNp _ _ _ M.s _ _ M.univ oκ o' (M.X.fromSpecResidueField z) (spMap τ)
    rfl ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ M.s) hτ).trans hv1)) aκ av'
  have hκ : (p : M.X.residueField z) = 0 :=
    σ.injective (by rw [map_natCast, map_zero]; exact hk)
  have hT : (p : DualNumber k) = 0 := by
    rw [← map_natCast (algebraMap k (DualNumber k)), hk, map_zero]
  have hNO' := desc p D R b N w f π _ k (DualNumber k) hκ hk hT σ τ _ _ _ oκ o₀ o' b₀ b' hNO
  have h0 := estep p D R b N w f hf π k hk hT (spMap β) _ o₀ o' m' hNO' x hxg
  rw [hhom] at h0
  have hmem := (GlobalTheory.T.hodgeFiltration_lift_determines_mod_fil k o₀.A o'.A m'.φ m'.cart o'.ab x hxFil (g x) 0 (hlift x hxFil)).mp h0
  have hneg := (Fil o₀.A).neg_mem hmem
  rw [zero_sub, neg_neg] at hneg
  exact hgx hneg
