module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousOfCond
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleAdelicDataStandardBasePoints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceGeometryExtensionCosetOrbitReps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsExtGeometryTupleOfRepresentatives

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExp
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDegOnePow

section Arith
variable {K : Type} [Field K] [NumberField K]

theorem pow_dvd_of_mem (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hvI : IsCoprime v.asIdeal I) (hpI : Ideal.span {(p : 𝓞 K)} = v.asIdeal * I) (n : ℕ) (r : ℤ)
    (hr : (r : 𝓞 K) ∈ v.asIdeal ^ n) : (p : ℤ) ^ n ∣ r := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨s, rfl⟩ := ih (Ideal.pow_le_pow_right (Nat.le_succ n) hr)
    have h1 : v.asIdeal ^ n * v.asIdeal ∣ v.asIdeal ^ n * (I ^ n * Ideal.span {(s : 𝓞 K)}) := by
      rw [← pow_succ, ← mul_assoc, ← mul_pow, ← hpI, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
        Ideal.dvd_span_singleton]
      simpa using hr
    rw [mul_dvd_mul_iff_left (pow_ne_zero n v.ne_bot)] at h1
    have h2 : (s : 𝓞 K) ∈ v.asIdeal := Ideal.dvd_span_singleton.1 (hvI.pow_right.dvd_of_dvd_mul_left h1)
    have hpv : (p : 𝓞 K) ∈ v.asIdeal :=
      (Ideal.span_singleton_le_iff_mem _).1 (hpI ▸ Ideal.mul_le_left)
    have h3 : (p : ℤ) ∣ s := by
      by_contra hc
      obtain ⟨x, y, e⟩ := ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).2 hc
      have e' : (x : 𝓞 K) * p + y * s = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 K) e
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (e' ▸ add_mem (Ideal.mul_mem_left _ _ hpv) (Ideal.mul_mem_left _ _ h2)))
    rw [pow_succ]
    exact mul_dvd_mul_left _ h3

theorem exists_int_sub_mem (N : ℕ) (hN : N ≠ 0) (J : Ideal (𝓞 K)) (hJ : Ideal.absNorm J = N)
    (hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ J → (N : ℤ) ∣ r) (m : 𝓞 K) : ∃ r : ℤ, m - r ∈ J := by
  have hle : Ideal.span {(N : ℤ)} ≤ J.comap (Int.castRingHom (𝓞 K)) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hJ]
    exact Ideal.absNorm_mem J
  have hi : Function.Injective (Ideal.quotientMap J (Int.castRingHom (𝓞 K)) hle) :=
    Ideal.quotientMap_injective' fun r hr => Ideal.mem_span_singleton.2 (hinj r hr)
  have hc : Nat.card (𝓞 K ⧸ J) = N := by rw [← hJ, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 K ⧸ J) := Nat.finite_of_card_ne_zero (hc ▸ hN)
  have hb := hi.bijective_of_nat_card_le (by
    rw [hc, Nat.card_congr (Int.quotientSpanNatEquivZMod N).toEquiv, Nat.card_zmod])
  obtain ⟨r, hr⟩ := hb.2 (Ideal.Quotient.mk J m)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact ⟨r, Ideal.Quotient.eq.1 hr.symm⟩

theorem trace_idem (N : ℕ) (J I : Ideal (𝓞 K)) (hN : Ideal.span {(N : 𝓞 K)} = J * I)
    (hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ J → (N : ℤ) ∣ r) (hsurj : ∀ m : 𝓞 K, ∃ r : ℤ, m - r ∈ J)
    (t : 𝓞 K) (ht : t ∈ I) (ht1 : t - 1 ∈ J) : ∃ m : ℤ, Algebra.trace ℤ (𝓞 K) t = 1 + N * m := by
  classical
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  choose r hr using fun j => hsurj (b j)
  have hy : ∀ j, ∃ y : 𝓞 K, y * N = (b j - r j) * t := fun j =>
    Ideal.mem_span_singleton'.1 (hN ▸ Ideal.mul_mem_mul (hr j) ht)
  choose y hy using hy
  let π : 𝓞 K →ₗ[ℤ] ℤ := b.constr ℤ r
  let g : 𝓞 K →ₗ[ℤ] 𝓞 K := b.constr ℤ y
  have hπ : ∀ m : 𝓞 K, m - (π m : 𝓞 K) ∈ J := by
    have : (J.restrictScalars ℤ).mkQ ∘ₗ (LinearMap.id - (Algebra.linearMap ℤ (𝓞 K)) ∘ₗ π) = 0 :=
      b.ext fun j => (Submodule.Quotient.mk_eq_zero _).2 (by simpa [π] using hr j)
    intro m
    simpa using (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun this m)
  have hm : Algebra.lmul ℤ (𝓞 K) t = π.smulRight t + (N : ℤ) • g := b.ext fun j => by
    simp only [π, g, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, Module.Basis.constr_basis,
      Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    linear_combination (-1 : 𝓞 K) * hy j
  obtain ⟨c, hc⟩ := hinj (π t - 1) (by
    have := sub_mem ht1 (hπ t)
    push_cast
    convert this using 1
    ring)
  refine ⟨c + LinearMap.trace ℤ _ g, ?_⟩
  rw [Algebra.trace_apply, hm, map_add (f := _), map_smul, LinearMap.trace_smulRight, smul_eq_mul]
  linear_combination hc

theorem fin_part (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) (α : Af K)
    (hα1 : evalV K v α = 1) (hα0 : ∀ w, w ≠ v → evalV K w α = 0) (b : ℤ) (n : ℕ) :
    ∃ x : 𝓞 K, (∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + (p : ℤ) ^ n * m) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (α * algebraMap K (Af K) ((b : K) / (p : K) ^ n) -
        algebraMap K (Af K) ((x : K) / (p : K) ^ n)) w ∈ w.adicCompletionIntegers K := by
  obtain ⟨I, hvI, hpI⟩ := GlobalTheory.StdCharDegOne.exists_cofactor p v hnorm hsq
  obtain ⟨u, hu, t, ht, hut⟩ := Ideal.isCoprime_iff_exists.mp (hvI.pow (m := n) (n := n))
  have hN : Ideal.span {((p ^ n : ℕ) : 𝓞 K)} = v.asIdeal ^ n * I ^ n := by
    rw [← mul_pow, ← hpI, Ideal.span_singleton_pow, Nat.cast_pow]
  have hinj : ∀ r : ℤ, (r : 𝓞 K) ∈ v.asIdeal ^ n → ((p ^ n : ℕ) : ℤ) ∣ r := fun r hr => by
    rw [Nat.cast_pow]; exact pow_dvd_of_mem p hp v I hvI hpI n r hr
  obtain ⟨m, hm⟩ := trace_idem (p ^ n) _ _ hN hinj
    (exists_int_sub_mem _ (pow_ne_zero n hp.ne_zero) _ (by rw [map_pow, hnorm]) hinj) t ht (by
      rw [show t - 1 = -u by linear_combination hut]; exact neg_mem hu)
  have hp0 : (p : 𝓞 K) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hmemp : ∀ z ∈ v.asIdeal ^ n * I ^ n, ∃ y, z = (p : 𝓞 K) ^ n * y := fun z hz => by
    rw [← hN, Ideal.mem_span_singleton'] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by rw [← hy, mul_comm, Nat.cast_pow]⟩
  refine ⟨b * t, ⟨b * m, ?_⟩, fun w => ?_⟩
  · rw [← zsmul_eq_mul, map_smul, Algebra.intTrace_eq_trace, hm, smul_eq_mul]
    push_cast
    ring
  have hcomp : (α * algebraMap K (Af K) ((b : K) / (p : K) ^ n) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n)) w =
      α w * algebraMap K (Af K) ((b : K) / (p : K) ^ n) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) w := rfl
  rw [hcomp]
  by_cases hw : w = v
  · subst hw
    have h1 : α w = 1 := hα1
    have hsub : algebraMap K (Af K) ((b : K) / (p : K) ^ n) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) w =
        algebraMap K (Af K) ((((b : 𝓞 K) - (b : 𝓞 K) * t : 𝓞 K) : K) / (((p : 𝓞 K) ^ n : 𝓞 K) : K)) w := by
      rw [show ((((b : 𝓞 K) - (b : 𝓞 K) * t : 𝓞 K) : K) / (((p : 𝓞 K) ^ n : 𝓞 K) : K)) =
        (b : K) / (p : K) ^ n - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K) ^ n) by rw [← sub_div]; simp, map_sub]
      rfl
    rw [h1, one_mul, hsub]
    obtain ⟨u', hu', s, hs, hus⟩ := Ideal.isCoprime_iff_exists.mp (hvI.pow_right (n := n))
    have hsv : s ∉ w.asIdeal := fun h =>
      w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hus ▸ add_mem hu' h))
    have hmem : ((b : 𝓞 K) - (b : 𝓞 K) * t) * s ∈ w.asIdeal ^ n * I ^ n := by
      refine Ideal.mul_mem_mul ?_ hs
      rw [show (b : 𝓞 K) - (b : 𝓞 K) * t = b * u by linear_combination (-b : 𝓞 K) * hut]
      exact Ideal.mul_mem_left _ _ hu
    obtain ⟨y, hy⟩ := hmemp _ hmem
    exact GlobalTheory.StdCharDegOne.integral_of_mul w _ _ s y hp0 hsv hy
  · have h0 : α w = 0 := hα0 w hw
    rw [h0, zero_mul, zero_sub]
    refine neg_mem ?_
    obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
      by_contra hc
      push Not at hc
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)
    obtain ⟨y, hy⟩ := hmemp _ (Ideal.mul_mem_mul (Ideal.pow_mem_pow hsv n) (Ideal.mul_mem_left _ (b : 𝓞 K) ht))
    have := GlobalTheory.StdCharDegOne.integral_of_mul w ((p : 𝓞 K) ^ n) ((b : 𝓞 K) * t) (s ^ n) y hp0
      (fun h => hsw (w.isPrime.mem_of_pow_mem n h)) (by rw [mul_comm]; exact hy)
    simpa using this

end Arith

theorem stdChar_placeIdem_div_pow (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2)
    (ε) (hε : IsPlaceIdem D v ε) (b : ℤ) (n : ℕ) :
    ψ (ε * algebraMap D.host.F (AF D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ) ^ n) := by
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  obtain ⟨x, ⟨m, hm⟩, hint⟩ := fin_part p hp v hnorm hsq α hα1 hα0 b n
  have hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n)) +
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n)) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * _ = 0 + 0
      rw [zero_mul, add_zero]
    · show α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) =
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n) +
        (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
          algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n))
      rw [add_sub_cancel]
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  have h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((b : D.host.F) / (p : D.host.F) ^ n) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F) ^ n))) = 1 := by
    refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
      (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
      (fun r => ?_) _ hint
    show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
  have hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F) ^ n) = ((b : ℚ) + p ^ n * m) / p ^ n := by
    have e : (x : D.host.F) / (p : D.host.F) ^ n = (((p : ℚ) ^ n)⁻¹) • (x : D.host.F) := by
      rw [Algebra.smul_def, map_inv₀, map_pow, map_natCast, div_eq_inv_mul]
    rw [e, map_smul, htr, hm, smul_eq_mul]
    push_cast
    ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p ^ n * m) / p ^ n : ℚ) : ℂ) =
      2 * Real.pi * Complex.I * b / (p : ℂ) ^ n + m * (2 * Real.pi * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem weilChar_pr_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (Formalism.L2.Col.qOf PP).Prime → ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk → ∀ (a : D.host.E) (b : ℤ) (n : ℕ), Formalism.L2.Col.IntAt PP (D.host.xi0 * a - (b : D.host.E) / (Formalism.L2.Col.qOf PP : D.host.E) ^ n) → (ψk ((ofSplit q).pr a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (Formalism.L2.Col.qOf PP : ℂ) ^ n) := by
  intro D k _ _ _ _ q PP hid hp hsq hint ψ hψ ψk hch a b n hx
  have hv := GlobalTheory.LocMod.PinInhab.v_eq_under q hid
  have hPP : Ideal.absNorm PP.asIdeal = Formalism.L2.Col.qOf PP := rfl
  generalize Formalism.L2.Col.qOf PP = p at hp hsq hx hPP ⊢
  have hpr : ∀ y : D.host.E, (ofSplit q).pr y = q.pr (incA D y) := fun _ => rfl
  have hms : ∀ (x : AE D) (y : k), x * q.sec y = q.sec (q.pr x * y) := fun x y => by
    have h := q.sec_pr (x * q.sec y)
    have h' := q.sec_pr (q.sec y)
    rw [map_mul, q.pr_sec] at h
    rw [q.pr_sec] at h'
    rw [h, mul_left_comm, ← h']
  have h0 : (ψk ((ofSplit q).pr a) : ℂ) = psiE ψ (q.sec (q.pr (incA D (D.host.xi0 * a)))) := by
    rw [map_mul, map_mul]
    exact (hch _).trans (congrArg _ (hms _ _))
  rw [h0]
  generalize D.host.xi0 * a = x at hx
  set c : D.host.F := (b : D.host.F) / (p : D.host.F) ^ n with hcdef
  have hc : algebraMap D.host.F D.host.E c = (b : D.host.E) / (p : D.host.E) ^ n := by
    rw [hcdef, map_div₀, map_pow, map_intCast, map_natCast]
  have hxs : x = (x - (b : D.host.E) / (p : D.host.E) ^ n) + algebraMap D.host.F D.host.E c := by
    rw [hc]; ring
  have hadd : ∀ u w : AE D, psiE ψ (u + w) = psiE ψ u * psiE ψ w := by
    intro u w; simp only [GlobalTheory.MixPer.psiE, map_add (f := _), AddChar.map_add_eq_mul]
  rw [hxs, map_add (f := _), map_add (f := _), map_add (f := _), hadd]
  have hy : q.pr (incA D (x - (b : D.host.E) / (p : D.host.E) ^ n)) ∈ 𝒪[k] := by
    rw [← hpr]; exact (hint _).2 hx
  have h1 : psiE ψ (q.sec (q.pr (incA D (x - (b : D.host.E) / (p : D.host.E) ^ n)))) = 1 := by
    rw [GlobalTheory.MixPer.psiE, GlobalTheory.SplitCharCond.trace_sec q, GlobalTheory.SplitCharCond.snd_trace,
      GlobalTheory.SplitCharCond.char_int hψ (GlobalTheory.SplitCharCond.trace_int ((q.int_iff _).1 hy))]
  rw [h1, one_mul]
  obtain ⟨ε, hε, he⟩ := q.above
  have htr : Algebra.trace (AF D.host.F) (AE D) q.e = ε := by
    refine Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_
    change algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [GlobalTheory.FockCompare.SymplVal.trace_AE, he]
  have hinc : incA D (algebraMap D.host.F D.host.E c) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c) := GlobalTheory.SplitCharCond.one_tmul_eq c
  rw [q.sec_pr, hinc, mul_comm, ← Algebra.smul_def, GlobalTheory.MixPer.psiE, map_smul, smul_eq_mul, htr, mul_comm]
  have hnorm : Ideal.absNorm q.v.asIdeal = p := by rw [hv]; exact GlobalTheory.SplitDegOneChar.absNorm_under PP p hp hPP
  have hsqv : (p : 𝓞 D.host.F) ∉ q.v.asIdeal ^ 2 := by
    rw [hv]; exact GlobalTheory.SplitDegOneChar.natCast_not_mem_under_sq PP p hsq
  exact stdChar_placeIdem_div_pow D ψ hψ p hp q.v hnorm hsqv ε hε b n

end GlobalTheory.SplitDegOnePow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitDegreeOnePlaceEqExpStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilCharacter_splitDegreeOne_place_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (Formalism.L2.Col.qOf PP).Prime → ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar ψ ψk → ∀ (a : D.host.E) (b : ℤ) (n : ℕ), Formalism.L2.Col.IntAt PP (D.host.xi0 * a - (b : D.host.E) / (Formalism.L2.Col.qOf PP : D.host.E) ^ n) → (ψk ((ofSplit q).pr a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (Formalism.L2.Col.qOf PP : ℂ) ^ n) := by
  first | exact @GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp | exact GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp | (intros; apply GlobalTheory.SplitDegOnePow.weilChar_pr_eq_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCoset
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridge


open Classical in
theorem twNext_rep_eq_of_sameDC {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Tup X.F X.E X.K S₀)
    (cst : LocCst X (rowSG Pr sel mu)) {i : ℕ} (st : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) i)
    (hinj : ∀ d d' : (twNext Ch sel mu cst st).β, (∀ P : rowSG Pr sel mu,
      SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h d P) ((twNext Ch sel mu cst st).h d' P)) → d = d')
    (d d' : (twNext Ch sel mu cst st).β) (P : rowSG Pr sel mu)
    (hs : SameDC (Pr := Pr) cst.sharp (i + 1) P.1 ((twNext Ch sel mu cst st).h d P) ((twNext Ch sel mu cst st).h d' P)) :
    (twNext Ch sel mu cst st).h d P = (twNext Ch sel mu cst st).h d' P := by
  by_cases hP : P.1 ∈ twQOff (Pr := Pr) sel mu
  · let P₀ : twQOff (Pr := Pr) sel mu := ⟨P.1, hP⟩
    let d'' : (twNext Ch sel mu cst st).β := ⟨Function.update d.1 P₀ (d'.1 P₀), d.2⟩
    have hall : ∀ Q : rowSG Pr sel mu, SameDC (Pr := Pr) cst.sharp (i + 1) Q.1
        ((twNext Ch sel mu cst st).h d Q) ((twNext Ch sel mu cst st).h d'' Q) := by
      intro Q
      by_cases hQ : Q.1 ∈ twQOff (Pr := Pr) sel mu
      · by_cases e : (⟨Q.1, hQ⟩ : twQOff (Pr := Pr) sel mu) = P₀
        · have hQP1 : Q.1 = P.1 := congrArg (fun x : twQOff (Pr := Pr) sel mu => x.1) e
          have hQP : Q = P := Subtype.ext hQP1
          rw [hQP]
          have e1 : (twNext Ch sel mu cst st).h d'' P = (twNext Ch sel mu cst st).h d' P := by
            simp only [twNext, dif_pos hP, d'']
            rw [Function.update_self]
          rw [e1]; exact hs
        · have e1 : (twNext Ch sel mu cst st).h d'' Q = (twNext Ch sel mu cst st).h d Q := by
            simp only [twNext, dif_pos hQ, d'']
            rw [Function.update_of_ne e]
          rw [e1]; exact twDC_refl _ _ _ _
      · have e1 : (twNext Ch sel mu cst st).h d'' Q = (twNext Ch sel mu cst st).h d Q := by
          simp only [twNext, dif_neg hQ]
        rw [e1]; exact twDC_refl _ _ _ _
    have hdd := hinj d d'' hall
    have hc : d.1 P₀ = d'.1 P₀ := by
      have := congrArg (fun x : (twNext Ch sel mu cst st).β => x.1 P₀) hdd
      simpa [d''] using this
    simp only [twNext, dif_pos hP]
    exact congrArg (fun D => twRep Ch sel mu cst st P₀ D.1) hc
  · simp only [twNext, dif_neg hP]

theorem idxProd_twIdx : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (G : ChGlob X R.m), (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 → IdxProd sel mu cst (twIdx Ch sel mu cst m2) := by
  intro X Pr R Ch sel S₀ mu cst m2 G hok j b b' P hs
  rcases j with _ | i
  · rfl
  · by_cases hi : i + 1 ≤ m2
    · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) →
          ∀ b b' : st'.β, (∀ b b' : st'.β, (∀ P : rowSG Pr sel mu,
            SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (st'.h b P) (st'.h b' P)) → b = b') →
          SameDC (Pr := Pr) cst.sharp (i + 1) P.1 (st'.h b P) (st'.h b' P) → st'.h b P = st'.h b' P := by
        rintro st' rfl b b' hinj hs
        exact twNext_rep_eq_of_sameDC Ch sel mu cst _ hinj b b' P hs
      exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_pos hi]) b b' (hok.inj i (by omega)) hs
    · by_cases hi2 : i + 1 = m2 + 1
      · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twUnitSt _ (i + 1) →
            ∀ b b' : st'.β, st'.h b P = st'.h b' P := by
          rintro st' rfl b b'; rfl
        exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_neg hi, if_pos hi2]) b b'
      · have key : ∀ st' : TwSt X Pr R (QE sel (mu : Chr X.F X.E X.K)) (i + 1), st' = twEmptySt _ (i + 1) →
            ∀ b b' : st'.β, st'.h b P = st'.h b' P := by
          rintro st' rfl b; exact b.elim
        exact key (twSt Ch sel mu cst m2 (i + 1)) (by rw [twSt, if_neg hi, if_neg hi2]) b b'

end GlobalTheory.TwBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexDataRepresentativeDependsOnDoubleCosetStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistIndexData_representative_dependsOnDoubleCoset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (G : ChGlob X R.m), (twIdx Ch sel mu cst m2).Ok Ch sel mu cst G m2 → IdxProd sel mu cst (twIdx Ch sel mu cst m2) := by
  first | exact @GlobalTheory.TwBridge.idxProd_twIdx | exact GlobalTheory.TwBridge.idxProd_twIdx | (intros; apply GlobalTheory.TwBridge.idxProd_twIdx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentatives
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.TwBridge

theorem idxIsProd_of_ok : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  intro X Pr R Ch sel S₀ mu cst L G s hL hP j hj hh hex
  have hrefl : ∀ (i : ℕ) (P : rowSG Pr sel mu) (a : AutY X R i), SameDC (Pr := Pr) cst.sharp i P.1 a a :=
    fun i P a => ⟨1, one_mem _, 1, one_mem _, by simp⟩
  rcases j with _ | i
  · obtain ⟨b, hb⟩ := hL.zero_uniq
    refine ⟨b, fun P => ?_, fun b' _ => hb b'⟩
    obtain ⟨b₀, hb₀⟩ := hex P
    rw [← hb₀, hL.zero_h, hL.zero_h]
  · have hi : i < s := by omega
    choose bP hbP using hex
    obtain ⟨b, hb⟩ := hL.surj i hi hh
      (fun P hPg => hbP P ▸ hL.stabG (i + 1) (bP P) P hPg)
      (fun P hPg => hbP P ▸ hL.boundQ (i + 1) (bP P) P hPg)
      (fun P => by
        obtain ⟨al, hal⟩ := hL.nonvan i hi (bP P) P
        exact ⟨al, hbP P ▸ hal⟩)
    refine ⟨b, fun P => ?_, fun b' hb' => ?_⟩
    · have h1 := hb P
      rw [← hbP P] at h1 ⊢
      exact hP (i + 1) b (bP P) P h1
    · refine hL.inj i hi b' b (fun P => ?_)
      have e : L.h (i + 1) b' P = L.h (i + 1) b P := by
        have h1 := hb P
        rw [hb' P, ← hbP P] at *
        exact (hP (i + 1) b (bP P) P h1).symm
      rw [e]; exact hrefl _ _ _

end GlobalTheory.TwBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistIndexSetEqProdLocalRepresentativesStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistIndexSet_eq_prod_localRepresentatives : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → IdxIsProd sel mu s L := by
  first | exact @GlobalTheory.TwBridge.idxIsProd_of_ok | exact GlobalTheory.TwBridge.idxIsProd_of_ok | (intros; apply GlobalTheory.TwBridge.idxIsProd_of_ok <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumns
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

noncomputable section
namespace GlobalTheory.TwBridgeInhab

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_eq_one_of_sub_one {x : k} (hx : valuation k (x - 1) < 1) : valuation k x = 1 := by
  have h := Valuation.map_add_eq_of_lt_right (valuation k) (x := x - 1) (y := 1) (by simpa using hx)
  simpa using h

def delta (μ₁ : kˣ →* ℂˣ) (ϖ : kˣ) : kˣ →* ℂˣ := μ₁ * GlobalTheory.SmGL.unrChar k (μ₁ ϖ)⁻¹

theorem delta_unit (μ₁ : kˣ →* ℂˣ) (ϖ : kˣ) {x : kˣ} (hx : valuation k (x : k) = 1) : delta μ₁ ϖ x = μ₁ x := by
  simp [delta, GlobalTheory.SmGL.isUnram_unrChar k _ x hx]

theorem delta_tame {μ₁ : kˣ →* ℂˣ} (h : IsTame μ₁) (ϖ : kˣ) : IsTame (delta μ₁ ϖ) := by
  intro x hx
  rw [delta_unit μ₁ ϖ (val_eq_one_of_sub_one hx)]
  exact h x hx

def eta (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) (j : ℕ) : kˣ →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ m then μ j * δ⁻¹ else 1

theorem eta_mul (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ) {i : ℕ} (hi : i < m) :
    eta μ m δ (i + 1) * δ = μ (i + 1) := by
  rw [eta, if_pos ⟨by omega, by omega⟩, inv_mul_cancel_right]

theorem eta_unram (μ : ℕ → kˣ →* ℂˣ) (m : ℕ) (δ : kˣ →* ℂˣ)
    (h : ∀ i, i < m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = δ x) (j : ℕ) : IsUnram (eta μ m δ j) := by
  intro x hx
  unfold eta
  split_ifs with hj
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h i (by omega) x hx, mul_inv_cancel]
  · rfl

theorem exists_near {E : Type} [Field E] {ι : E →+* k} (hd : DenseRange ι) (x : k) :
    ∃ a : E, valuation k (ι a - x) < 1 := by
  have hU : {y | valuation k (y - x) < 1} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff]
    exact ⟨1, by rintro _ ⟨z, hz, rfl⟩; simpa using hz⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hU
  exact ⟨a, hy⟩

theorem tame_near {μ : kˣ →* ℂˣ} (h : IsTame μ) {x u : kˣ} (hx : valuation k (x : k) = 1)
    (hu : valuation k ((u : k) - x) < 1) : μ u = μ x := by
  have hx0 : (x : k) ≠ 0 := x.ne_zero
  have hy : valuation k (((x⁻¹ * u : kˣ) : k) - 1) < 1 := by
    have e : ((x⁻¹ * u : kˣ) : k) - 1 = (x : k)⁻¹ * ((u : k) - x) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hx, inv_one, one_mul]; exact hu
  have := h _ hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

end Loc

section Arith
variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem unitV_inv {P : HeightOneSpectrum (𝓞 E)} (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    LocE.unitV χ⁻¹ a = (LocE.unitV χ a)⁻¹ := by
  unfold LocE.unitV
  split_ifs <;> simp

theorem valuation_self (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) :
    LocE.vP P q (q : E) = 1 := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have hnu : ¬ IsUnit (0 : 𝓞 E ⧸ P.asIdeal) := not_isUnit_zero
  have key : ∀ z : ℤ, IsUnit (redP P ((q : E) / (q : E) ^ z)) ↔ z = 1 := by
    intro z
    constructor
    · intro h
      by_contra hz
      rcases lt_or_gt_of_ne hz with hlt | hgt
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = -(k : ℤ) := ⟨(-z).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = algebraMap (𝓞 E) E (((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
          rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, map_pow, map_natCast, pow_succ']
        rw [e, reduction_coe] at h
        have h1 : Ideal.Quotient.mk P.asIdeal (((q : ℕ) : 𝓞 E) ^ (k + 1)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [h1] at h; exact hnu h
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, z = (k : ℤ) + 2 := ⟨(z - 2).toNat, by omega⟩
        have e : (q : E) / (q : E) ^ z = ((q : E) ^ (k + 1))⁻¹ := by
          have e1 : (q : E) ^ z = (q : E) ^ (k + 1) * (q : E) := by
            rw [hk, ← pow_succ, ← zpow_natCast]; congr 1
          rw [e1, div_mul_eq_div_div_swap, div_self hqE, one_div]
        have hni : ¬ IntAt P ((q : E) / (q : E) ^ z) := by
          rintro ⟨r, s, hs, hrs⟩
          apply hs
          have h2 : algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E (r * ((q : ℕ) : 𝓞 E) ^ (k + 1)) := by
            rw [map_mul, ← hrs, e, map_pow, map_natCast, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hqE), mul_one]
          rw [(FaithfulSMul.algebraMap_injective (𝓞 E) E) h2]
          exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hq _ (Nat.succ_pos k))
        rw [reduction_eq_zero_of_not_integral P hni] at h; exact hnu h
    · rintro rfl
      rw [zpow_one, div_self hqE]
      have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
      rw [h3, reduction_coe, map_one]; exact isUnit_one
  unfold LocE.vP
  have h4 : (fun z : ℤ => IsUnit (redP P ((q : E) / (q : E) ^ z))) = fun z => z = 1 := funext fun z => propext (key z)
  rw [h4]
  exact Classical.epsilon_spec (p := fun z : ℤ => z = 1) ⟨1, rfl⟩

theorem locChar_q {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (h0 : 0 < q) (cq : K)
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.locChar q cq χ (q : E) = cq := by
  have hqE : (q : E) ≠ 0 := by exact_mod_cast h0.ne'
  have h1 : redP P (1 : E) = 1 := by
    have h3 : (1 : E) = algebraMap (𝓞 E) E 1 := (map_one _).symm
    rw [h3, reduction_coe, map_one]
  have hu : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.locChar
  rw [valuation_self P q hq h0, zpow_one, zpow_one, div_self hqE]
  unfold LocE.unitV
  rw [dite_eq_left hu]
  have h2 : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h1]; rfl)
  rw [h2, map_one, Units.val_one, mul_one]

end Arith

section Chain
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem muAt_unit (hP : P.1 ∉ Pr.vGs) (i : ℕ) {a : X.E} (ha : IsUnit (redP P.1 a)) :
    muAt Ch sel mu cst i P a = LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1)⁻¹ a := by
  unfold muAt
  rw [if_neg hP]
  exact GlobalTheory.LastSteps.locChar_unit _ _ ha

theorem muAt_q (hP : P.1 ∉ Pr.vGs) (i : ℕ) (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal) (h0 : 0 < qOf P.1) :
    muAt Ch sel mu cst i P ((qOf P.1 : ℕ) : X.E) = cst.muq (i + 1) P := by
  unfold muAt
  rw [if_neg hP]
  exact locChar_q _ hq h0 _ _

end Chain

theorem exists_twData : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  intro X Pr R Ch sel S₀ mu cst L G s hL P hP k _ _ _ _ ι ϖ hc hϖ ψ hψc hψ1 hψt μ hμ
  have hm : R.m = s + 2 := hL.hm
  have hm0 : 0 < R.m := by omega
  have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.SymBridge.ComplRes.q_ne_zero hc
  have hqpos : 0 < qOf P.1 := Nat.pos_of_ne_zero fun h => hq0 (by rw [h, Nat.cast_zero])
  have hqmem : ((qOf P.1 : ℕ) : 𝓞 X.E) ∈ P.1.asIdeal := GlobalTheory.SymBridge.ComplRes.q_mem hc
  have hμ1 : ∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ 1 u : ℂ) = G.σ₀ (muAt Ch sel mu cst 0 P a) :=
    fun a u h => (hμ 0 hm0).1 a u h
  have ht1 : IsTame (μ 1) := (hμ 0 hm0).2

  have hunit : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = μ 1 x := by
    intro i hi x hx
    obtain ⟨a, ha⟩ := exists_near hc.dense (x : k)
    have hva : valuation k (ι a) = 1 := by
      have e : ι a = (ι a - x) + x := by ring
      rw [e, Valuation.map_add_eq_of_lt_right _ (by rw [hx]; exact ha), hx]
    have ha0 : ι a ≠ 0 := by
      intro h0; rw [h0, map_zero] at hva; exact zero_ne_one hva
    have hint : IntAt P.1 a := GlobalTheory.SymBridge.ComplRes.intAt_of_v hc (le_of_eq hva)
    have hred : IsUnit (redP P.1 a) := (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ hint).mp hva
    have hn : valuation k (((Units.mk0 (ι a) ha0 : kˣ) : k) - x) < 1 := ha
    rw [← tame_near (hμ i hi).2 hx hn, ← tame_near ht1 hx hn]
    apply Units.ext
    rw [(hμ i hi).1 a _ rfl, hμ1 a _ rfl, muAt_unit Ch sel mu cst P hP i hred, muAt_unit Ch sel mu cst P hP 0 hred]
  have hδ : ∀ i, i < R.m → ∀ x : kˣ, valuation k (x : k) = 1 → μ (i + 1) x = delta (μ 1) ϖ x := by
    intro i hi x hx
    rw [delta_unit _ _ hx]; exact hunit i hi x hx

  have hsq : G.σ₀ (cst.sq P) ^ 2 = ((Real.sqrt (qOf P.1) : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, hL.cst_ok.sq_sq P, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Complex.ofReal_natCast]
  obtain ⟨sg, hsg1, hsg2⟩ : ∃ sg : ℂ, (sg = 1 ∨ sg = -1) ∧ G.σ₀ (cst.sq P) = sg * (Real.sqrt (qOf P.1) : ℂ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  refine ⟨⟨ϖ, hϖ, ψ, hψc, hψ1, delta (μ 1) ϖ, delta_tame ht1 ϖ, eta μ R.m (delta (μ 1) ϖ),
    eta_unram μ R.m _ hδ, sg⟩, ⟨hP, hm, hc, ?_, ?_, ?_, hsg2⟩, rfl, rfl, fun i hi => eta_mul μ R.m _ hi, hsg1⟩
  ·
    intro a ha
    show (ψ (ι a) : ℂ) = G.σ₀ (cst.psi P a)
    have hxi : IntAt P.1 G.xi0 := (hL.xiUnitAtPrime P).1
    have hx : valuation k (ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a))) ≤ 1 :=
      GlobalTheory.SymBridge.ComplRes.v_le_one hc (hxi.mul ha)
    obtain ⟨i, -, hi⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep hc hϖ (cst.D P) _ hx
    have hqk : ((qOf P.1 : ℕ) : k) ≠ 0 := by
      rw [← GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]; exact ϖ.ne_zero
    have hint : IntAt P.1 (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) := by
      apply GlobalTheory.SymBridge.ComplRes.intAt_of_v hc
      have e : ι (G.xi0 * ((qOf P.1 : X.E) ^ cst.D P * a)) - (i : k) =
          ι (G.xi0 * a - ((i : ℤ) : X.E) / (qOf P.1 : X.E) ^ cst.D P) * (ϖ : k) ^ cst.D P := by
        rw [GlobalTheory.SymBridge.ComplRes.unif_eq_cast hc]
        simp only [map_mul, map_sub, map_div₀, map_pow, map_intCast, map_natCast]
        push_cast
        field_simp
      rw [e, map_mul, map_pow] at hi
      have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) ^ cst.D P :=
        pow_pos (zero_lt_iff.mpr (by simp)) _
      exact le_of_mul_le_mul_right (by rwa [one_mul]) h0
    rw [hψt a (i : ℤ) (cst.D P) hint, hL.weil P a (i : ℤ) ha hint]
  ·
    intro a u ha hr hu
    show ((delta (μ 1) ϖ u : ℂˣ) : ℂ) = _
    have hva : valuation k (u : k) = 1 := by
      rw [hu]; exact (GlobalTheory.SymBridge.ComplRes.v_eq_one_iff_red hc hϖ ha).mpr hr
    rw [delta_unit _ _ hva, hμ1 a u hu, muAt_unit Ch sel mu cst P hP 0 hr, unitV_inv, map_inv₀]
  ·
    intro i hi
    show ((eta μ R.m (delta (μ 1) ϖ) (i + 1) * delta (μ 1) ϖ) ϖ : ℂ) = _
    rw [eta_mul μ R.m _ hi, (hμ i hi).1 ((qOf P.1 : ℕ) : X.E) ϖ hc.unif, muAt_q Ch sel mu cst P hP i hqmem hqpos]

end GlobalTheory.TwBridgeInhab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompletionTwistDataChainColumnsStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.TwBridgeInhab in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completionTwistData_chainColumns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (s : ℕ), L.Ok Ch sel mu cst G s → ∀ (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P.1 (qOf P.1) ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ ψ : AddChar k Circle, Continuous ψ → HasConductor ψ 1 → (∀ (a : X.E) (b : ℤ) (n : ℕ), IntAt P.1 (G.xi0 * a - (b : X.E) / (qOf P.1 : X.E) ^ n) → (ψ (ι a) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (qOf P.1 : ℂ) ^ n)) → ∀ μ : ℕ → kˣ →* ℂˣ, (∀ i, i < R.m → (∀ (a : X.E) (u : kˣ), (u : k) = ι a → (μ (i + 1) u : ℂ) = G.σ₀ (muAt Ch sel mu cst i P a)) ∧ IsTame (μ (i + 1))) → ∃ W : TwData k, AtTwist (R := R) sel mu cst G.σ₀ P ι s W ∧ W.ϖ = ϖ ∧ W.ψ = ψ ∧ (∀ i, i < R.m → W.η (i + 1) * W.δ = μ (i + 1)) ∧ (W.sg = 1 ∨ W.sg = -1) := by
  exact @_root_.GlobalTheory.TwBridgeInhab.exists_twData
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowJoin

open GlobalTheory.TwBridge GlobalTheory.StepData GlobalTheory.SplitWeil

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

theorem idxProd (hI : I.Ok) (hT : I.IsTw) (a : I.ι) : IdxProd I.sel (I.tup a) (I.cst a) (I.idx a) := by
  have h := hI.idx_ok a
  rw [(hT a).2] at h ⊢
  exact GlobalTheory.T.twistIndexData_representative_dependsOnDoubleCoset _ _ _ _ _ _ _ _ _ _ h

theorem h_one (hT : I.IsTw) (a : I.ι) : ∀ j b (P : BadPr I a), P.1 ∈ (B.primes X).vGs → (I.idx a).h j b P = 1 := by
  rw [(hT a).2]
  exact Formalism.L2.Col.twSt_h_g I.Ch I.sel (I.tup a) (I.cst a) _

theorem get_bij {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} (hA : A.Is) (j : ℕ) (hj : j + 1 < B.R.m) :
    Function.Bijective fun β : Ch₀ j => (A.b0 j β).get (by omega) := by
  have h0 : ∀ p : PtAt B.R I.sel (I.tup a) (I.cst a) u j, cosetIn p = fun _ => ∅ := fun p => by
    have h := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj.ne] at h
    funext P
    rw [cosetIn, show p.1.2 = ∅ from h]
    simp
  refine ⟨fun β β' e => hA.chart_ext j (by omega) β β' ?_ ((h0 _).trans (h0 _).symm), fun b => ?_⟩
  · rw [← (A.b0 j β).of_get (by omega) (by omega), ← (A.b0 j β').of_get (by omega) (by omega)]
    exact congrArg (Idx.of · _) e
  · haveI : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
    letI := B.fields.starE
    obtain ⟨p, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := j) (Formalism.L2.Col.DecoF.base _ _ _ _ _)
    refine ⟨A.chOf j ((I.stp u a j).cl (Idx.of b (by omega)) p), ?_⟩
    exact Idx.get_eq (congrArg Subtype.val (hA.rep j (by omega) _).1.symm) _

section Place

variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E}

structure Good (P : BadPr I a) (G : QGeo v Bs PP) {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ) (hψ : Continuous G.ψk)
    (sg : ℂ) : Prop where
  sign : sg = 1 ∨ sg = -1
  tw : AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (I.rec7 l Z))) G.s (E.tw hψ sg)
  M : E.M = (I.cst a).M
  up : ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j))
  rat : ∀ j d h, Nonempty ((I.idx a).β j) → E.A j d h =
    {g | ∃ b, IsGL (X := B.fields) (R := B.R) (k := G.k) (G.q.pr.comp (incA (I.rec7 l Z))) ((I.idx a).h j b P) g}
  next : ∀ j d (h : j + 1 + d = G.s), Nonempty ((I.idx a).β j) → (E.A (j + 1) d h).Nonempty →
    ∃ γ : Formalism.L2.Col.AutY B.fields B.R (j + 1), Bdd (B.primes X) (j + 1) P.1 γ ∧
      ∃ al, Formalism.L2.Col.FiniteSumNonzeroLargeDepth I.Ch I.sel (I.tup a) (I.cst a) j P ((I.idx a).h j al P) γ


set_option maxHeartbeats 1000000 in
theorem exists_good (hI : I.Ok) (hT : I.IsTw) (P : BadPr I a) (hP : P.1 ∉ (B.primes X).vGs) (G : QGeo v Bs PP) (heq : PP = P.1) (hc : c.Is)
    (hstd : IsStdChar (I.rec7 l Z) c.ψ (-1)) (χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle)
    (hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (χ j) (I.C.mu0 ⟨j, hj⟩ * I.xi a)) :
    ∃ (E : QExt G χ) (hψ : Continuous G.ψk) (sg : ℂ), Good P G E hψ sg := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have hcp : GlobalTheory.SymBridge.IsCompl (E := B.fields.E) P.1 (Formalism.L2.Col.qOf P.1) (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ := heq ▸ G.compl
  have hid : Formalism.L2.NTheta.IsIdemAt (D := I.rec7 l Z) G.q.e P.1 := heq ▸ G.idem
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = G.s by omega] at hL
  obtain ⟨-, -, -, -, hcomp⟩ := GlobalTheory.LocChar.weil_char_split (I.rec7 l Z) G.k (ofSplit G.q) c.ψ hstd
  choose μ hμ using fun j => hcomp (χ (j - 1))⁻¹
  have hψ := continuous_of_cond G.cond
  have hd := TC.degOne_of_ok hI a P
  obtain ⟨⟨ϖ, unif, ψ, cont, cond, δ, tame, η, unr, sg⟩, hA, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.exists_completionTwistData_chainColumns _ _ _ _ _ _ _ _ _ _ _ hL P hP G.k (G.q.pr.comp (incA (I.rec7 l Z))) G.ϖ hcp G.unif G.ψk hψ G.cond
      (GlobalTheory.T.weilCharacter_splitDegreeOne_place_eq_exp (I.rec7 l Z) G.k G.q P.1 hid hd.1 hd.2 hcp.int c.ψ hstd G.ψk G.char) μ
      fun i hi => GlobalTheory.T.step_inverse_character_local_component_chain_tame I hI l Z a P hP G.k G.q hid hcp.int hcp.dense i hi (χ i) (hχ i hi) _ (hμ (i + 1))
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  have hM : G.s + 1 ≤ (I.cst a).M := by
    rw [hT.cst_eq]
    show _ ≤ B.R.m
    omega
  obtain ⟨A, a1, a2, a3, a4⟩ := exists_system G.unitVol hA hL (idxProd hI hT a) hM
  have hmu : ∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ) := fun j hj => by
    rw [h3 j (by omega)]
    exact hμ (j + 1)
  obtain ⟨E₀, rfl, rfl, rfl, e4⟩ := GlobalTheory.T.exists_extGeometry_tuple_of_representatives _ c v Bs _ G χ hc δ tame η unr hmu A a1 _ a2
  obtain ⟨E, e1, e2, e3, e5, -, e6⟩ := GlobalTheory.T.exists_splitPlaceGeometryExtension_cosetOrbitReps _ c v Bs _ G χ hc _ tame _ unr hmu _ a1 _ a2 (E₀.Ch (G.s + 1))
    (fun y => (E₀.cos y).out ∘ id) (fun y y' h => E₀.cos_inj y y' (by
      rw [← e4] at h
      simpa only [Function.comp_id, Submodule.Quotient.mk_out] using h))
    (fun z hz => by
      rw [← e4] at hz ⊢
      simpa only [Function.comp_id, Submodule.Quotient.mk_out] using E₀.cos_all z hz)
  refine ⟨E, hψ, sg, h4, ?_, e5, e6, e3 ▸ a3, e3 ▸ a4⟩
  have e7 : E.tw hψ sg = ⟨G.ϖ, unif, G.ψk, cont, cond, E₀.δ, tame, E₀.η, unr, sg⟩ := by simp only [QExt.tw, e1, e2]
  rw [e7]
  exact hA

theorem res_of_tw (hI : I.Ok) {hP : PP ∈ Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)} {G : QGeo v Bs PP} {W : TwData G.k}
    (h : AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL ⟨PP, hP⟩ (G.q.pr.comp (incA (I.rec7 l Z))) G.s W)
    {ξ : (kP PP)ˣ →* ℂˣ} (hξ : IsRes (I.xi a) PP ξ) : G.Res W.δ ξ := by
  intro z x r hx hr
  have h0 : (z : (I.rec7 l Z).host.E) ≠ 0 := fun e => x.ne_zero (by rw [hx, e]; exact (G.q.pr.comp (incA (I.rec7 l Z))).map_zero)
  have h1 : Formalism.L2.Col.redP PP (z : (I.rec7 l Z).host.E) = (r : kP PP) := (Formalism.L2.Col.reduction_coe PP z).trans hr.symm
  have h2 : IsUnit (Formalism.L2.Col.redP PP (z : (I.rec7 l Z).host.E)) := h1 ▸ r.isUnit
  have h3 : Formalism.L2.Col.IntAt PP (z : (I.rec7 l Z).host.E) :=
    ⟨z, 1, fun e => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 e), by simp⟩
  have h4 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads a)
    (GlobalTheory.Mem.ReadTwist.tameAt (hI.xi_reads a) fun v => Subgroup.mem_iInf.1 (I.tup a).2.1.2 v) PP h2.unit z (Units.mk0 _ h0) rfl
    (hr.symm.trans h1.symm)
  refine Units.ext ((h.del _ x h3 h2 hx).trans ?_)
  rw [hξ z (Units.mk0 _ h0) r rfl hr, Units.val_inv_eq_inv_val]
  exact congrArg _ ((congrArg _ (dif_pos h2)).trans h4)

end Place


end GlobalTheory.LowJoin

end
