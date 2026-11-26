module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GlueHoldsVar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocalAssemblyPrincipal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.IdemMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WFrameOf

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WeilBasisExistence
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HGZeroRight
noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WB

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_def (x y : Fin I.n → I.E) : hG I x y = ∑ i, ∑ j, star (x i) * I.J i j * y j := rfl

theorem hG_add_right (x y z : Fin I.n → I.E) : hG I x (y + z) = hG I x y + hG I x z := by
  simp only [hG_def, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hG_smul_right (c : I.E) (x y : Fin I.n → I.E) : hG I x (c • y) = c * hG I x y := by
  simp only [hG_def, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hG_zero_right (x : Fin I.n → I.E) : hG I x 0 = 0 := by simp [hG_def]

theorem hG_sum_right {ι : Type*} (s : Finset ι) (x : Fin I.n → I.E) (y : ι → Fin I.n → I.E) :
    hG I x (∑ t ∈ s, y t) = ∑ t ∈ s, hG I x (y t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hG_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hG_add_right, ih]

theorem J_entry (i j : Fin I.n) : star (I.J j i) = I.J i j := by
  have h := congrFun (congrFun I.J_herm i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h
  exact h

theorem hG_symm (x y : Fin I.n → I.E) : hG I y x = star (hG I x y) := by
  simp only [hG_def, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [J_entry]
  ring

variable {I}

end PI.ScRefExists.WB
end
end

noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WB

variable (I : Formalism.MainNotions.S.AutInst)

theorem smul_Ap {p : ℕ} (c : Ap I p) (x : Fin I.n → I.E) : c • x = (c : I.E) • x := rfl

def WA (p r : ℕ) (e f : Fin r → Fin I.n → I.E) : Submodule (Ap I p) (Fin I.n → I.E) :=
  LA I p ⊓
  { carrier := {x | ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0}
    add_mem' := by
      intro x y hx hy
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      intro a
      exact ⟨by rw [hG_add_right, (hx a).1, (hy a).1, add_zero],
        by rw [hG_add_right, (hx a).2, (hy a).2, add_zero]⟩
    zero_mem' := by
      simp only [Set.mem_setOf_eq]
      intro a
      exact ⟨hG_zero_right I _, hG_zero_right I _⟩
    smul_mem' := by
      intro c x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      intro a
      exact ⟨by rw [smul_Ap, hG_smul_right, (hx a).1, mul_zero],
        by rw [smul_Ap, hG_smul_right, (hx a).2, mul_zero]⟩ }

theorem mem_WA {p r : ℕ} {e f : Fin r → Fin I.n → I.E} {x : Fin I.n → I.E} :
    x ∈ WA I p r e f ↔ x ∈ LA I p ∧ ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0 := Iff.rfl

theorem LA_fg (p : ℕ) : (LA I p).FG := by
  obtain ⟨s, hs⟩ := I.L_fg
  refine ⟨s, ?_⟩
  unfold LA
  rw [← hs, Submodule.span_span_of_tower]

theorem span_Ap_le {p : ℕ} (s : Set (Fin I.n → I.E)) {x : Fin I.n → I.E}
    (hx : x ∈ Submodule.span (Ap I p) s) : x ∈ Submodule.span I.E s := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy => rw [smul_Ap]; exact Submodule.smul_mem _ _ hy

theorem WA_finite {p r : ℕ} (e f : Fin r → Fin I.n → I.E) [IsPrincipalIdealRing (Ap I p)] :
    Module.Finite (Ap I p) (WA I p r e f) := by
  have hle : WA I p r e f ≤ LA I p := fun x hx => (mem_WA I).mp hx |>.1
  haveI : IsNoetherian (Ap I p) (LA I p) := isNoetherian_of_fg_of_noetherian _ (LA_fg I p)
  have hfg : ((WA I p r e f).comap (LA I p).subtype).FG := IsNoetherian.noetherian _
  have hmap : ((WA I p r e f).comap (LA I p).subtype).map (LA I p).subtype = WA I p r e f := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  rw [Module.Finite.iff_fg, ← hmap]
  exact hfg.map _

theorem weil_basis_existence : WBasis := by
  intro I p r k e f M hp hPID hn hee hff hef hM hMe
  haveI := hPID
  have hfe : ∀ a b, hG I (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hG_symm, hef]
    by_cases h : b = a
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  let φ : (Fin I.n → I.E) →ₗ[I.E] (Fin r → I.E) × (Fin r → I.E) :=
    { toFun := fun x => (fun a => hG I (e a) x, fun a => hG I (f a) x)
      map_add' := fun x y => by
        refine Prod.ext (funext fun a => ?_) (funext fun a => ?_) <;> simp [hG_add_right]
      map_smul' := fun c x => by
        refine Prod.ext (funext fun a => ?_) (funext fun a => ?_) <;> simp [hG_smul_right] }
  have hφ : ∀ x, x ∈ LinearMap.ker φ ↔ ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0 := by
    intro x
    simp only [LinearMap.mem_ker, φ, LinearMap.coe_mk, AddHom.coe_mk, Prod.ext_iff, funext_iff,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
    exact ⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨s, t⟩
    refine ⟨∑ b, (s b • f b + t b • e b), ?_⟩
    refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · simp [φ, hG_sum_right, hG_add_right, hG_smul_right, hef, hee, Prod.fst_sum, Finset.sum_apply]
    · simp [φ, hG_sum_right, hG_add_right, hG_smul_right, hfe, hff, Prod.snd_sum, Finset.sum_apply]
  have hker : Module.finrank I.E (LinearMap.ker φ) = k + 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h1
    omega
  have hNZ : NoZeroSMulDivisors (Ap I p) (WA I p r e f) := by
    refine ⟨fun {c x} h => ?_⟩
    have h2 : (c : I.E) • (x : Fin I.n → I.E) = 0 := by
      have := congrArg Subtype.val h
      simpa [smul_Ap] using this
    rcases smul_eq_zero.1 h2 with h3 | h3
    · left; exact Subtype.ext h3
    · right; exact Subtype.ext h3
  haveI := hNZ
  haveI := WA_finite I (p := p) e f
  haveI : Module.Free (Ap I p) (WA I p r e f) := Module.free_of_finite_type_torsion_free'
  have hLI : ∀ {ι : Type} [Fintype ι] (bb : Module.Basis ι (Ap I p) (WA I p r e f)),
      LinearIndependent I.E (fun j => ((bb j : WA I p r e f) : Fin I.n → I.E)) := by
    intro ι _ bb
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 I.E)) Finset.univ g
    choose a ha using fun i => hdd i (Finset.mem_univ i)
    have hsum : ∑ i, (⟨algebraMap (𝓞 I.E) I.E (a i), (Ap I p).algebraMap_mem (a i)⟩ : Ap I p) • bb i = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, smul_Ap, ZeroMemClass.coe_zero]
      have : ∑ i, ((dd : 𝓞 I.E) : I.E) • (g i • ((bb i : WA I p r e f) : Fin I.n → I.E)) = 0 := by
        rw [← Finset.smul_sum, hg, smul_zero]
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ha i, Algebra.smul_def]
      rfl
    have hz := (Fintype.linearIndependent_iff.1 bb.linearIndependent) _ hsum j
    have h0 : algebraMap (𝓞 I.E) I.E (a j) = 0 := congrArg Subtype.val hz
    rw [ha j, Algebra.smul_def] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exfalso
      have hd0 : (dd : 𝓞 I.E) ≠ 0 := nonZeroDivisors.coe_ne_zero dd
      exact hd0 (by simpa using h1)
    · exact h1
  have hL_le : ∀ y ∈ I.L, y ∈ LA I p := fun y hy => Submodule.subset_span hy
  have hclear : ∀ x : Fin I.n → I.E, ∃ d : 𝓞 I.E, d ≠ 0 ∧ ((d : I.E) • x) ∈ I.L := by
    intro x
    obtain ⟨s, hs⟩ := I.L_fg
    have hx : x ∈ Submodule.span I.E (s : Set (Fin I.n → I.E)) := by
      have h1 : Submodule.span I.E (s : Set (Fin I.n → I.E)) = ⊤ := by
        rw [← I.L_span, ← hs, Submodule.span_span_of_tower]
      rw [h1]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_finset).1 hx
    obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 I.E)) s c
    choose a ha using hdd
    refine ⟨dd, nonZeroDivisors.coe_ne_zero dd, ?_⟩
    rw [← hc.2, Finset.smul_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [smul_smul]
    have h2 : ((dd : 𝓞 I.E) : I.E) * c y = algebraMap (𝓞 I.E) I.E (a y hy) := by
      rw [ha y hy, Algebra.smul_def]
    rw [h2, algebraMap_smul]
    exact I.L.smul_mem _ (hs ▸ Submodule.subset_span hy)
  let b := Module.finBasis (Ap I p) (WA I p r e f)
  have hspan : Submodule.span I.E (Set.range fun j => ((b j : WA I p r e f) : Fin I.n → I.E)) =
      LinearMap.ker φ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (hφ _).2 ((mem_WA I).mp (b j).2).2
    · intro x hx
      obtain ⟨d, hd, hdx⟩ := hclear x
      have hWA : (d : I.E) • x ∈ WA I p r e f := by
        refine (mem_WA I).mpr ⟨hL_le _ hdx, fun a => ?_⟩
        have := ((hφ x).1 hx) a
        rw [hG_smul_right, hG_smul_right, this.1, this.2, mul_zero]
        exact ⟨rfl, rfl⟩
      have h1 : ((d : I.E) • x) ∈ Submodule.span (Ap I p)
          (Set.range fun j => ((b j : WA I p r e f) : Fin I.n → I.E)) := by
        have hm := b.mem_span (⟨(d : I.E) • x, hWA⟩ : WA I p r e f)
        have := Submodule.apply_mem_span_image_of_mem_span (WA I p r e f).subtype hm
        rwa [← Set.range_comp] at this
      have h2 := span_Ap_le I _ h1
      have hdE : (d : I.E) ≠ 0 := by simpa using hd
      have := Submodule.smul_mem _ ((d : I.E)⁻¹) h2
      rwa [smul_smul, inv_mul_cancel₀ hdE, one_smul] at this
  have hm : Module.finrank (Ap I p) (WA I p r e f) = k + 1 := by
    have h1 := (linearIndependent_iff_card_eq_finrank_span.1 (hLI b))
    rw [Fintype.card_fin] at h1
    unfold Set.finrank at h1
    rw [hspan, hker] at h1
    exact h1
  let b' := b.reindex (finCongr hm)
  refine ⟨fun i => ((b' i : WA I p r e f) : Fin I.n → I.E), fun i => (mem_WA I).mp (b' i).2, hLI b', ?_⟩
  intro x hxL hxo
  have hWA : x ∈ WA I p r e f := (mem_WA I).mpr ⟨hxL, hxo⟩
  have hm2 := b'.mem_span (⟨x, hWA⟩ : WA I p r e f)
  have := Submodule.apply_mem_span_image_of_mem_span (WA I p r e f).subtype hm2
  rwa [← Set.range_comp] at this

end PI.ScRefExists.WB
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.TargetOfWframe
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.ThetaSeriesExistence
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain

namespace PI.ScRefExists.TH

variable (I : Formalism.MainNotions.S.AutInst)

theorem spanG_ne (g : ℕ) (hg : 1 ≤ g) : Ideal.span {(g : 𝓞 I.E)} ≠ 0 := by
  have hg0 : (g : 𝓞 I.E) ≠ 0 := by
    intro h
    have h2 := congrArg (fun x : 𝓞 I.E => (x : I.E)) h
    have h3 : (g : I.E) = 0 := by simpa using h2
    have h4 : g = 0 := by exact_mod_cast h3
    omega
  rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact hg0

def primesG (g : ℕ) (hg : 1 ≤ g) : Finset (HeightOneSpectrum (𝓞 I.E)) :=
  (Ideal.finite_factors (spanG_ne I g hg)).toFinset

theorem mem_primesG (g : ℕ) (hg : 1 ≤ g) (P : HeightOneSpectrum (𝓞 I.E)) :
    P ∈ primesG I g hg ↔ (g : 𝓞 I.E) ∈ P.asIdeal := by
  unfold primesG
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]

theorem prod_le_radical (g : ℕ) (hg : 1 ≤ g) :
    (∏ P ∈ primesG I g hg, P.asIdeal) ≤ (Ideal.span {(g : 𝓞 I.E)}).radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J hJ => ?_
  obtain ⟨hJle, hJp⟩ := hJ
  have hgJ : (g : 𝓞 I.E) ∈ J := hJle (Ideal.mem_span_singleton_self _)
  have hJ0 : J ≠ ⊥ := by
    intro h
    apply spanG_ne I g hg
    rw [Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rw [h] at hgJ
    exact (Submodule.mem_bot _).mp hgJ
  let Q : HeightOneSpectrum (𝓞 I.E) := ⟨J, hJp, hJ0⟩
  have hQ : Q ∈ primesG I g hg := (mem_primesG I g hg Q).mpr hgJ
  exact Ideal.prod_le_inf.trans (Finset.inf_le hQ)

private lemma sk_GE_of_mem_span_natCast (g : ℕ) (z : 𝓞 I.E) (hz : z ∈ Ideal.span {(g : 𝓞 I.E)}) :
    PI.ScRefExists.Sk.GE I g (z : I.E) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨t, ?_⟩
  rw [← ht]
  first
    | (push_cast; ring)
    | simp [mul_comm]

theorem theta_series_existence : PI.ScRefExists.Sk.ThetaEx := by
  intro I g hg hS
  classical
  letI : LinearOrder (HeightOneSpectrum (𝓞 I.E)) := by
    first
      | exact linearOrderOfSTO WellOrderingRel
      | exact IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (∏ P ∈ primesG I g hg, P.asIdeal) ^ N ≤ Ideal.span {(g : 𝓞 I.E)} := by
    first
      | exact Ideal.exists_pow_le_of_le_radical_of_fg (prod_le_radical I g hg) (IsNoetherian.noetherian _)
      | exact Ideal.exists_pow_le_of_le_radical_of_fg (IsNoetherian.noetherian _) (prod_le_radical I g hg)
  obtain ⟨θ, hθ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := primesG I g hg)
    (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal) (fun _ => N) (fun P _ => P.prime)
    (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))
    (fun P => if (P : HeightOneSpectrum (𝓞 I.E)) < cj I P then (1 : 𝓞 I.E) else 0)
  have h1 : ∀ P ∈ primesG I g hg, P < cj I P → θ - 1 ∈ P.asIdeal ^ N := by
    intro P hP h
    simpa [h] using hθ P hP
  have h0 : ∀ P ∈ primesG I g hg, ¬ P < cj I P → θ ∈ P.asIdeal ^ N := by
    intro P hP h
    simpa [h] using hθ P hP
  have hcjS : ∀ P ∈ primesG I g hg, cj I P ∈ primesG I g hg := by
    intro P hP
    rw [mem_primesG] at hP ⊢
    rw [mem_cj, map_natCast]
    exact hP
  have hsg : ∀ (P : HeightOneSpectrum (𝓞 I.E)) (z : 𝓞 I.E), z ∈ (cj I P).asIdeal ^ N →
      sg I z ∈ P.asIdeal ^ N := by
    intro P z hz
    have h2 := Ideal.mem_map_of_mem (sg I) hz
    rwa [Ideal.map_pow, show (cj I P).asIdeal = P.asIdeal.comap (sg I) from rfl,
      Ideal.map_comap_of_surjective _ (fun y => ⟨sg I y, sg_sg I y⟩)] at h2
  have hloc : ∀ P ∈ primesG I g hg, θ * θ - θ ∈ P.asIdeal ^ N ∧ θ * sg I θ ∈ P.asIdeal ^ N ∧
      1 - θ - sg I θ ∈ P.asIdeal ^ N := by
    intro P hP
    have hne : cj I P ≠ P := cj_ne I g hg hS P ((mem_primesG I g hg P).mp hP)
    by_cases hlt : P < cj I P
    · have ha := h1 P hP hlt
      have hb : θ ∈ (cj I P).asIdeal ^ N :=
        h0 (cj I P) (hcjS P hP) (by rw [cj_cj]; exact lt_asymm hlt)
      have hb' := hsg P θ hb
      refine ⟨?_, ?_, ?_⟩
      · have e : θ * θ - θ = (θ - 1) * θ := by ring
        rw [e]
        exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_left _ _ hb'
      · have e : 1 - θ - sg I θ = -(θ - 1) - sg I θ := by ring
        rw [e]
        exact Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'
    · have ha := h0 P hP hlt
      have hlt' : cj I P < cj I (cj I P) := by
        rw [cj_cj]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have hb' := hsg P _ (h1 (cj I P) (hcjS P hP) hlt')
      rw [map_sub, map_one] at hb'
      refine ⟨?_, ?_, ?_⟩
      · have e : θ * θ - θ = θ * (θ - 1) := by ring
        rw [e]
        exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_right _ _ ha
      · have e : 1 - θ - sg I θ = -θ - (sg I θ - 1) := by ring
        rw [e]
        exact Ideal.sub_mem _ (Submodule.neg_mem _ ha) hb'
  have key : (primesG I g hg).inf (fun P : HeightOneSpectrum (𝓞 I.E) => P.asIdeal ^ N) =
      (∏ P ∈ primesG I g hg, P.asIdeal) ^ N := by
    rw [← Finset.prod_pow]
    exact IsDedekindDomain.inf_pow_eq_prod_of_prime _ _ _ (fun P _ => P.prime)
      (fun P _ Q _ h e => h (HeightOneSpectrum.ext e))
  have hmem : ∀ z : 𝓞 I.E, (∀ P ∈ primesG I g hg, z ∈ P.asIdeal ^ N) →
      z ∈ Ideal.span {(g : 𝓞 I.E)} := by
    intro z hz
    apply hN
    rw [← key]
    exact (Ideal.span_singleton_le_iff_mem _).mp
      (Finset.le_inf fun P hP => (Ideal.span_singleton_le_iff_mem _).mpr (hz P hP))
  refine ⟨θ, ?_, ?_, ?_⟩
  · have e : ((θ * θ - θ : 𝓞 I.E) : I.E) = (θ : I.E) * θ - θ := by push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).1)
  · have e : ((θ * sg I θ : 𝓞 I.E) : I.E) = (θ : I.E) * star (θ : I.E) := by
      rw [← sg_coe]; push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.1)
  · have e : ((1 - θ - sg I θ : 𝓞 I.E) : I.E) = 1 - (θ : I.E) - star (θ : I.E) := by
      rw [← sg_coe]; push_cast; ring
    rw [← e]
    exact sk_GE_of_mem_span_natCast I g _ (hmem _ fun P hP => (hloc P hP).2.2)

end PI.ScRefExists.TH
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.GWGlue
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.GWG

open PI.ScRefExists.Sk

section Lemmas

variable (I : Formalism.MainNotions.S.AutInst)

theorem hG_add_left (x y z : Fin I.n → I.E) : hG I (x + y) z = hG I x z + hG I y z := by
  unfold hG Formalism.UG.hform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.add_apply, map_add (f := _)]
  ring

theorem hG_add_right (x y z : Fin I.n → I.E) : hG I x (y + z) = hG I x y + hG I x z := by
  unfold hG Formalism.UG.hform
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.add_apply, map_add (f := _)]
  ring

theorem hG_zsmul_left (q : ℤ) (x y : Fin I.n → I.E) : hG I (q • x) y = (q : I.E) * hG I x y := by
  unfold hG Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
  ring

theorem hG_zsmul_right (q : ℤ) (x y : Fin I.n → I.E) : hG I x (q • y) = (q : I.E) * hG I x y := by
  unfold hG Formalism.UG.hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
  ring

theorem hG_zero_right (x : Fin I.n → I.E) : hG I x 0 = 0 := by
  simp [hG, Formalism.UG.hform]

theorem hG_comb (q₁ q₂ : ℤ) (x₁ x₂ y₁ y₂ : Fin I.n → I.E) :
    hG I (q₁ • x₁ + q₂ • x₂) (q₁ • y₁ + q₂ • y₂) =
      (q₁ : I.E) ^ 2 * hG I x₁ y₁ + (q₁ : I.E) * (q₂ : I.E) * (hG I x₁ y₂ + hG I x₂ y₁) +
        (q₂ : I.E) ^ 2 * hG I x₂ y₂ := by
  simp only [hG_add_left, hG_add_right, hG_zsmul_left, hG_zsmul_right]
  ring

theorem hG_int {x y : Fin I.n → I.E} (hx : x ∈ I.L) (hy : y ∈ I.L) :
    hG I x y ∈ (algebraMap (𝓞 I.E) I.E).range := (I.L_dual y).mp hy x hx

theorem theta_mem (θ : 𝓞 I.E) : (θ : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := ⟨θ, rfl⟩

theorem ite_mem {p : Prop} [Decidable p] :
    (if p then (1 : I.E) else 0) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem osmul_mem {t : I.E} (ht : t ∈ (algebraMap (𝓞 I.E) I.E).range) {v : Fin I.n → I.E}
    (hv : v ∈ I.L) : t • v ∈ I.L := by
  obtain ⟨s, rfl⟩ := ht
  rw [algebraMap_smul]
  exact I.L.smul_mem s hv

theorem crt_ge {g₁ g₂ : ℕ} {A B q₁ q₂ : ℤ} (hq₁ : q₁ = g₂ * B) (hq₂ : q₂ = g₁ * A)
    {x X₁₁ X₁₂ X₂₂ : I.E} (h₁ : GE I g₁ X₁₁) (h₂ : GE I g₂ X₂₂)
    (h₁₂ : X₁₂ ∈ (algebraMap (𝓞 I.E) I.E).range)
    (hx : x = (q₁ : I.E) ^ 2 * X₁₁ + (q₁ : I.E) * (q₂ : I.E) * X₁₂ + (q₂ : I.E) ^ 2 * X₂₂) :
    GE I (g₁ * g₂) x := by
  obtain ⟨t1, ht1⟩ := h₁
  obtain ⟨t2, ht2⟩ := h₂
  obtain ⟨s, hs⟩ := h₁₂
  have hc : ∀ u : 𝓞 I.E, (u : I.E) = algebraMap (𝓞 I.E) I.E u := fun u => rfl
  refine ⟨(g₂ : 𝓞 I.E) * (B : 𝓞 I.E) ^ 2 * t1 + (B : 𝓞 I.E) * (A : 𝓞 I.E) * s +
    (g₁ : 𝓞 I.E) * (A : 𝓞 I.E) ^ 2 * t2, ?_⟩
  rw [hx, hq₁, hq₂, ht1, ht2, ← hs]
  simp only [hc, map_add (f := _), map_mul, map_pow, map_natCast, map_intCast]
  push_cast
  try ring

theorem ge_one {x : I.E} (hx : x ∈ (algebraMap (𝓞 I.E) I.E).range) : GE I 1 x := by
  obtain ⟨s, rfl⟩ := hx
  exact ⟨s, by rw [Nat.cast_one, one_mul]⟩

def SS (r k M : ℕ) (e f : Fin r → Fin I.n → I.E) (θ : 𝓞 I.E) (z : Fin I.n → I.E)
    (b bd : Fin k → Fin I.n → I.E) : Set (Fin I.n → I.E) :=
  Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪
    Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)

theorem gL_mem (G : ℕ) {x : Fin I.n → I.E} (hx : x ∈ I.L) : (G : I.E) • x ∈ gL I G := Submodule.subset_span ⟨x, hx, rfl⟩

private theorem star_coe_mem_range_algebraMap (θ : 𝓞 I.E) :
    star (θ : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := by
  have h : IsIntegral ℤ (star (θ : I.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe θ).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨star (θ : I.E), h⟩, rfl⟩

theorem side_mem {r k M : ℕ} (e f : Fin r → Fin I.n → I.E) (θ : 𝓞 I.E) (G ga : ℕ) (qa qb w wab : ℤ)
    (z za zb : Fin I.n → I.E) (b ba bb bd bda bdb : Fin k → Fin I.n → I.E)
    (hza : za ∈ I.L) (hzb : zb ∈ I.L)
    (hbL : ∀ i, ba i ∈ I.L ∧ bb i ∈ I.L ∧ bda i ∈ I.L ∧ bdb i ∈ I.L)
    (hsum : (qa : I.E) + (qb : I.E) = 1) (hprod : (qa : I.E) * (qb : I.E) = (G : I.E) * (wab : I.E))
    (hga : (qa : I.E) * (ga : I.E) = (G : I.E) * (w : I.E))
    (hz : z = qa • za + qb • zb) (hb : ∀ i, b i = qa • ba i + qb • bb i)
    (hbd : ∀ i, bd i = qa • bda i + qb • bdb i) {y : Fin I.n → I.E}
    (hsp : y ∈ Submodule.span (𝓞 I.E) (SS I r k M e f θ za ba bda) ⊔ gL I ga) :
    qa • y ∈ Submodule.span (𝓞 I.E) (SS I r k M e f θ z b bd) ⊔ gL I G := by
  set S' := Submodule.span (𝓞 I.E) (SS I r k M e f θ z b bd) ⊔ gL I G with hS'
  have hsp' : ∀ v ∈ SS I r k M e f θ z b bd, v ∈ S' :=
    fun v hv => Submodule.mem_sup_left (Submodule.subset_span hv)
  have hG' : ∀ x ∈ I.L, (G : I.E) • x ∈ S' := fun x hx => Submodule.mem_sup_right (gL_mem I G hx)
  have hzs : ∀ (q : ℤ) {v : Fin I.n → I.E}, v ∈ S' → q • v ∈ S' := fun q v hv => zsmul_mem hv q
  have hwab : (wab : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := ⟨(wab : 𝓞 I.E), by simp⟩
  let φ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    { toFun := fun v => qa • v
      map_add' := fun a c => smul_add qa a c
      map_smul' := fun c v => smul_comm qa c v }
  suffices h : Submodule.span (𝓞 I.E) (SS I r k M e f θ za ba bda) ⊔ gL I ga ≤ S'.comap φ from h hsp
  apply sup_le
  · rw [Submodule.span_le]
    intro v hv
    simp only [SS, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hv
    show qa • v ∈ S'
    rcases hv with ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | hvz) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact hzs qa (hsp' _ (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))))
    · exact hzs qa (hsp' _ (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))))
    · rw [hvz]
      have hv : qa • za = qa • z + (G : I.E) • ((wab : I.E) • (za - zb)) := by
        ext j
        simp only [hz, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination (za j - zb j) * hprod - ((qa : I.E) * za j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' z (Or.inl (Or.inl (Or.inr rfl)))))
        (hG' _ (osmul_mem I hwab (I.L.sub_mem hza hzb)))
    · have hv : qa • ((θ : I.E) • ba i) = qa • ((θ : I.E) • b i) +
          (G : I.E) • ((wab : I.E) • ((θ : I.E) • (ba i - bb i))) := by
        ext j
        simp only [hb, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination (θ : I.E) * (ba i j - bb i j) * hprod - ((θ : I.E) * (qa : I.E) * ba i j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' _ (Or.inl (Or.inr ⟨i, rfl⟩))))
        (hG' _ (osmul_mem I hwab (osmul_mem I (theta_mem I θ) (I.L.sub_mem (hbL i).1 (hbL i).2.1))))
    · have hv : qa • (star (θ : I.E) • bda i) = qa • (star (θ : I.E) • bd i) +
          (G : I.E) • ((wab : I.E) • (star (θ : I.E) • (bda i - bdb i))) := by
        ext j
        simp only [hbd, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
        linear_combination star (θ : I.E) * (bda i j - bdb i j) * hprod -
          (star (θ : I.E) * (qa : I.E) * bda i j) * hsum
      rw [hv]
      exact S'.add_mem (hzs qa (hsp' _ (Or.inr ⟨i, rfl⟩)))
        (hG' _ (osmul_mem I hwab (osmul_mem I (star_coe_mem_range_algebraMap I θ)
          (I.L.sub_mem (hbL i).2.2.1 (hbL i).2.2.2))))
  · rw [gL, Submodule.span_le]
    rintro v ⟨x, hx, rfl⟩
    show qa • ((ga : I.E) • x) ∈ S'
    have hv : qa • ((ga : I.E) • x) = (G : I.E) • ((w : I.E) • x) := by
      ext j
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.intCast_apply, zsmul_eq_mul, smul_eq_mul]
      linear_combination (x j) * hga
    rw [hv]
    exact hG' _ (osmul_mem I ⟨(w : 𝓞 I.E), by simp⟩ hx)

end Lemmas

theorem chinese_remainder_gluing : GWcrt := by
  intro I g₁ g₂ r k θ e f M hcop _ hC1 hC2
  obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨za, ba, bda, hza, hbaL, hoza, hoba, hGa, hTa, hTTa, hspa⟩ := hC1
  obtain ⟨zb, bb, bdb, hzb, hbbL, hozb, hobb, hGb, hTb, hTTb, hspb⟩ := hC2
  set qa : ℤ := (g₂ : ℤ) * B with hqa
  set qb : ℤ := (g₁ : ℤ) * A with hqb
  have hsumZ : qa + qb = 1 := by rw [hqa, hqb]; linarith
  have hsum : (qa : I.E) + (qb : I.E) = 1 := by exact_mod_cast hsumZ
  have hprod : (qa : I.E) * (qb : I.E) = ((g₁ * g₂ : ℕ) : I.E) * ((A * B : ℤ) : I.E) := by
    rw [hqa, hqb]; push_cast; ring
  have hga : (qa : I.E) * (g₁ : I.E) = ((g₁ * g₂ : ℕ) : I.E) * (B : I.E) := by
    rw [hqa]; push_cast; ring
  have hgb : (qb : I.E) * (g₂ : I.E) = ((g₁ * g₂ : ℕ) : I.E) * (A : I.E) := by
    rw [hqb]; push_cast; ring
  have hsum' : (qb : I.E) + (qa : I.E) = 1 := by rw [add_comm]; exact hsum
  have hprod' : (qb : I.E) * (qa : I.E) = ((g₁ * g₂ : ℕ) : I.E) * ((A * B : ℤ) : I.E) := by
    rw [mul_comm]; exact hprod
  have two_mem : (2 : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := ⟨2, map_ofNat _ 2⟩
  refine ⟨qa • za + qb • zb, fun i => qa • ba i + qb • bb i, fun i => qa • bda i + qb • bdb i,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact I.L.add_mem (zsmul_mem hza qa) (zsmul_mem hzb qb)
  · exact fun i => ⟨I.L.add_mem (zsmul_mem (hbaL i).1 qa) (zsmul_mem (hbbL i).1 qb),
      I.L.add_mem (zsmul_mem (hbaL i).2 qa) (zsmul_mem (hbbL i).2 qb)⟩
  · intro a
    obtain ⟨h1, h2⟩ := hoza a
    obtain ⟨h3, h4⟩ := hozb a
    constructor <;> simp only [hG_add_right, hG_zsmul_right, h1, h2, h3, h4, mul_zero, add_zero]
  · intro a i
    obtain ⟨h1, h2, h3, h4⟩ := hoba a i
    obtain ⟨h5, h6, h7, h8⟩ := hobb a i
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [hG_add_right, hG_zsmul_right, h1, h2, h3, h4, h5, h6, h7, h8, mul_zero, add_zero]
  · refine crt_ge I hqa hqb hGa hGb
      (add_mem (add_mem (hG_int I hza hzb) (hG_int I hzb hza)) two_mem) ?_
    rw [hG_comb]
    linear_combination (-((qa : I.E) + qb + 1)) * hsum
  · intro i
    constructor
    · refine crt_ge I hqa hqb (hTa i).1 (hTb i).1
        (mul_mem (theta_mem I θ) (add_mem (hG_int I hza (hbbL i).1) (hG_int I hzb (hbaL i).1))) ?_
      beta_reduce
      rw [hG_comb]
      ring
    · refine crt_ge I hqa hqb (hTa i).2 (hTb i).2
        (mul_mem (star_coe_mem_range_algebraMap I θ)
          (add_mem (hG_int I hza (hbbL i).2) (hG_int I hzb (hbaL i).2))) ?_
      beta_reduce
      rw [hG_comb]
      ring
  · intro i j
    refine crt_ge I hqa hqb (hTTa i j) (hTTb i j)
      (mul_mem (theta_mem I θ) (sub_mem (add_mem (hG_int I (hbaL i).2 (hbbL j).1)
        (hG_int I (hbbL i).2 (hbaL j).1)) (mul_mem two_mem (ite_mem I (p := i = j))))) ?_
    beta_reduce
    rw [hG_comb]
    linear_combination ((θ : I.E) * (if i = j then (1 : I.E) else 0) * ((qa : I.E) + qb + 1)) * hsum
  · intro y hy
    have h1 := side_mem I e f θ (g₁ * g₂) g₁ qa qb B (A * B) (qa • za + qb • zb) za zb
      (fun i => qa • ba i + qb • bb i) ba bb (fun i => qa • bda i + qb • bdb i) bda bdb hza hzb
      (fun i => ⟨(hbaL i).1, (hbbL i).1, (hbaL i).2, (hbbL i).2⟩) hsum hprod hga rfl
      (fun i => rfl) (fun i => rfl) (hspa y hy)
    have h2 := side_mem I e f θ (g₁ * g₂) g₂ qb qa A (A * B) (qa • za + qb • zb) zb za
      (fun i => qa • ba i + qb • bb i) bb ba (fun i => qa • bda i + qb • bdb i) bdb bda hzb hza
      (fun i => ⟨(hbbL i).1, (hbaL i).1, (hbbL i).2, (hbaL i).2⟩) hsum' hprod' hgb (add_comm _ _)
      (fun i => add_comm _ _) (fun i => add_comm _ _) (hspb y hy)
    have hy' : y = qa • y + qb • y := by rw [← add_smul, hsumZ, one_smul]
    rw [hy']
    exact add_mem h1 h2

theorem hyp_dvd {I : Formalism.MainNotions.S.AutInst} {g g' r k : ℕ} {θ : 𝓞 I.E} {e f : Fin r → Fin I.n → I.E} {M : ℕ}
    (h : Hyp I g r k θ e f M) (hd : g' ∣ g) (h1 : 1 ≤ g') : Hyp I g' r k θ e f M := by
  obtain ⟨c, rfl⟩ := hd
  have hc : ∀ u : 𝓞 I.E, (u : I.E) = algebraMap (𝓞 I.E) I.E u := fun u => rfl
  have hGE : ∀ x, GE I (g' * c) x → GE I g' x := by
    rintro x ⟨t, rfl⟩
    refine ⟨(c : 𝓞 I.E) * t, ?_⟩
    simp only [hc, map_mul, map_natCast]
    push_cast
    ring
  obtain ⟨_, hS, hT, hn, he, hf, hef, hM, hL⟩ := h
  refine ⟨h1, ?_, ⟨hGE _ hT.1, hGE _ hT.2.1, hGE _ hT.2.2⟩, hn, he, hf, hef,
    Nat.Coprime.coprime_dvd_right (Dvd.intro c rfl) hM, hL⟩
  intro v hv
  apply hS v
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

theorem concl_one (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ) :
    Concl I 1 r k θ e f M := by
  have hz0 : ∀ x : Fin I.n → I.E, hG I x 0 = 0 := hG_zero_right I
  refine ⟨0, fun _ => 0, fun _ => 0, I.L.zero_mem, fun _ => ⟨I.L.zero_mem, I.L.zero_mem⟩,
    fun a => ⟨hz0 _, hz0 _⟩, fun a i => ⟨hz0 _, hz0 _, hz0 _, hz0 _⟩, ?_, ?_, ?_, ?_⟩
  · rw [hz0, zero_add]; exact ge_one I (one_mem _)
  · intro i
    simp only [hz0, mul_zero]
    exact ⟨ge_one I (zero_mem _), ge_one I (zero_mem _)⟩
  · intro i j
    exact ge_one I (mul_mem (theta_mem I θ) (sub_mem (by rw [hz0]; exact zero_mem _) (ite_mem I (p := i = j))))
  · intro y hy
    apply Submodule.mem_sup_right
    have := gL_mem I 1 hy
    rwa [Nat.cast_one, one_smul] at this

theorem globW_of (h1 : GWpp) (h2 : GWcrt) : GlobW := by
  have key : ∀ (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ)
      (g : ℕ), Hyp I g r k θ e f M → Concl I g r k θ e f M := by
    intro I r k θ e f M g
    induction g using Nat.recOnPosPrimePosCoprime with
    | prime_pow p n hp hn => exact h1 I p n r k θ e f M hp hn
    | zero => intro h; exact absurd h.1 (by norm_num)
    | one => intro _; exact concl_one I r k θ e f M
    | coprime a b ha hb hab iha ihb =>
      intro h
      exact h2 I a b r k θ e f M hab h (iha (hyp_dvd h (Dvd.intro b rfl) (by omega)))
        (ihb (hyp_dvd h (Dvd.intro_left a rfl) (by omega)))
  intro I g r k θ e f M hg hS hT hn he hf hef hM hL
  exact key I r k θ e f M g ⟨hg, hS, hT, hn, he, hf, hef, hM, hL⟩

end PI.ScRefExists.GWG

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.LocGlob
noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors

namespace PI.ScRefExists.LG

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem int_mem_intAd (r : 𝓞 F) : algebraMap F (Af F) (algebraMap (𝓞 F) F r) ∈ Formalism.UG.intAd F := by
  intro v
  show ((algebraMap (𝓞 F) F r : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

theorem int_of_mem_intAd (x : F) (h : algebraMap F (Af F) x ∈ Formalism.UG.intAd F) :
    x ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
  have hv : ((x : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := h v
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv

def lam (a : E) : E →ₗ[F] F := (Algebra.trace F E) ∘ₗ (LinearMap.mulLeft F a)

def Phi (a : E) : E ⊗[F] Af F →ₗ[F] Af F :=
  (TensorProduct.lid F (Af F)).toLinearMap ∘ₗ TensorProduct.map (lam a) LinearMap.id

omit [NumberField E] in
theorem Phi_tmul (a x : E) (c : Af F) :
    Phi a (x ⊗ₜ[F] c) = algebraMap F (Af F) (Algebra.trace F E (a * x)) * c := by
  simp [Phi, lam, Algebra.smul_def]

def Gens : Submonoid (E ⊗[F] Af F) where
  carrier := {x | ∃ o : 𝓞 E, ∃ c ∈ Formalism.UG.intAd F, x = (algebraMap (𝓞 E) E o) ⊗ₜ[F] c}
  one_mem' := ⟨1, 1, one_mem _, by simp [Algebra.TensorProduct.one_def]⟩
  mul_mem' := by
    rintro _ _ ⟨o, c, hc, rfl⟩ ⟨o', c', hc', rfl⟩
    exact ⟨o * o', c * c', mul_mem hc hc', by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩

theorem Phi_mem (a : E) (ha : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
    (algebraMap (𝓞 F) F).range) {y : E ⊗[F] Af F} (hy : y ∈ IntAf F E) :
    Phi a y ∈ Formalism.UG.intAd F := by
  have hy' : y ∈ AddSubgroup.closure ((Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
        Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) : Set _)) :=
    Subring.mem_closure_iff.mp hy
  have hle : Submonoid.closure
      (Set.range (fun x : Formalism.UG.intOE E => (x : E) ⊗ₜ[F] (1 : Af F)) ∪
        Set.range (fun y : Formalism.UG.intAd F => (1 : E) ⊗ₜ[F] (y : Af F))) ≤ (Gens : Submonoid _) := by
    rw [Submonoid.closure_le]
    rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · exact ⟨o, 1, one_mem _, rfl⟩
    · exact ⟨1, c, hc, by simp⟩
  have hy2 := AddSubgroup.closure_mono hle hy'
  clear hy hy' hle
  induction hy2 using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨o, c, hc, rfl⟩ := hx
    rw [Phi_tmul]
    obtain ⟨r, hr⟩ := ha o
    rw [← hr]
    exact mul_mem (int_mem_intAd r) hc
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem locGlob_gen (t : E) (ht : Formalism.UG.inclE (F := F) (Af F) t ∈ IntAf F E) :
    ∃ s : 𝓞 E, algebraMap (𝓞 E) E s = t := by
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hd : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero (𝓞 F) F h1
  have hmem : t ∈ FractionalIdeal.dual (𝓞 F) F
      (FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E)) := by
    rw [FractionalIdeal.mem_dual hd]
    intro a ha
    rw [FractionalIdeal.mem_dual h1] at ha
    have ha' : ∀ o : 𝓞 E, Algebra.trace F E (a * algebraMap (𝓞 E) E o) ∈
        (algebraMap (𝓞 F) F).range := by
      intro o
      have := ha (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).mpr ⟨o, rfl⟩)
      simpa [Algebra.traceForm_apply] using this
    have hP := Phi_mem a ha' ht
    have hx : Phi a (Formalism.UG.inclE (F := F) (Af F) t) =
        algebraMap F (Af F) (Algebra.trace F E (a * t)) := by
      simp [Formalism.UG.inclE, Phi_tmul]
    rw [hx] at hP
    have := int_of_mem_intAd _ hP
    simpa [Algebra.traceForm_apply, mul_comm] using this
  rw [FractionalIdeal.dual_dual] at hmem
  exact (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp hmem

end Gen

theorem local_global_principle_alt : PI.ScRefExists.Sk.LocGlob := by
  intro I t ht
  exact locGlob_gen t ht

end PI.ScRefExists.LG
end
end

namespace PI.ScRefExists.Top

open PI.ScRefExists.Sk

theorem target_of_wframe (h : WFrame) : PI.ScRefExists.Target :=
  target_of_steps PI.ScRefExists.GlueC.glue_holds_var PI.ScRefExists.TH.theta_series_existence
    PI.ScRefExists.Id.idemLift PI.ScRefExists.LG.local_global_principle_alt
    (PI.ScRefExists.GWG.globW_of (gwpp_of h PI.ScRefExists.PPA.local_assembly_principal)
      PI.ScRefExists.GWG.chinese_remainder_gluing)

end PI.ScRefExists.Top
end

theorem sc_reference_exists : PI.ScRefExists.Target :=
  PI.ScRefExists.Top.target_of_wframe
    (PI.ScRefExists.WF.wFrame_of PI.ScRefExists.ApP.principal_ideal_ring_at_prime PI.ScRefExists.WB.weil_basis_existence)
