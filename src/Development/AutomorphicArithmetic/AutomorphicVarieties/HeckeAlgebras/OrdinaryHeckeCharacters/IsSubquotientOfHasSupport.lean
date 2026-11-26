module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IsSubquotientOfHasSupport
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this

private theorem multiset_eq_of_sum {Γ : Type} [Monoid Γ] (s t : Multiset (Γ →* ℂ))
    (h : ∀ g, (s.map fun f => f g).sum = (t.map fun f => f g).sum) : s = t :=
  _root_.UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum s t h

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem exists_char {z : WD h} (hz : IsIrrWD z) {n : ℕ} (η : Fin n → Weil h →* ℂˣ)
    (hd : ∀ g, z.charPol g ∣ ∏ j, (X - C (η j g : ℂ))) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), z = WD.lpOfChar h ξ hξ := by
  obtain ⟨m, b, rfl, hirr⟩ := hz
  have hc : ∀ g k, b.ρ g * b.ρ k = b.ρ k * b.ρ g := fun g k => by
    have h1 : b.ρ ((k * g)⁻¹ * (g * k)) = 1 := by
      have h2 := hd ((k * g)⁻¹ * (g * k))
      have h3 : ∀ j, η j ((k * g)⁻¹ * (g * k)) = 1 := fun j => by
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (η j g), inv_mul_cancel]
      simp only [h3, Units.val_one, Finset.prod_const, WD.charPol_mk] at h2
      exact eq_one_of_charpoly_dvd _ (b.semisimple _) h2
    rw [← map_mul, ← map_mul, ← mul_inv_cancel_left (k * g) (g * k), map_mul, h1, mul_one]
  have hsub : ∀ S : Submodule ℂ (Fin m → ℂ), (∀ g v, v ∈ S → b.ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ := fun S hS => by
    rcases hirr.eq_bot_or_eq_top ⟨S, fun g v hv => hS g v hv⟩ with h | h
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h)
  haveI : Nontrivial (Fin m → ℂ) := nontrivial_of_irreducible hirr
  have hsc : ∀ g, ∃ c : ℂ, ∀ v, b.ρ g v = c • v := fun g => by
    obtain ⟨c, hcv⟩ := Module.End.exists_eigenvalue (b.ρ g)
    refine ⟨c, fun v => ?_⟩
    rcases hsub (Module.End.eigenspace (b.ρ g) c) (fun k u hu => by
      rw [Module.End.mem_eigenspace_iff] at hu ⊢
      have := LinearMap.congr_fun (hc g k) u
      simp only [Module.End.mul_apply] at this
      rw [this, hu, map_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.mp hcv)
    · exact Module.End.mem_eigenspace_iff.mp (h ▸ Submodule.mem_top)
  have hm : m = 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℂ)
    rcases hsub (Submodule.span ℂ {v}) (fun g u hu => by
      obtain ⟨c, h⟩ := hsc g
      rw [h]; exact Submodule.smul_mem _ _ hu) with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hv
    · have := finrank_span_singleton (K := ℂ) hv
      rw [h, finrank_top] at this
      simpa using this
  subst hm
  have hsc : ∀ f : Module.End ℂ (Fin 1 → ℂ), ∀ v, f v = f 1 0 • v := fun f v => by
    have hv : v = v 0 • (1 : Fin 1 → ℂ) := by
      funext i; rw [Subsingleton.elim i 0]; simp
    funext i
    rw [Subsingleton.elim i 0]
    conv_lhs => rw [hv, map_smul]
    simp [mul_comm]
  let c : Weil h →* ℂ :=
    { toFun := fun σ => b.ρ σ 1 0
      map_one' := by simp
      map_mul' := fun σ τ => by
        rw [map_mul, Module.End.mul_apply, hsc (b.ρ σ) (b.ρ τ 1)]; simp }
  have hker : ∀ σ, b.ρ σ = 1 → c.toHomUnits σ = 1 := fun σ hσ => by
    ext
    show b.ρ σ 1 0 = 1
    simp [hσ]
  have hN : b.N = 0 := by
    obtain ⟨n, hn⟩ := b.nilpotent
    have e : b.N = b.N 1 0 • (1 : Module.End ℂ (Fin 1 → ℂ)) := LinearMap.ext fun v => by
      rw [hsc b.N v]; rfl
    rw [e, _root_.smul_pow, one_pow] at hn
    have := congrFun (LinearMap.congr_fun hn 1) 0
    have h2 : b.N 1 0 ^ n = 0 := by simpa using this
    rw [e, pow_eq_zero_iff'.mp h2 |>.1, zero_smul]
  refine ⟨c.toHomUnits, b.smooth.of_le hker, ?_⟩
  refine WD.sound ⟨LinearEquiv.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · funext i
    rw [WDRep.ofChars_ρ, diagEnd_apply, LinearEquiv.refl_apply, LinearEquiv.refl_apply, hsc (b.ρ σ) v]
    rfl
  · simp [hN]

variable {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

private theorem charPol_ofChar (H : Laws a ha ε rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

private theorem hasSupport_iff (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : Laws a ha ε rc)
    (x : IrrGL (k := w.adicCompletion E)) {n : ℕ} (ω : Fin n → (w.adicCompletion E)ˣ →* ℂˣ)
    (hω : ∀ i, IsSmoothChar (ω i)) :
    HasSupport x.rep (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) ↔
      ∀ g, (rc x).charPol g = ∏ j, (X - C (ω j (a g) : ℂ)) := by
  refine ⟨fun hs g => ?_, fun hp => ?_⟩
  · rw [H.supp x _ hs g, Multiset.map_map, Finset.prod_eq_multiset_prod]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => charPol_ofChar H _ _ g)
  obtain ⟨s, hs⟩ := SupportRing.exists_hasSupport hZ x
  have hch : ∀ y ∈ s, ∃ χ hχ, IrrGL.ofChar χ hχ = y := fun y hy => by
    obtain ⟨ξ, hξ, e⟩ := exists_char ((H.cusp y).1 (hs.isCusp hy)) (fun j => (ω j).comp a) fun g => by
      refine Dvd.dvd.trans ?_ (hp g).dvd
      rw [H.supp _ s hs g]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol g) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    exact ⟨χ, hχ, (H.bij.1 (e.trans (H.one χ hχ).symm)).symm⟩
  let S := {χ : (w.adicCompletion E)ˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL (k := w.adicCompletion E) := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL (k := w.adicCompletion E)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := hch y hy
      exact ⟨⟨χ, hχ⟩, e⟩
  let c : S → (w.adicCompletion E)ˣ →* ℂ := fun χ => (Units.coeHom ℂ).comp χ.1
  have hc : Function.Injective c := fun χ ψ e =>
    Subtype.ext (MonoidHom.ext fun y => Units.ext (DFunLike.congr_fun e y))
  let t' : Multiset S := Finset.univ.val.map fun i => ⟨ω i, hω i⟩
  have htt : t = t' := by
    refine Multiset.map_injective hc (multiset_eq_of_sum _ _ fun y => ?_)
    obtain ⟨g, rfl⟩ := ha.surj y
    have h1 : (((t.map c).map fun f => f (a g)).map fun r => X - C r).prod =
        (((t'.map c).map fun f => f (a g)).map fun r => X - C r).prod := by
      have h2 := (H.supp x _ hs g).symm.trans (hp g)
      simp only [Multiset.map_map, Function.comp_def, t'] at h2 ⊢
      rw [Finset.prod_eq_multiset_prod] at h2
      refine Eq.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun χ _ => ?_)) h2
      exact (charPol_ofChar H χ.1 χ.2 g).symm
    have h3 := congrArg Polynomial.roots h1
    rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h3
    rw [h3]
  rw [htt, Multiset.map_map] at hs
  exact hs

end

private theorem isSubquotient_of_hasSupport (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (τ : IrrRep (GL (Fin n) k)) (μ : Fin n → kˣ →* ℂˣ)
    (hμ : ∀ i, IsSmoothChar (μ i)) (hs : HasSupport τ.ρ (Finset.univ.val.map fun i => IrrGL.ofChar (μ i) (hμ i))) :
    IsSubquotient τ.ρ (prinSeries μ) := by
  have hd : ∑ i, (IrrGL.ofChar (μ i) (hμ i)).1 = n := by simp [IrrGL.ofChar]
  refine IsSubquotient.trans ?_ (GlobalTheory.SphSeg.isSubquotient_prodIrr_prinSeries _ hd μ hμ fun _ => rfl)
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hZ k
  have h1 := SupportRing.pos_pc_sub hΨ hs τ.smooth τ.irr
  obtain ⟨hp, ep⟩ := SupportRing.prodIrr_cls hΨ _ hd
  refine SupportRing.isSubquotient_of_clsGL_ne hp τ.smooth τ.irr ?_
  have h2 := h1 (IrrGL.of τ.ρ τ.smooth τ.irr)
  rw [SupportRing.pc_map, ← ep] at h2
  have e1 : ∀ (A : GrothGL k) (y : IrrGL (k := k)), Ψ.symm (Ψ A - SupportRing.bas Ψ y) y = A y - 1 := by
    intro A y
    rw [SupportRing.bas, ← map_sub, Ψ.symm_apply_apply, Finsupp.sub_apply, Finsupp.single_eq_same]
  rw [e1] at h2
  intro h3
  rw [h3] at h2
  exact absurd h2 (by norm_num)

theorem UpperTheory.V.Hi.psRec :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ rc, IsRec h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (IsSubquotient σ.ρ (PS ω) ↔ ∀ s, (rc (algNorm σ)).charPol s = ∏ j, (X - C (ω j (a s) : ℂ))) := by
  intro P L Ω _ _ _ _ _ n w A h a ha rc hrc σ ω hω
  obtain ⟨a', ha', ε, -, H⟩ := hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := P.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective P.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion L) (((n : ℂ) - 1) / 2)) :=
    fun i => (hω i).mul (isSmoothChar_absPow _)
  have e0 : ((n : ℂ) - 1) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = 0 := by push_cast; ring
  have e1 : ∀ i, (IrrGL.ofChar (ω i) (hω i)).nu (((n : ℂ) - 1) / 2) = IrrGL.ofChar _ (hμ i) := fun i =>
    IrrGL.tw_ofChar _ _ _ _
  rw [← hasSupport_iff P.loc.zel H (algNorm σ) ω hω]
  let τ : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, σ.ρ, σ.smooth, σ.irred⟩
  constructor
  · intro hs
    have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hμ τ hs).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
    have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
    simp only [Multiset.map_map, Function.comp_def, ← e1, IrrGL.nu_nu, e0, IrrGL.nu_zero] at h2
    exact h2
  · intro hs
    have h2 := SupportRing.hasSupport_nu hs (((n : ℂ) - 1) / 2)
    have e2 : (algNorm σ).nu (((n : ℂ) - 1) / 2) = IrrGL.of σ.ρ σ.smooth σ.irred := by
      rw [algNorm, IrrGL.nu_nu, add_comm, e0, IrrGL.nu_zero]
    have key : ∀ (x y : IrrGL (k := w.adicCompletion L)) s, x = y → HasSupport x.rep s → HasSupport y.rep s := by
      rintro _ _ _ rfl h; exact h
    have h3 := (key _ _ _ e2 h2).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
    simp only [Multiset.map_map, Function.comp_def, e1] at h3
    exact isSubquotient_of_hasSupport P.loc.zel τ _ hμ h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.EqOfTwist
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Hi.PsIrr

open GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem eq_of_twist {χ ψ η : kˣ →* ℂˣ}
    (φ : (detRep (Fin 1) χ).Equiv (twist (detRep (Fin 1) ψ) (detChar (Fin 1) η))) : χ = ψ * η := by
  refine MonoidHom.ext fun x => Units.ext ?_
  let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar _ x
  have hg : Matrix.GeneralLinearGroup.det g = x := by
    ext; simp [g, Matrix.GeneralLinearGroup.scalar]
  obtain ⟨y, hy⟩ := φ.surjective 1
  have h1 := LinearMap.congr_fun (φ.isIntertwining' g) y
  have hy' : φ.toLinearMap y = 1 := hy
  have h2 : detRep (Fin 1) χ g y = (χ x : ℂ) • y := by simp [detRep, hg]
  simp only [LinearMap.comp_apply, h2, map_smul, hy'] at h1
  simpa [twist, detRep, ofChar, hg, mul_comm] using h1

private theorem irr_zero (ψ : Fin 0 → kˣ →* ℂˣ) : (prinSeries ψ).IsIrreducible := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp (points (Fin 0)) ((ofChar (torusChar ψ)).comp (leviTorus k (Fin 0)).symm.toMonoidHom) :=
    { toFun := fun c => ⟨⟨fun _ => c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
  have E : (detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prinSeries ψ) :=
    Representation.Equiv.mk' ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ (fun F => F.1.1 1)
      (fun c => rfl) (fun F => Subtype.ext (Subtype.ext (funext fun g => by rw [hg g])))
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E (isIrreducible_ofChar _)

set_option synthInstance.maxHeartbeats 400000 in
private theorem irr_prin (H : GlobalTheory.Published.TotallyDisjointProductIrreducible) (n : ℕ) :
    ∀ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) →
      (∀ i j, i ≠ j → ψ i ≠ ψ j ∧ ψ i ≠ ψ j * absPow k 1) → (prinSeries ψ).IsIrreducible := by
  induction n with
  | zero => exact fun ψ _ _ => irr_zero ψ
  | succ n ih =>
    intro ψ hψ hne
    let ψ₁ : Fin n → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd 1 i)
    let ψ₂ : Fin 1 → kˣ →* ℂˣ := fun _ => ψ (Fin.natAdd n 0)
    have happ : Fin.append ψ₁ ψ₂ = ψ := by
      have : ψ₂ = fun i => ψ (Fin.natAdd n i) := funext fun i => by rw [Subsingleton.elim i 0]
      rw [this]
      exact Fin.append_castAdd_natAdd
    have h₁ : (prinSeries ψ₁).IsIrreducible :=
      ih ψ₁ (fun i => hψ _) fun i j hij => hne _ _ fun h => hij (Fin.castAdd_injective _ _ h)
    have h₂ : (prinSeries ψ₂).IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (GlobalTheory.PrinSat.oneEquiv _ (hψ _)) (isIrreducible_ofChar _)
    let σ₁ : Irr k n := ⟨_, prinSeries ψ₁, isSmooth_parInd _ _, h₁⟩
    let σ₂ : Irr k 1 := ⟨_, prinSeries ψ₂, isSmooth_parInd _ _, h₂⟩
    have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
      refine H k n 1 n 1 σ₁ σ₂ _ _ _ _
        (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₁ (ψ := ψ₁) (fun i => hψ _) (.refl _))
        (GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries σ₂ (ψ := ψ₂) (fun i => hψ _) (.refl _)) ?_
      rintro a b h j hj ⟨φ⟩
      have e : ψ (Fin.castAdd 1 a) = ψ (Fin.natAdd n 0) * absPow k (j : ℂ) := eq_of_twist φ
      have hab : Fin.castAdd 1 a ≠ Fin.natAdd n 0 := fun h => by
        have := congrArg Fin.val h
        have := a.2
        simp at *
        omega
      obtain rfl | rfl | rfl : j = -1 ∨ j = 0 ∨ j = 1 := by
        have := abs_le.1 hj
        omega
      · refine (hne _ _ hab.symm).2 ?_
        rw [e, mul_assoc, ← absPow_add]
        simp
      · exact (hne _ _ hab).1 (by simpa using e)
      · exact (hne _ _ hab).2 (by simpa using e)
    obtain ⟨E1⟩ := PrinProd.stage_one (k := k) ψ₁ ψ₂
    obtain ⟨E2⟩ := PrinProd.stage_two (k := k) ψ₁ ψ₂
    rw [← happ]
    exact GlobalTheory.Parabolic.isIrreducible_of_equiv (E1.trans E2) hirr

end UpperTheory.V.Hi.PsIrr

theorem UpperTheory.V.Hi.psIrr :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ω : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow k 1) → (PS ω).IsIrreducible ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), π.IsIrreducible → IsSubquotient π (PS ω) → Nonempty (π.Equiv (PS ω)) := by
  intro H k _ _ _ _ n ω hω hne
  have hi : (PS ω).IsIrreducible := by
    refine PsIrr.irr_prin H.loc.disj n _
      (fun i => (hω i).mul (isSmoothChar_of_isUnram (isUnram_absPow k _))) fun i j hij => ⟨fun h => ?_, fun h => ?_⟩
    · exact (hne i j hij).1 (mul_right_cancel h)
    · rw [mul_right_comm] at h
      exact (hne i j hij).2 (mul_right_cancel h)
  exact ⟨hi, fun V _ _ π hπ hs => (hs.nonempty_equiv hπ hi).map fun e => e.symm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SphComm
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcGelfand
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem dcG_mem {H : Type} [Group H] (K : Subgroup H) (x p : H) :
    (p : H ⧸ K) ∈ MulAction.orbit K (x : H ⧸ K) ↔ ∃ k ∈ K, ∃ k' ∈ K, p = k * x * k' := by
  constructor
  · rintro ⟨k, hk⟩
    have h : (((k : H) * x : H) : H ⧸ K) = (p : H ⧸ K) := hk
    exact ⟨k, k.2, _, QuotientGroup.eq.mp h, by group⟩
  · rintro ⟨k, hk, k', hk', rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    change ((k * x : H) : H ⧸ K) = _
    exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hk')

private theorem dcG_sum {α β γ M : Type} [AddCommMonoid M] [DecidableEq γ] (s : Finset α) (t : Finset β)
    (F : α → γ) (G : β → γ) (g : γ → M)
    (h : ∀ r, (s.filter fun a => F a = r).card = (t.filter fun b => G b = r).card) :
    ∑ a ∈ s, g (F a) = ∑ b ∈ t, g (G b) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image F ∪ t.image G) (g := F)
      (fun a ha => Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)),
    ← Finset.sum_fiberwise_of_maps_to (s := t) (t := s.image F ∪ t.image G) (g := G)
      (fun a ha => Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g r) (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
    Finset.sum_congr rfl (s₁ := t.filter fun b => G b = r) (g := fun _ => g r)
      (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
    Finset.sum_const, Finset.sum_const, h]

open Classical in
private theorem dcG_le {H : Type} [Group H] (K : Subgroup H) (s : H → H)
    (hmul : ∀ x y, s (x * y) = s y * s x) (hss : ∀ x, s (s x) = x) (hK : ∀ k ∈ K, s k ∈ K)
    (hd : ∀ x, ∃ k ∈ K, ∃ k' ∈ K, s x = k * x * k')
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x y : H) (r : H ⧸ K) :
    (((hfin x).toFinset ×ˢ (hfin y).toFinset).filter fun a => a.1.out • a.2 = r).card ≤
      (((hfin y).toFinset ×ˢ (hfin x).toFinset).filter fun a => a.1.out • a.2 = r).card := by
  have h1 : s 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact left_eq_mul.mp this
  have hinv : ∀ a, s a⁻¹ = (s a)⁻¹ := fun a => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hmul, mul_inv_cancel, h1]
  have hD : ∀ x p : H, (∃ k ∈ K, ∃ k' ∈ K, p = k * x * k') → ∀ a ∈ K, ∀ b ∈ K,
      ∃ k ∈ K, ∃ k' ∈ K, a * s p * b = k * x * k' := by
    rintro x p ⟨k, hk, k', hk', hp⟩ a ha b hb
    obtain ⟨l, hl, l', hl', h⟩ := hd p
    exact ⟨a * l * k, mul_mem (mul_mem ha hl) hk, k' * l' * b, mul_mem (mul_mem hk' hl') hb, by
      rw [h, hp]; group⟩
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective r
  obtain ⟨k, hk, k', hk', hz⟩ := hd z
  let φ : H ⧸ K → H ⧸ K := fun p => ((k⁻¹ * s (p.out⁻¹ * z) * 1 : H) : H ⧸ K)
  refine Finset.card_le_card_of_injOn (fun a => (φ a.1, (φ a.1).out⁻¹ • (z : H ⧸ K))) ?_ ?_
  · rintro ⟨p, q⟩ ha
    simp only [Finset.coe_filter, Finset.mem_product, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at ha ⊢
    obtain ⟨⟨hp, hq⟩, hpq⟩ := ha
    have hq' : q = ((p.out⁻¹ * z : H) : H ⧸ K) := by
      change q = p.out⁻¹ • (z : H ⧸ K)
      rw [← hpq, inv_smul_smul]
    refine ⟨⟨?_, ?_⟩, smul_inv_smul _ _⟩
    · rw [hq', dcG_mem] at hq
      exact (dcG_mem K _ _).mpr (hD _ _ hq _ (inv_mem hk) _ (one_mem _))
    · rw [← QuotientGroup.out_eq' p, dcG_mem] at hp
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (k⁻¹ * s (p.out⁻¹ * z) * 1)
      change (((φ p).out⁻¹ * z : H) : H ⧸ K) ∈ _
      have : (φ p).out⁻¹ * z = (m : H)⁻¹ * s p.out * k'⁻¹ := by
        simp only [φ]
        rw [hm, hmul, hinv, hz]
        group
      rw [this]
      exact (dcG_mem K _ _).mpr (hD _ _ hp _ (inv_mem m.2) _ (inv_mem hk'))
  · rintro ⟨p, q⟩ ha ⟨p', q'⟩ ha' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha ha'
    have h2 : φ p = φ p' := congrArg Prod.fst h
    have h3 := hK _ (QuotientGroup.eq.mp h2)
    have h4 : (k⁻¹ * s (p.out⁻¹ * z) * 1)⁻¹ * (k⁻¹ * s (p'.out⁻¹ * z) * 1) = s (p'.out⁻¹ * p.out) := by
      rw [hmul, hmul, hmul, hinv, hinv]
      group
    rw [h4, hss] at h3
    have h5 : p' = p := by
      rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' p']
      exact QuotientGroup.eq.mpr h3
    subst h5
    have h6 : q = q' := smul_left_cancel p'.out (ha.2.trans ha'.2.symm)
    rw [h6]

private theorem dcG_two {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H)
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x y : H) (v : M) (hv : v ∈ fixd ρ K) :
    dc ρ K K x (dc ρ K K y v) =
      ∑ a ∈ (hfin x).toFinset ×ˢ (hfin y).toFinset, ρ (a.1.out • a.2 : H ⧸ K).out v := by
  have h : ∀ (x : H) (w : M), dc ρ K K x w = ∑ p ∈ (hfin x).toFinset, ρ p.out w := by
    intro x w
    rw [dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ (hfin x),
      LinearMap.sum_apply]
  rw [h, h, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K (p.out * q.out)
  have h2 : (p.out • q : H ⧸ K) = ((p.out * q.out : H) : H ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [h2, hm, map_mul, map_mul]
  simp only [Module.End.mul_apply]
  rw [hv m m.2]

theorem UpperTheory.V.Hi.dcGelfand :
    ∀ (A H M : Type) [CommRing A] [Group H] [AddCommGroup M] [Module A M] (ρ : Representation A H M) (K : Subgroup H) (s : H → H), (∀ x y, s (x * y) = s y * s x) → (∀ x, s (s x) = x) → (∀ k ∈ K, s k ∈ K) → (∀ x, ∃ k ∈ K, ∃ k' ∈ K, s x = k * x * k') → (∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) → (∀ x : H, (MulAction.orbit K (x : H ⧸ K)).ncard = (MulAction.orbit K ((x⁻¹ : H) : H ⧸ K)).ncard) → ∀ x y, ∀ v ∈ fixd ρ K, dc ρ K K x (dc ρ K K y v) = dc ρ K K y (dc ρ K K x v) := by
  intro A H M _ _ _ _ ρ K s hmul hss hK hd hfin _ x y v hv
  classical
  rw [dcG_two ρ K hfin x y v hv, dcG_two ρ K hfin y x v hv]
  refine dcG_sum _ _ (fun a : (H ⧸ K) × (H ⧸ K) => a.1.out • a.2) (fun a : (H ⧸ K) × (H ⧸ K) => a.1.out • a.2)
    (fun r => ρ r.out v) fun r => ?_
  apply le_antisymm
  · convert dcG_le K s hmul hss hK hd hfin x y r
  · convert dcG_le K s hmul hss hK hd hfin y x r
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem sphC_fin {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} (hL : IsCompact (K : Set G)) (hK' : IsOpen (K : Set G)) (x : G) :
    (MulAction.orbit K (x : G ⧸ K)).Finite := by
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK'
  have hc : Continuous fun g : G => ((g * x : G) : G ⧸ K) :=
    QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const)
  refine ((hL.image hc).finite_of_discrete).subset ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨g, g.2, rfl⟩

private theorem sphC_le {H : Type} [Group H] (K : Subgroup H) (θ : H →* H) (hθ : ∀ x, θ (θ x) = x)
    (hK : ∀ k ∈ K, θ k ∈ K) (hd : ∀ x, ∃ k ∈ K, ∃ k' ∈ K, θ x⁻¹ = k * x * k')
    (hfin : ∀ x : H, (MulAction.orbit K (x : H ⧸ K)).Finite) (x : H) :
    (MulAction.orbit K (x : H ⧸ K)).ncard ≤ (MulAction.orbit K ((x⁻¹ : H) : H ⧸ K)).ncard := by
  refine Set.ncard_le_ncard_of_injOn (fun q => ((θ q.out : H) : H ⧸ K)) ?_ ?_ (hfin _)
  · rintro q ⟨a, ha⟩
    have h : (((a : H) * x : H) : H ⧸ K) = (q.out : H ⧸ K) := by
      rw [QuotientGroup.out_eq']; exact ha
    have h1 := hK _ (QuotientGroup.eq.mp h)
    obtain ⟨l, hl, l', hl', h2⟩ := hd x⁻¹
    rw [inv_inv] at h2
    refine ⟨⟨θ a * l, mul_mem (hK _ a.2) hl⟩, ?_⟩
    change ((θ a * l * x⁻¹ : H) : H ⧸ K) = _
    refine QuotientGroup.eq.mpr ?_
    have h3 : (θ a * l * x⁻¹)⁻¹ * θ q.out = l' * θ (((a : H) * x)⁻¹ * q.out) := by
      rw [map_mul, map_inv, map_mul, h2]; group
    rw [h3]
    exact mul_mem hl' h1
  · intro p _ q _ h
    have h1 := hK _ (QuotientGroup.eq.mp h)
    rw [← map_inv, ← map_mul, hθ] at h1
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.mpr h1

private theorem sphC_central {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H) (z : H) (hz : ∀ g, g * z = z * g) (v : M) (hv : v ∈ fixd ρ K) :
    dc ρ K K z v = ρ z v := by
  have ho : MulAction.orbit K (z : H ⧸ K) = {(z : H ⧸ K)} := by
    ext q
    constructor
    · rintro ⟨a, rfl⟩
      change (((a : H) * z : H) : H ⧸ K) = _
      rw [hz]
      exact QuotientGroup.eq.mpr (by simp)
    · rintro rfl
      exact MulAction.mem_orbit_self _
  rw [dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), ho, finsum_mem_singleton]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul K z
  rw [hm, map_mul, Module.End.mul_apply, hv m m.2]

private theorem sphC_invT {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (g : GL (Fin n) k) (hg : g ∈ KO k (Fin n)) : GlobalTheory.CuspRep.invT n k g ∈ KO k (Fin n) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  exact ⟨fun i j => hg.2 j i, fun i j => hg.1 j i⟩

private theorem sphC_cartan {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (g : GL (Fin n) k) :
    ∃ a ∈ KO k (Fin n), ∃ b ∈ KO k (Fin n), GlobalTheory.CuspRep.invT n k g⁻¹ = a * g * b := by
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors 𝒪[k])
    (fun p : Fin n × Fin n => g.val p.1 p.2)
  choose f hf using hc
  obtain ⟨U, V, d, hU, hV, hΦ, -⟩ := KStar.Selmer.exists_smith n (Matrix.of fun i j => f (i, j))
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det U).2 hU
  obtain ⟨w, rfl⟩ := (Matrix.isUnit_iff_isUnit_det V).2 hV
  set u' : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u with hu'
  set w' : GL (Fin n) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w with hw'
  have hu : u' ∈ KO k (Fin n) := ⟨u, rfl⟩
  have hw : w' ∈ KO k (Fin n) := ⟨w, rfl⟩
  have hc0 : algebraMap 𝒪[k] k c ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero c.2 (Subtype.ext h)
  have h1 : algebraMap 𝒪[k] k c • g.val =
      u'.val * Matrix.diagonal (fun i => algebraMap 𝒪[k] k (d i)) * w'.val := by
    have h2 := congrArg (algebraMap 𝒪[k] k).mapMatrix hΦ
    rw [map_mul, map_mul, RingHom.mapMatrix_apply (M := Matrix.diagonal d), Matrix.diagonal_map (map_zero _)] at h2
    refine Eq.trans ?_ h2
    ext i j
    exact (hf (i, j)).symm
  have h3 : algebraMap 𝒪[k] k c • (u'⁻¹ * g * w'⁻¹).val = Matrix.diagonal (fun i => algebraMap 𝒪[k] k (d i)) := by
    rw [Units.val_mul, Units.val_mul, ← smul_mul_assoc, ← mul_smul_comm, h1]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
    rw [mul_assoc, Units.mul_inv, mul_one]
  have h4 : GlobalTheory.CuspRep.invT n k (u'⁻¹ * g * w'⁻¹)⁻¹ = u'⁻¹ * g * w'⁻¹ := by
    apply Units.ext
    change (u'⁻¹ * g * w'⁻¹).val.transpose = _
    apply smul_right_injective _ hc0
    simp only
    rw [← Matrix.transpose_smul, h3, Matrix.diagonal_transpose]
  refine ⟨GlobalTheory.CuspRep.invT n k w'⁻¹ * u'⁻¹, mul_mem (sphC_invT _ (inv_mem hw)) (inv_mem hu),
    w'⁻¹ * GlobalTheory.CuspRep.invT n k u'⁻¹, mul_mem (inv_mem hw) (sphC_invT _ (inv_mem hu)), ?_⟩
  have h5 : g⁻¹ = w'⁻¹ * (u'⁻¹ * g * w'⁻¹)⁻¹ * u'⁻¹ := by group
  rw [h5, map_mul, map_mul, h4]
  simp only [mul_assoc]

theorem UpperTheory.V.Hi.sphComm :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), (∀ x : GL (Fin n) k, (MulAction.orbit (KO k (Fin n)) (x : GL (Fin n) k ⧸ KO k (Fin n))).Finite) ∧ (∀ x y, ∀ v ∈ fixd ρ (KO k (Fin n)), dc ρ (KO k (Fin n)) (KO k (Fin n)) x (dc ρ (KO k (Fin n)) (KO k (Fin n)) y v) = dc ρ (KO k (Fin n)) (KO k (Fin n)) y (dc ρ (KO k (Fin n)) (KO k (Fin n)) x v)) ∧ ∀ v ∈ fixd ρ (KO k (Fin n)), sphOp ρ 0 v = v ∧ sphOp ρ n v = ρ (al k n n) v := by
  intro k _ _ _ _ n A M _ _ _ ρ
  have hfin : ∀ x : GL (Fin n) k, (MulAction.orbit (KO k (Fin n)) (x : GL (Fin n) k ⧸ KO k (Fin n))).Finite :=
    sphC_fin GlobalTheory.SplitFlip.isCompact_KO GlobalTheory.SplitFlip.isOpen_KO
  have hθ : ∀ x, GlobalTheory.CuspRep.invT n k (GlobalTheory.CuspRep.invT n k x) = x := fun x => Units.ext rfl
  have hle := sphC_le (KO k (Fin n)) (GlobalTheory.CuspRep.invT n k) hθ sphC_invT sphC_cartan hfin
  refine ⟨hfin, ?_, fun v hv => ⟨?_, ?_⟩⟩
  · refine dcGelfand A _ M ρ _ (fun x => GlobalTheory.CuspRep.invT n k x⁻¹) ?_ ?_ ?_ sphC_cartan hfin ?_
    · intro x y
      rw [mul_inv_rev, map_mul]
    · intro x
      rw [← map_inv, inv_inv, hθ]
    · intro a ha
      exact sphC_invT _ (inv_mem ha)
    · intro x
      refine le_antisymm (hle x) ?_
      simpa using hle x⁻¹
  · have h1 : al k n 0 = 1 := by
      rw [al, upow, ← (diagT k (Fin n)).map_one]
      congr 1
      funext i
      simp
    rw [sphOp, h1, sphC_central ρ _ 1 (by simp) v hv, map_one, Module.End.one_apply]
  · refine sphC_central ρ _ _ (fun g => Units.ext ?_) v hv
    have h1 : (al k n n).val = Matrix.scalar (Fin n) (unif k : k) := by
      rw [al, upow, val_diagT, Matrix.scalar_apply]
      congr 1
      funext i
      simp [i.isLt]
    rw [Units.val_mul, Units.val_mul, h1]
    exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SatTUnif
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem satT_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (a : G) (hf : (MulAction.orbit K (a : G ⧸ K)).Finite) (S : Set G)
    (hS : ∀ g, g ∈ S ↔ ∃ x ∈ K, ∃ y ∈ K, g = x * a * y) (v : V) :
    dc ρ K K a v = GlobalTheory.LFun.heckeVec ρ K (Set.indicator S 1) v := by
  classical
  haveI := hf.to_subtype
  have h1 : dc ρ K K a v = ∑ᶠ q : MulAction.orbit K (a : G ⧸ K), ρ (q : G ⧸ K).out v :=
    (LinearMap.applyₗ (R := ℂ) (M₂ := V) v).toAddMonoidHom.map_finsum (Set.toFinite _)
  rw [h1, finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out v), finsum_mem_def, GlobalTheory.LFun.heckeVec]
  refine finsum_congr fun c => ?_
  have h2 : c ∈ MulAction.orbit K (a : G ⧸ K) ↔ c.out ∈ S := by
    rw [hS]
    constructor
    · rintro ⟨x, hx⟩
      have hx' : ((x.1 * a : G) : G ⧸ K) = (c.out : G ⧸ K) := hx.trans c.out_eq'.symm
      exact ⟨x, x.2, _, QuotientGroup.eq.1 hx', by group⟩
    · rintro ⟨x, hx, y, hy, e⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      change ((x * a : G) : G ⧸ K) = c
      rw [← c.out_eq', e]
      exact (QuotientGroup.mk_mul_of_mem _ hy).symm
  by_cases hc : c.out ∈ S
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (h2.2 hc)]; simp
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (mt h2.1 hc)]; simp

private theorem satT_unif (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    Formalism.UG.IsUnifV L w (unif (w.adicCompletion L) : w.adicCompletion L) := by
  haveI : (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (valuation (w.adicCompletion L))
    (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hu : valuation (w.adicCompletion L) (unif (w.adicCompletion L) : w.adicCompletion L) =
      uniformizer (w.adicCompletion L) := by
    refine Classical.epsilon_spec (p := fun x : (w.adicCompletion L)ˣ =>
      valuation (w.adicCompletion L) (x : w.adicCompletion L) = uniformizer (w.adicCompletion L)) ?_
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer (w.adicCompletion L))
    refine ⟨Units.mk0 x ?_, hx⟩
    rintro rfl
    exact (zero_lt_iff.2 (by simp) : 0 < uniformizer (w.adicCompletion L)).ne ((map_zero _).symm.trans hx)
  obtain ⟨p, hp⟩ := GlobalTheory.LFun.exists_isUnifV w
  unfold Formalism.UG.IsUnifV at hp ⊢
  have h1 : Valued.v (unif (w.adicCompletion L) : w.adicCompletion L) < (1 : WithZero (Multiplicative ℤ)) :=
    he.lt_one_iff_lt_one.1 (hu.trans_lt uniformizer_lt_one)
  have h2 : valuation (w.adicCompletion L) p < 1 := he.lt_one_iff_lt_one.2 (by rw [hp]; decide)
  have h3 := (he _ _).1 ((le_uniformizer_iff.2 h2).trans_eq hu.symm)
  rw [hp] at h3
  refine le_antisymm ?_ h3
  change _ ≤ WithZero.exp (-1 : ℤ)
  rw [← WithZero.lt_mul_exp_iff_le (by simp), ← WithZero.exp_add]
  simpa using h1

private theorem satT_num (q n j : ℕ) (hq : q ≠ 0) :
    ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j =
      (q : ℂ) ^ (j * (j - 1) / 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have h2 : ((j * (j - 1) / 2 : ℕ) : ℂ) = (j : ℂ) * ((j : ℂ) - 1) / 2 := by
    rw [← Nat.choose_two_right, Nat.cast_choose_two]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q), ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, h2]
  push_cast
  rw [← Complex.cpow_add _ _ hq']
  congr 1
  ring

private theorem satT_pol (q n : ℕ) (hq : q ≠ 0) (B : Multiset ℂˣ) (hB : B.card = n) (a : ℕ → ℂ)
    (ha : ∀ j ≤ n, a j = GlobalTheory.LFun.satEig q n B j) :
    ((UpperTheory.V.Af.algSat n q B).map fun b => X - C b).prod = heckePol n q a := by
  have hc : (UpperTheory.V.Af.algSat n q B).card = n := by simp [UpperTheory.V.Af.algSat, hB]
  rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc, UpperTheory.V.Hi.heckePol]
  refine Finset.sum_congr rfl fun j hj => ?_
  have e : (UpperTheory.V.Af.algSat n q B).esymm j =
      ((((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ)) ^ j * (B.map fun b : ℂˣ => (b : ℂ)).esymm j := by
    rw [← smul_eq_mul, Multiset.pow_smul_esymm, UpperTheory.V.Af.algSat]
    congr 2
    simp
  rw [ha j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)), e, satT_num q n j hq, GlobalTheory.LFun.satEig]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

theorem UpperTheory.V.Hi.satT :
    ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (w.adicCompletion L))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → GlobalTheory.LFun.KGL w (n := n) = KO (w.adicCompletion L) (Fin n) ∧ ∃ a : ℕ → ℂ, a 0 = 1 ∧ (∀ j, ∀ v ∈ fixd σ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp σ.ρ j v = a j • v) ∧ ((UpperTheory.V.Af.algSat n (normV w) B).map fun b => X - C b).prod = heckePol n (normV w) a := by
  intro L _ _ n w σ B hB
  have hK : KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := GlobalTheory.SmGL.SphCompletion.KO_completion w n
  have hq : Formalism.UG.qV L w = normV w := by
    simp [normV, Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨hK.symm, fun j => GlobalTheory.LFun.satEig (normV w) n B (min j n), by simp [GlobalTheory.LFun.satEig, Multiset.esymm], ?_,
    satT_pol (normV w) n (hq ▸ GlobalTheory.LFun.qV_ne_zero w) B hB.card
      (fun j => GlobalTheory.LFun.satEig (normV w) n B (min j n)) (fun j hj => by rw [min_eq_left hj])⟩
  intro j v hv
  by_cases h0 : v = 0
  · simp [h0]
  rw [hK] at hv
  have h1 := (hB.2 v (GlobalTheory.LGrp.mem_fixed.2 hv) h0).2.2.2 _ (satT_unif L w) (min j n) (min_le_right _ _)
  rw [hq] at h1
  refine Eq.trans ?_ h1
  rw [sphOp, hK]
  refine satT_dc σ.ρ _ _ (Formalism.UG.P.orbit_coset_finite _ (Formalism.UG.Final.GLintComm L w n) _) _ (fun g => ?_) v
  have hal : (al (w.adicCompletion L) n j).val =
      Formalism.UG.diagJ n (unif (w.adicCompletion L) : w.adicCompletion L) (min j n) := by
    rw [UpperTheory.V.Hi.al, upow, val_diagT, Formalism.UG.diagJ]
    congr 1
    funext i
    have := i.2
    by_cases h : (i : ℕ) < j
    · simp [h]
    · simp [h]
  simp only [Set.mem_setOf_eq, ← hal, ← Units.val_mul, Units.val_inj]
end
