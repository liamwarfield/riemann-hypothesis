module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.ExistsOfInLat
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

section

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] {J : Type}

private theorem coe_add' (y y' : J → 𝓞 F) :
    (fun j => ((y + y') j : F)) = (fun j => (y j : F)) + fun j => (y' j : F) := by
  funext j
  simp

end

theorem UpperTheory.V.ZK.Cl.cInt :
    UpperTheory.V.ZK.Cl.CInt := by
  intro L F _ _ _ _ _ J _ b
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · haveI : Module.FinitePresentation (𝓞 L) (J → 𝓞 F) := Module.finitePresentation_of_finite _ _
    exact Module.Flat.projective_of_finitePresentation
  have hadd : ∀ u w : 𝓞 F, ((u + w : 𝓞 F) : F) = (u : F) + (w : F) := fun u w => by simp
  have hmul : ∀ u w : 𝓞 F, ((u * w : 𝓞 F) : F) = (u : F) * (w : F) := fun u w => by simp
  have hone1 : ((1 : 𝓞 F) : F) = 1 := by simp
  have hint : ∀ y : J → F, InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) y ↔ ∀ j, ∃ a : 𝓞 F, (a : F) = y j := by
    intro y
    constructor
    · intro hy j
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y j)
        (fun P => by simpa using hy j P)
      exact ⟨a, ha⟩
    · intro hy j P
      obtain ⟨a, ha⟩ := hy j
      rw [← ha]
      simpa using HeightOneSpectrum.valuation_le_one (K := F) P a
  let φ : GG L F J → (J → 𝓞 F) → (J → 𝓞 F) := fun g x j =>
    if hx : ∃ a : 𝓞 F, (a : F) = g (fun i => (x i : F)) j then hx.choose else 0
  have hφ : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x j,
      ((φ g x j : 𝓞 F) : F) = g (fun i => (x i : F)) j := by
    intro g hg x j
    have hg' : ∀ y, InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) y ↔
        InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (g y) := hg
    have h1 : InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (fun i => (x i : F)) :=
      (hint _).2 (fun i => ⟨x i, rfl⟩)
    have h2 := (hint _).1 ((hg' _).1 h1) j
    simp only [φ, dif_pos h2]
    exact h2.choose_spec
  have hφf : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x,
      (fun i => ((φ g x i : 𝓞 F) : F)) = g (fun i => (x i : F)) := fun g hg x => funext (hφ g hg x)
  have hcomp : ∀ g1 ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)),
      ∀ g2 ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x, φ g1 (φ g2 x) = φ (g1 * g2) x := by
    intro g1 hg1 g2 hg2 x
    funext j
    apply RingOfIntegers.ext
    rw [hφ g1 hg1, hφf g2 hg2, hφ _ (Subgroup.mul_mem _ hg1 hg2)]
    rfl
  have hone : ∀ x, φ 1 x = x := by
    intro x
    funext j
    apply RingOfIntegers.ext
    rw [hφ 1 (Subgroup.one_mem _)]
    rfl
  have hsmul : ∀ (a : 𝓞 L) (z : 𝓞 F), ((a • z : 𝓞 F) : F) = (a : L) • (z : F) := by
    intro a z
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  have hlin : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x y,
      φ g (x + y) = φ g x + φ g y ∧ ∀ a : 𝓞 L, φ g (a • x) = a • φ g x := by
    intro g hg x y
    constructor
    · funext j
      apply RingOfIntegers.ext
      rw [Pi.add_apply, hadd, hφ g hg, hφ g hg, hφ g hg, coe_add', map_add (f := _), Pi.add_apply]
    · intro a
      funext j
      apply RingOfIntegers.ext
      have e : (fun i => ((a • x) i : F)) = (a : L) • fun i => (x i : F) := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, hsmul]
      rw [Pi.smul_apply, hsmul, hφ g hg, hφ g hg, e, map_smul, Pi.smul_apply]
  let E : ∀ g : GG L F J, g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)) →
      ((J → 𝓞 F) ≃ₗ[𝓞 L] J → 𝓞 F) := fun g hg =>
    { toFun := φ g
      invFun := φ g⁻¹
      map_add' := fun x y => (hlin g hg x y).1
      map_smul' := fun a x => (hlin g hg x x).2 a
      left_inv := by
        intro x
        show φ g⁻¹ (φ g x) = x
        rw [hcomp _ (Subgroup.inv_mem _ hg) _ hg, inv_mul_cancel, hone]
      right_inv := by
        intro x
        show φ g (φ g⁻¹ x) = x
        rw [hcomp _ hg _ (Subgroup.inv_mem _ hg), mul_inv_cancel, hone] }
  let α : ↥((StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ))).subgroupOf (GLoc F J b)) →*
      ((J → 𝓞 F) ≃ₗ[𝓞 L] J → 𝓞 F) :=
    { toFun := fun h => E _ (Subgroup.mem_subgroupOf.1 h.2)
      map_one' := by
        apply LinearEquiv.ext
        intro x
        exact hone x
      map_mul' := by
        intro h1 h2
        apply LinearEquiv.ext
        intro x
        exact (hcomp _ (Subgroup.mem_subgroupOf.1 h1.2) _ (Subgroup.mem_subgroupOf.1 h2.2) x).symm }
  refine ⟨α, ?_⟩
  intro k _ r hr μ hμ
  have hfix : ∀ (σ : Gal(F/L)) (a : 𝓞 L), actO σ (algebraMap (𝓞 L) (𝓞 F) a) = algebraMap (𝓞 L) (𝓞 F) a := by
    intro σ a
    apply RingOfIntegers.ext
    show σ ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F) = ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F)
    have e : ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F) = algebraMap L F (a : L) := by
      have := hsmul a 1
      simpa [Algebra.smul_def] using this
    rw [e]
    exact σ.commutes _
  let π : (J → 𝓞 F) →+ (Gal(F/L) × J → k) :=
    { toFun := fun x p => r (actO p.1 (x p.2))
      map_zero' := by
        funext p
        simp
      map_add' := by
        intro x y
        funext p
        simp }
  have huniq : ∀ (y : F) (u u' : k), ResF r y u → ResF r y u' → u = u' := by
    rintro y u u' ⟨a, c, hc, hyc, hu⟩ ⟨a', c', hc', hyc', hu'⟩
    have e : a * c' = a' * c := by
      apply RingOfIntegers.ext
      rw [hmul, hmul, ← hyc, ← hyc']
      ring
    have e2 := congrArg r e
    rw [map_mul, map_mul, hu, hu'] at e2
    have hcc : r c * r c' ≠ 0 := mul_ne_zero hc hc'
    apply mul_right_cancel₀ hcc
    linear_combination e2
  have hR : ∀ z : J → 𝓞 F, RedV L r (fun i => (z i : F)) (π z) := by
    intro z σ j
    refine ⟨actO σ (z j), 1, by simp, ?_, ?_⟩
    · rw [hone1, mul_one]
      rfl
    · show r (actO σ (z j)) = r (actO σ (z j)) * r 1
      rw [map_one, mul_one]
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · intro a x
    funext p
    show r (actO p.1 ((a • x) p.2)) = (r.comp (algebraMap (𝓞 L) (𝓞 F))) a • r (actO p.1 (x p.2))
    rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hfix, smul_eq_mul]
    rfl
  · intro v
    choose a ha using fun j => hr.1 (fun σ => v (σ, j))
    exact ⟨a, funext fun p => ha p.2 p.1⟩
  · intro x hx
    have hj : ∀ j, x j ∈ Ideal.map (algebraMap (𝓞 L) (𝓞 F)) (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) :=
      fun j => hr.2 (x j) (fun σ => congrFun hx (σ, j))
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro j _
    have h1 : x j ∈ ((RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) • ⊤ : Submodule (𝓞 L) (𝓞 F)) := by
      rw [Ideal.smul_top_eq_map]
      exact hj j
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.single (𝓞 L) (fun _ : J => 𝓞 F) j) h1
    rw [Submodule.map_smul'', LinearMap.single_apply] at h2
    exact Submodule.smul_mono le_rfl le_top h2
  · intro h x
    funext p
    have hloc : InLoc b (fun i => (x i : F)) := by
      intro j P _
      exact HeightOneSpectrum.valuation_le_one (K := F) P (x j)
    have hred := hμ (h : ↥(GLoc F J b)) (fun i => (x i : F)) (π x) hloc (hR x)
    have hα := hR (α h x)
    have hc : (fun i => ((α h x i : 𝓞 F) : F)) = ((h : ↥(GLoc F J b)) : GG L F J) (fun i => (x i : F)) :=
      hφf _ (Subgroup.mem_subgroupOf.1 h.2) x
    rw [hc] at hα
    exact huniq _ _ _ (hα p.1 p.2) (hred p.1 p.2)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CJoin
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cJoin : CJoin := by
  intro hChain hFree hTriv hAct hSplit hSupp hLatLoc hMu hInt hVal hGtNe hGtEq hBetaDiv
    hBetaVal hRep hUnit
  intro sChain sPrism sPrismMul sZc sRel sEta sStein
  intro L F _ _ _ _ _ l c ν e _ ζ γ hL he α 𝔡 hD
  classical
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hζq : ζ ^ (l ^ ν) = 1 := hL.prim.pow_eq_one
  have hR := hRep L F (l ^ ν) ζ hζq
  obtain ⟨kap, hkap⟩ := hR.2.2.2.2 hL.prim
  obtain ⟨b₀, hb₀, hsplit⟩ := hSplit L F hL.gal
  obtain ⟨b, hb, hb₀b, hbP⟩ := hSupp L F 𝔡 b₀ hb₀
  obtain ⟨n, t₀, hn, hrel⟩ := sRel l ν e
  obtain ⟨η, hη_ne, hη_eq⟩ := sEta l c ν (2 * e + 3) he hL.c_le t₀
  have hβ := hBetaDiv L F γ (1 + l ^ c) (2 * e + 3) (e + 1) (by omega) α 𝔡 hD
  set β := polAct γ (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1)) α with hβdef
  have hcar : ∀ t : Fin (2 * e + 4), ∃ g : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν)),
      Carries L (l ^ ν) ζ (fun x => x.1 + ((t : ℕ) : ZMod (l ^ ν)) * x.2) (fun j => η j • 𝔡)
        (if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) g := by
    intro t
    by_cases ht : t = t₀
    · subst ht
      rw [if_pos rfl]
      refine hGtEq sStein L F (ZMod (l ^ ν) × ZMod (l ^ ν)) l c ν (2 * e + 3) ζ γ hL _ η 𝔡
        (fun i => (pol ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3)).coeff i) β ⟨(1, 0), by simp⟩ ?_ hβ
      rw [hη_eq]
      simp [pol]
    · rw [if_neg ht]
      exact hGtNe sStein L F (ZMod (l ^ ν) × ZMod (l ^ ν)) (l ^ ν) ζ _ η 𝔡 (hη_ne t ht)
  choose gG hgG using hcar
  have hmem : ∀ t, gG t ∈ GLoc F (ZMod (l ^ ν) × ZMod (l ^ ν)) b := by
    intro t
    refine hLatLoc L F (ZMod (l ^ ν) × ZMod (l ^ ν)) b hb 0 (fun j => η j • 𝔡) ?_ ?_ (gG t) (hgG t).1
    · intro j P h
      simp at h
    · intro j P h
      apply hbP P
      intro h0
      apply h
      simp [h0]
  set Gr := GLoc F (ZMod (l ^ ν) × ZMod (l ^ ν)) b with hGr
  set Hs := (StabP L (InLat (0 : ZMod (l ^ ν) × ZMod (l ^ ν) → HeightOneSpectrum (𝓞 F) →₀ ℤ))).subgroupOf Gr with hHs
  let gs : Fin (2 * e + 4) → Gr := fun t => ⟨gG t, hmem t⟩
  let ρD : Cq (l ^ ν) × Cq (l ^ ν) →* Gr := (repD L (l ^ ν) ζ hζq).codRestrict Gr (fun x => hR.2.2.1 b x)
  have memStab : ∀ (p : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      g ∈ StabP L p ↔ ∀ x, p x ↔ p (g x) := fun _ _ => Iff.rfl
  have hstab : ∀ (p p' : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g h : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      (∀ x, p x ↔ p' (g x)) → (∀ x, p' x ↔ p' (h x)) → g⁻¹ * h * g ∈ StabP L p := by
    intro p p' g h hg hh
    rw [memStab]
    intro x
    rw [hg x, hg ((g⁻¹ * h * g) x)]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact hh (g x)
  have hstab2 : ∀ (p p' : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g g' : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      (∀ x, p x ↔ p' (g x)) → (∀ x, p x ↔ p' (g' x)) → g⁻¹ * g' ∈ StabP L p := by
    intro p p' g g' hg hg'
    rw [memStab]
    intro x
    rw [hg' x, hg ((g⁻¹ * g') x)]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  have hcomm : ∀ (t : Fin (2 * e + 4)) (c' : Cq (l ^ ν)), Commute (gs t) (ρD (dt (l ^ ν) (t : ℕ) c')) := by
    intro t c'
    have hc := hR.2.2.2.1 _ _ _ _ _ (hgG t) c'
    apply Subtype.ext
    simp only [Subgroup.coe_mul, gs, ρD, MonoidHom.codRestrict_apply]
    rw [hR.1]
    exact hc.eq
  have hrhoH : ∀ x, ρD x ∈ Hs := by
    intro x
    rw [hHs, Subgroup.mem_subgroupOf]
    exact hR.2.1 0 x
  have hconj : ∀ x, (gs t₀)⁻¹ * ρD x * gs t₀ ∈ Hs := by
    intro x
    rw [hHs, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, gs, ρD, MonoidHom.codRestrict_apply]
    exact hstab _ _ _ _ (hgG t₀).1 ((memStab _ _).mp (hR.2.1 (fun j => η j • 𝔡) x))
  have hquot : ∀ t, (gs t)⁻¹ * gs t₀ ∈ Hs := by
    intro t
    rw [hHs, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, gs]
    exact hstab2 _ _ _ _ (hgG t).1 (hgG t₀).1
  obtain ⟨y, hyc, hyb⟩ := hChain (ZMod (l ^ ν)) (Cq (l ^ ν)) (Cq (l ^ ν) × Cq (l ^ ν)) Gr
    (Fin (2 * e + 4)) (2 * e + 1) Hs ρD (fun t => dt (l ^ ν) (t : ℕ)) n (zc (l ^ ν) e) gs t₀
    (sZc (l ^ ν) e) hrel hcomm hrhoH hconj hquot
  obtain ⟨hfin, hproj, αI, hαI⟩ := hInt L F (ZMod (l ^ ν) × ZMod (l ^ ν)) b
  haveI := hfin
  haveI := hproj
  obtain ⟨N, lam, hlam⟩ := hFree (𝓞 L) (ZMod (l ^ ν) × ZMod (l ^ ν) → 𝓞 F) Hs αI
  set w : ZMod (l ^ ν) := ((hn.unit⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) with hw
  set y' := w • y with hy'
  have hy'c : Cyc y' := by
    unfold Cyc at hyc ⊢
    rw [hy', map_smul, hyc, smul_zero]
  refine ⟨N, cm (ZMod (l ^ ν)) lam (2 * e + 1 + 1 + 1) y', algebraMap (𝓞 L) (𝓞 F) b, ?_, ?_, ?_⟩
  · unfold Cyc at hy'c ⊢
    rw [(sChain (ZMod (l ^ ν))).2.1]
    erw [hy'c, map_zero]
  · intro h
    apply hb
    exact FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 F) (by rw [h, map_zero])
  intro k _ _ r hr hrb hζ v θ hθ hv
  have hrb₀ : r (algebraMap (𝓞 L) (𝓞 F) b₀) ≠ 0 := by
    obtain ⟨c', hc'⟩ := hb₀b
    intro h0
    apply hrb
    rw [hc', map_mul, map_mul, h0, zero_mul]
  have hSp : Split L r := hsplit k r hr hrb₀
  obtain ⟨μ, hμ⟩ := hMu L F (ZMod (l ^ ν) × ZMod (l ^ ν)) k r b hrb hr hSp
  obtain ⟨U, f, hUdef, hUact, hfadd, hf1, hfres, hUres⟩ := hUnit L F k r b hrb (l ^ ν) v
  have hαU : α ∈ U := by
    rw [hUdef]
    intro P hP
    have h1 : 𝔡 P = 0 := by
      by_contra h0
      exact hP (hbP P h0)
    have h2 : 𝔡 (actP γ P) = 0 := by
      by_contra h0
      exact hP (((hAct L F).2.2.2.1 γ P b).mp (hbP _ h0))
    rw [hD P, h1, h2]
    simp
  have hnrmU : nrm γ ((1 + l ^ c) ^ (e + 1)) α ∈ U := by
    unfold nrm
    exact Subgroup.prod_mem U fun j _ => U.pow_mem (hUact _ _ hαU) _
  obtain ⟨u, hu⟩ := hUres _ hnrmU
  refine ⟨u, hu, ?_⟩
  rw [← hfres _ _ hu]
  obtain ⟨π, hπ1, hπ2, hπ3, hπ4⟩ := hαI k r hSp μ hμ
  obtain ⟨P, φ, hφ⟩ := hlam k (r.comp (algebraMap (𝓞 L) (𝓞 F))) hr
    (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k) π (μ.comp Hs.subtype) hπ1 hπ2 hπ3 hπ4
  beta_reduce at hyb
  rw [← (sChain (ZMod (l ^ ν))).2.2.1, hφ]
  refine Eq.trans (hTriv k (ZMod (l ^ ν)) (2 * e + 1 + 1) θ hθ Hs
    (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k) P (Fin N → k) (μ.comp Hs.subtype) φ y' hy'c) ?_
  rw [(sChain (ZMod (l ^ ν))).2.2.1]
  change θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
    (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (cm (ZMod (l ^ ν)) Hs.subtype (2 * e + 1 + 2) (w • y))) = _
  rw [map_smul, map_smul, map_smul]
  have hA : θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
      (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (cm (ZMod (l ^ ν)) Hs.subtype (2 * e + 1 + 2) y)) =
      ∑ t : Fin (2 * e + 4), n t • θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
        (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (prism (ZMod (l ^ ν)) (gs t) (2 * e + 1 + 1)
          (cm (ZMod (l ^ ν)) (ρD.comp (dt (l ^ ν) (t : ℕ))) (2 * e + 1 + 1) (zc (l ^ ν) e)))) := by
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyb
    have h0 : θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
        (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (bd _ _ _ x)) = 0 :=
      hθ.bdry _ _ (LinearMap.mem_range.mpr ⟨cm (ZMod (l ^ ν)) μ _ x, (sChain _).2.1 _ _ μ _ x⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h0
    rw [h0]
    simp only [map_smul]
  have hT : ∀ t : Fin (2 * e + 4), θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
      (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (prism (ZMod (l ^ ν)) (gs t) (2 * e + 1 + 1)
        (cm (ZMod (l ^ ν)) (ρD.comp (dt (l ^ ν) (t : ℕ))) (2 * e + 1 + 1) (zc (l ^ ν) e)))) =
      ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) := by
    intro t
    erw [(sChain (ZMod (l ^ ν))).2.2.2.1, ← (sChain (ZMod (l ^ ν))).2.2.1]
    exact hVal L F (ZMod (l ^ ν) × ZMod (l ^ ν)) (l ^ ν) e ζ hζq kap hkap k r b hrb hSp μ hμ hζ v θ hθ hv
      f hfres _ _ _ (gs t) (ρD.comp (dt (l ^ ν) (t : ℕ))) (hgG t)
      (fun c' => by simp only [ρD, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]; exact hR.1 t c')
  have hT0 : ∀ t : Fin (2 * e + 4), t ≠ t₀ →
      ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) = 0 := by
    intro t ht
    simp [if_neg ht, hf1]
  have hTt₀ : ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t₀ = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) =
      ∑ σ, (kap σ : ZMod (l ^ ν)) ^ (e + 1) * f (actU σ β) := by
    rw [if_pos rfl]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_eq_single (1 : ZMod (l ^ ν))]
    · simp
    · intro x _ hx
      simp [hx, hf1]
    · simp
  have hBV := hBetaVal L F l c ν (e + 1) ζ γ hL kap hkap U f hUact hfadd α hαU
    (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1))
  have hev : ((eval (((1 + l ^ c) ^ (e + 1) : ℕ) : ℤ) (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1)) : ℤ) :
      ZMod (l ^ ν)) = ((pe (1 + l ^ c) (2 * e + 3) (e + 1) : ℤ) : ZMod (l ^ ν)) := by
    congr 1
    simp [polE, pe, eval_prod]
  rw [hA, Finset.sum_eq_single t₀ (fun t _ ht => by rw [hT t, hT0 t ht, smul_zero]) (by simp),
    hT t₀, hTt₀, hBV, hev, smul_eq_mul, smul_eq_mul, ← mul_assoc, hw, hn.val_inv_mul, one_mul]
end
