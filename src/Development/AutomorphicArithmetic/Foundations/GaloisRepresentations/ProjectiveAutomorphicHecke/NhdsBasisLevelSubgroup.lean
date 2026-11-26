module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTracePow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.ZetaMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.InvTMemSim
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig2Of
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PClassFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PIntConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSatVal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLevCompact
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLevCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.LevCompact := by
  intro hC hI hL hO E _ _ _ n Up w₀ hw₀ S Kw hS
  obtain ⟨-, hAp, -, -, -, -⟩ := hL E n w₀ hw₀
  have hclosed : IsClosed (lev S Kw : Set (GUf E n)) :=
    Subgroup.isClosed_of_isOpen _ (hO E n S Kw hS.opn)
  have hK₁ := hC E n
  have hJ := hS.cpt w₀ hS.mem
  have hKo := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w₀ n).1
  obtain ⟨F, -, hF⟩ := hJ.elim_nhds_subcover
    (fun a => {y : GLw n w₀ | a⁻¹ * y ∈ GlobalTheory.LFun.KGL w₀ (n := n)}) (fun a _ => by
      refine IsOpen.mem_nhds (hKo.preimage (continuous_const.mul continuous_id)) ?_
      simp [Subgroup.one_mem])
  have hcov : IsCompact (⋃ a ∈ F, (fun x : GUf E n => loc hw₀ a * x) ''
      (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n))) :=
    F.isCompact_biUnion fun a _ => hK₁.image (continuous_const.mul continuous_id)
  refine hcov.of_isClosed_subset hclosed fun k hk => ?_
  obtain ⟨hsim, hmem, hoff⟩ := mem_lev.1 hk
  obtain ⟨a, haF, ha⟩ := Set.mem_iUnion₂.1 (hF (hmem w₀ hS.mem))
  have ha' : a⁻¹ * comp w₀ k ∈ GlobalTheory.LFun.KGL w₀ (n := n) := ha
  have hsim' : sim ((loc hw₀ a)⁻¹ * k) ∈ ZU := by simpa using hsim
  have hw : comp w₀ ((loc hw₀ a)⁻¹ * k) ∈ GlobalTheory.LFun.KGL w₀ (n := n) := by simpa using ha'
  have hint : ∀ u : Plc E, u ≠ w₀ → u ≠ cj w₀ → comp u k ∈ GlobalTheory.LFun.KGL u (n := n) := by
    intro u h1 h2
    have hcc : cj (cj u) = u := GlobalTheory.SplitPts.conjSrc_conjSrc_cm u
    by_cases hu : u ∈ S
    · exact hS.le u hu h1 (hmem u hu)
    by_cases hc : cj u ∈ S
    · have hne : cj u ≠ w₀ := fun h => h2 (by rw [← h, hcc])
      have := hI E n k (cj u) hsim (hS.le _ hc hne (hmem _ hc))
      rwa [hcc] at this
    · exact hoff u hu hc
  have hk' : (loc hw₀ a)⁻¹ * k ∈ lev (E := E) (n := n) ∅ (fun _ => ⊤) := by
    refine mem_lev.2 ⟨hsim', by simp, fun u _ _ => ?_⟩
    by_cases h1 : u = w₀
    · subst h1; exact hw
    by_cases h2 : u = cj w₀
    · subst h2; exact hI E n _ w₀ hsim' hw
    · have happ : GlobalTheory.Cong.Apart u w₀ := (hAp u).2 ⟨h1, h2⟩
      have : comp u ((loc hw₀ a)⁻¹ * k) = comp u k := by
        rw [map_mul, map_inv, comp_loc_of_apart hw₀ happ, inv_one, one_mul]
      rw [this]
      exact hint u h1 h2
  exact Set.mem_iUnion₂.2 ⟨a, haF, _, hk', by simp⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PXiScalar
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pXiScalar_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar := by
  intro E _ _ _ n W j y s t hy v
  have hy' : y = Formalism.L2.Col.brpSc E t := Units.ext (by rw [hy, Formalism.L2.Col.brpSc_coe])
  have hinv : y⁻¹ = Formalism.L2.Col.brpSc E t⁻¹ := by
    rw [hy']
    exact (map_inv (Units.map (algebraMap E (Matrix (Fin n) (Fin n) E) : E →* Matrix (Fin n) (Fin n) E)) t).symm
  have hemb : embAll E n y⁻¹ = fun u => Formalism.L2.Col.brpSc ℂ (Units.map (u.embedding : E →* ℂ) t⁻¹) := by
    funext u
    ext i k
    rw [hinv]
    change ((((Formalism.L2.Col.brpSc E t⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E).map u.embedding) i k = _
    rw [Formalism.L2.Col.brpSc_coe, Formalism.L2.Col.brpSc_coe]
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
  have hr := Formalism.L2.Col.tensorWeights_scalar_action (K := ℂ) W (fun u => Units.map (u.embedding : E →* ℂ) t⁻¹)
  rw [← hemb] at hr
  simp only [xi, MonoidHom.coe_mk, OneHom.coe_mk, Representation.dual_apply]
  rw [MonoidHom.comp_apply, hr]
  ext x
  simp [Module.Dual.transpose_apply, smul_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PXiZeta
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem zpow_sum_eq_prod_zpow {ι : Type*} {a : ℂ} (ha : a ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ u ∈ s, e u) = ∏ u ∈ s, a ^ e u := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem UpperTheory.Gal.CertificateRingHomMap.pXiZeta_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar → UpperTheory.Gal.CertificateRingHomMap.XiZeta := by
  intro hXi E _ _ _ n W j x ζ hζ k
  obtain ⟨γ, t, h1, h2, h3, h4⟩ := hζ.onRat k
  refine ⟨γ, h1, fun v => ?_⟩
  have hs : xi0 W j γ v = _ := hXi E n W j γ.1.1 γ.1.2 t h2 v
  rw [hs]
  congr 1
  rw [h4]
  have e : ∀ u : InfinitePlace E, u.embedding (t : E) ^ (-∑ i, (W u).w i) =
      ∏ φ : E →+* ℂ, (if φ x = -u.embedding x then φ (k : E) else 1) ^ (-∑ i, (W u).w i) := by
    intro u
    rw [h3 u.embedding, Finset.prod_filter, Finset.prod_zpow]
  rw [Finset.prod_congr rfl fun u _ => e u, Finset.prod_comm, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  have ha : φ (k : E) ≠ 0 := (map_ne_zero φ).2 k.ne_zero
  unfold mOf
  rw [zpow_sub₀ ha, div_eq_mul_inv, zpow_sum_eq_prod_zpow ha, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  by_cases h : φ x = -u.embedding x
  · have h' : u.embedding x = -φ x := by rw [h, neg_neg]
    rw [if_pos h, if_pos h', _root_.zpow_neg]
  · have h' : ¬ u.embedding x = -φ x := fun h'' => h (by rw [h'', neg_neg])
    rw [if_neg h, if_neg h']
    simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PFinToHecke
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pFinToHecke_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke := by
  intro E _ _ ψ m ho hk
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E m
  let p : Neutral.B1.Ideles E →* (Af E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) : _ →* _)
  have hpc : Continuous p := Continuous.units_map _ continuous_snd
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ ho
  have hd : ∀ k : Eˣ, p (Neutral.B1.diagUnits E k) = diagF E k := fun k => Units.ext rfl
  have hl : ∀ (w : Plc E) y, p (Neutral.B1.localIdele E w y) = sgl w y := fun w y => Units.ext rfl
  have hi : ∀ k : Eˣ, p (infDiag k) = 1 := fun k => by
    rw [infDiag_eq]
    exact Units.ext rfl
  let θ : Neutral.B1.Ideles E →* ℂˣ := ψ.comp p * f
  have hθ : ∀ x, ((θ x : ℂˣ) : ℂ) = ((ψ (p x) : ℂˣ) : ℂ) * infPow m x := fun x => by
    rw [← hfe]
    rfl
  refine ⟨⟨θ, (hψ.comp hpc).mul hf, fun k => Units.ext ?_⟩, fun k _ => ?_, fun w y => ?_⟩
  · rw [hθ, hd, hk, infPow_diagUnits, Units.val_one]
    exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ (by simp))
  · show ((θ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hθ, hi, infPow_infDiag, infPow_diagUnits, map_one, Units.val_one, one_mul]
  · show θ (Neutral.B1.localIdele E w y) = _
    refine Units.ext ?_
    rw [hθ, hl, infPow_localIdele, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PFormGU
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.LKDef.HeckeTraceForms (forms)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem rop_single {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (u : H) (Φ : H → V) (g : H) :
    rop (Finsupp.single u 1) Φ g = Φ (g * u) := by
  unfold rop
  rw [Finsupp.sum_single_index (by simp), one_smul]

private theorem rop_sum {H V Y : Type} [Group H] [AddCommGroup V] [Module ℂ V] (R : Finset Y) (e : Y → H) (Φ : H → V) (g : H) :
    rop (∑ y ∈ R, Finsupp.single (e y) 1) Φ g = ∑ y ∈ R, Φ (g * e y) := by
  unfold rop
  rw [Finsupp.sum_finsetSum _ _ _ (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun y _ => by rw [Finsupp.sum_single_index (by simp), one_smul]

private structure HI {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (U : Submodule ℂ (UA E n → ℂ)) (S : Finset (Plc E)) where
  w : Plc E
  hw : IsSplitAt w
  h1 : w ∉ S
  h2 : cj w ∉ S
  B : Multiset ℂˣ
  hB : SatU U w B
  p : w.adicCompletion E
  hp : Formalism.UG.IsUnifV E w p
  i : ℕ
  hi : i ≤ n

set_option maxHeartbeats 1600000 in
theorem pFormGU_of (hExt : ExtEig2) (hCl : ClassFin) (hXi : XiZeta) (hKer : KerFormU) (hHk : HeckePres) (hSat : SatVal)
    (hMem : LocMem) (hComm : LocComm) (hOp : LevOpen) (hU : OfUBij) : FormGU := by
  intro E _ _ _ n x ζ hζ π W j Up w₀ hw₀ S Kw hS χ hχ f hf hf0 hfix
  obtain ⟨-, hap, -, -, hcc, -⟩ := hComm E n w₀ hw₀
  have hc0 : cj w₀ ∉ S := (hS.up w₀ hS.mem hw₀).2
  let Kw' := Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)
  have mem' : ∀ k : GUf E n, k ∈ lev S Kw' ↔ k ∈ lev S Kw ∧ ∃ h : comp w₀ k ∈ Kw w₀, χ ⟨_, h⟩ = 1 := by
    intro k
    have e0 : comp w₀ k ∈ Kw' w₀ ↔ ∃ h : comp w₀ k ∈ Kw w₀, χ ⟨_, h⟩ = 1 := by
      simp only [Kw', Function.update_self, Subgroup.mem_map, MonoidHom.mem_ker]
      exact ⟨fun ⟨y, hy, e⟩ => ⟨e ▸ y.2, by rw [← hy]; congr 1; exact Subtype.ext e.symm⟩, fun ⟨h, e⟩ => ⟨⟨_, h⟩, e, rfl⟩⟩
    have e1 : ∀ w, w ≠ w₀ → Kw' w = Kw w := fun w hw => Function.update_of_ne hw _ _
    rw [mem_lev, mem_lev]
    constructor
    · rintro ⟨a, b, c⟩
      obtain ⟨h, hh⟩ := e0.1 (b _ hS.mem)
      refine ⟨⟨a, fun w hw => ?_, c⟩, h, hh⟩
      by_cases e : w = w₀
      · subst e; exact h
      · rw [← e1 w e]; exact b w hw
    · rintro ⟨⟨a, b, c⟩, h⟩
      refine ⟨a, fun w hw => ?_, c⟩
      by_cases e : w = w₀
      · subst e; exact e0.2 h
      · rw [e1 w e]; exact b w hw
  have hopen : IsOpen (lev S Kw' : Set (GUf E n)) := by
    refine hOp E n S Kw' fun w hw => ?_
    by_cases e : w = w₀
    · subst e
      simp only [Kw', Function.update_self]
      exact (hS.opn w hw).isOpenMap_subtype_val _ hχ
    · simp only [Kw', Function.update_of_ne e]; exact hS.opn w hw
  have hfix' : ∀ u : finU (E := E) (n := n), ofU u ∈ lev S Kw' → algRep W u f = f := fun u hu => by
    obtain ⟨a, h, e⟩ := (mem' _).1 hu
    have := hfix u a h
    rwa [show χ ⟨cLoc w₀ u.1, h⟩ = 1 from e, Units.val_one, one_smul] at this
  obtain ⟨φ, hφ, hφu, hφ0⟩ := hKer E n W j f hf0 (lev S Kw') (fun k hk => (mem_lev.1 hk).1) hfix'
  have hloc : ∀ y : Kw w₀, loc hw₀ y.1 ∈ lev S Kw := fun y => (hMem E n S Kw w₀ hw₀ hc0 y.1).1 hS.mem y.2
  choose R hR1 hR2 using fun a : HI π.V S => hHk E n a.w a.hw a.p a.hp a.i
  have hsv : ∀ (w : Plc E) (hw : IsSplitAt w), w ∉ S → cj w ∉ S → ∀ B, SatU π.V w B →
      IsSatVecGL w ((algRep W).comp (locF hw)) f B := fun w hw h1 h2 B hB =>
    hSat E n π W f hf hf0 w hw (fun k hk => hfix' _ ((hMem E n S Kw' w hw h2 k).2 h1 hk)) B hB
  obtain ⟨Φ, hΦ, hΦ0, heig, ψ, hψ⟩ := hExt (Gam0 E n) (GUf E n) AfQˣ (Af E)ˣ _ rat (lev S Kw') (xi0 W j) sim ζ hζ.central
    (by
      obtain ⟨s, hs⟩ := hCl E ((lev S Kw').comap ζ) (hopen.preimage hζ.cont)
      refine ⟨s, fun z => ?_⟩
      obtain ⟨t, ht, o, ho, k, e⟩ := hs z
      obtain ⟨γ, h1, h2⟩ := hXi E n W j x ζ hζ k
      exact ⟨t, ht, o, _, e, ho, γ, _, h1, h2⟩)
    φ hφ hφ0 (Kw w₀ ⊕ HI π.V S)
    (Sum.elim (fun y => Finsupp.single (loc hw₀ y.1) 1) fun a => ∑ y ∈ R a, Finsupp.single (loc a.hw y) 1)
    (Sum.elim (fun y => (χ y : ℂ)) fun a => satEig (Formalism.UG.qV E a.w) n a.B a.i)
    (by
      rintro (y | a) u hu
      · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hu)
        rfl
      · obtain ⟨y, -, hy⟩ := Finsupp.mem_support_finsetSum u hu
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hy)
        rfl)
    (by
      rintro (y | a) Ψ hΨ
      · refine ⟨fun γ g => ?_, fun k hk g => ?_⟩
        · simp only [Sum.elim_inl, rop_single, mul_assoc, hΨ.1]
        · simp only [Sum.elim_inl, rop_single]
          obtain ⟨a, h, e⟩ := (mem' _).1 hk
          have hk' : (loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1 ∈ lev S Kw' := by
            have h' : comp w₀ ((loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1) = (y⁻¹ * ⟨_, h⟩ * y : Kw w₀) := by
              rw [map_mul, map_mul, map_inv, comp_loc]; rfl
            have h'' : comp w₀ ((loc hw₀ y.1)⁻¹ * k * loc hw₀ y.1) ∈ Kw w₀ := by rw [h']; exact Subtype.property _
            refine (mem' _).2 ⟨mul_mem (mul_mem (inv_mem (hloc y)) a) (hloc y), h'', ?_⟩
            rw [show (⟨_, h''⟩ : Kw w₀) = y⁻¹ * ⟨_, h⟩ * y from Subtype.ext h', map_mul, map_mul, e, map_inv, mul_one,
              inv_mul_cancel]
          rw [← hΨ.2 _ hk' (g * loc hw₀ y.1)]
          simp only [mul_assoc, mul_inv_cancel_left]
      · have := hR2 a S Kw' a.h1 a.h2 _ (xi0 W j) Ψ hΨ
        convert this using 1
        funext g
        exact rop_sum _ _ _ _)
    (by
      rintro (y | a) g hg
      · obtain ⟨u, rfl⟩ := (hU E n).2 g hg
        simp only [Sum.elim_inl, rop_single]
        have h : cLoc w₀ (locF hw₀ y.1).1 ∈ Kw w₀ := by rw [cLoc_locF]; exact y.2
        have e := hfix (locF hw₀ y.1) (hloc y) h
        rw [show (⟨_, h⟩ : Kw w₀) = y from Subtype.ext (cLoc_locF _ _)] at e
        rw [show ofU u * loc hw₀ y.1 = ofU (u * locF hw₀ y.1) from (map_mul ofU _ _).symm, hφu, hφu]
        rw [Subgroup.coe_mul, ← algForms.val_algRep, e]
        rfl
      · obtain ⟨u, rfl⟩ := (hU E n).2 g hg
        simp only [Sum.elim_inr, rop_sum]
        have e := (hsv a.w a.hw a.h1 a.h2 a.B a.hB).2.2.2 a.p a.hp a.i a.hi
        rw [hR1 a] at e
        have e2 : ∀ y, φ (ofU u * loc a.hw y) = algForms.val (((algRep W).comp (locF a.hw)) y f) u.1 := fun y => by
          rw [show ofU u * loc a.hw y = ofU (u * locF a.hw y) from (map_mul ofU _ _).symm, hφu]
          rfl
        simp only [e2]
        let L : algForms W →ₗ[ℂ] Module.Dual ℂ W.Sp :=
          { toFun := fun F => algForms.val F u.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        have e3 := congrArg L e
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_smul] at e3
        rw [hφu]
        exact e3)
  refine ⟨Φ, ψ, ⟨hΦ0, hΦ.1, fun k hk h g => ?_, fun w hw h1 h2 B hB => ⟨hΦ0, ?_, (hsv w hw h1 h2 B hB).2.2.1, fun p hp i hi => ?_⟩⟩, hψ.1⟩
  · have h1 := congrFun (heig (Sum.inl ⟨_, h⟩)) g
    simp only [Sum.elim_inl, rop_single, Pi.smul_apply] at h1
    have h' : comp w₀ ((loc hw₀ (comp w₀ k))⁻¹ * k) = 1 := by rw [map_mul, map_inv, comp_loc, inv_mul_cancel]
    have h'' : comp w₀ ((loc hw₀ (comp w₀ k))⁻¹ * k) ∈ Kw w₀ := by rw [h']; exact one_mem _
    have hk' : (loc hw₀ (comp w₀ k))⁻¹ * k ∈ lev S Kw' :=
      (mem' _).2 ⟨mul_mem (inv_mem (hloc ⟨_, h⟩)) hk, h'', by
        rw [show (⟨_, h''⟩ : Kw w₀) = 1 from Subtype.ext h', map_one]⟩
    rw [← h1, ← hΦ.2 _ hk' (g * loc hw₀ (comp w₀ k)), mul_assoc, mul_inv_cancel_left]
  · exact GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext fun g => hΦ.2 _ ((hMem E n S Kw' w hw h2 k).2 h1 hk) g
  · let a : HI π.V S := ⟨w, hw, h1, h2, B, hB, p, hp, i, hi⟩
    have h3 := heig (Sum.inr a)
    rw [show heckeVec _ _ _ Φ = _ from hR1 a _ _ Φ]
    refine Eq.trans ?_ h3
    funext g
    rw [Finset.sum_apply]
    exact (rop_sum _ _ _ _).symm

end UpperTheory.Gal.CertificateRingHomMap
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.ExistsOpenAvoid
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhd2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem exists_open_avoid (w : Plc E) (x : GLw n w) (hx : x ≠ 1) :
    ∃ V : Subgroup (GLw n w), IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n) ∧ x ∉ V := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  by_cases hxK : x ∈ GlobalTheory.LFun.KGL w (n := n)
  swap
  · exact ⟨_, hKo, le_rfl, hxK⟩
  have hne : ∃ i j, x.val i j ≠ (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    by_contra h
    push_neg at h
    exact hx (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hne
  haveI : CompactSpace ↥(GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hKc
  let f : ↥(GlobalTheory.LFun.KGL w (n := n)) → w.adicCompletion E :=
    fun g => g.1.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
  have hf : Continuous f :=
    Continuous.sub (Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) i j) continuous_const
  obtain ⟨A, hA⟩ := NonarchimedeanAddGroup.is_nonarchimedean
    ({x.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j}ᶜ : Set (w.adicCompletion E))
    (isOpen_compl_singleton.mem_nhds (by simpa using (sub_ne_zero.2 hij).symm))
  have hW : IsClopen (f ⁻¹' (A : Set (w.adicCompletion E))) := A.isClopen.preimage hf
  have h1 : (1 : ↥(GlobalTheory.LFun.KGL w (n := n))) ∈ f ⁻¹' (A : Set (w.adicCompletion E)) := by
    simp [f, A.zero_mem]
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1
  refine ⟨(H : Subgroup _).map (GlobalTheory.LFun.KGL w (n := n)).subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · exact hKo.isOpenEmbedding_subtypeVal.isOpenMap _ H.isOpen
  · rintro ⟨h, hh, rfl⟩
    exact hA (hH hh) rfl

private theorem exists_Kw
    (F : Finset (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n)})) :
    ∃ Kw : ∀ w : Plc E, Subgroup (GLw n w), (∀ w, IsOpen (Kw w : Set (GLw n w)) ∧ Kw w ≤ GlobalTheory.LFun.KGL w (n := n)) ∧
      ∀ i ∈ F, Kw i.1 ≤ i.2.1 := by
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨fun w => GlobalTheory.LFun.KGL w (n := n),
      fun w => ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).1, le_rfl⟩, by simp⟩
  | insert i F _ ih =>
    obtain ⟨Kw, h1, h2⟩ := ih
    obtain ⟨v, V, hVo, hVK⟩ := i
    have hle : ∀ w, Function.update Kw v (Kw v ⊓ V) w ≤ Kw w := fun w => by
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact inf_le_left
      · rw [Function.update_of_ne h]
    refine ⟨Function.update Kw v (Kw v ⊓ V), fun w => ?_, fun j hj => ?_⟩
    · refine ⟨?_, (hle w).trans (h1 w).2⟩
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact (h1 w).1.inter hVo
      · rw [Function.update_of_ne h]
        exact (h1 w).1
    · rcases Finset.mem_insert.1 hj with rfl | hj
      · simp only [Function.update_self]
        exact inf_le_right
      · exact (hle j.1).trans (h2 j hj)

end UpperTheory.Gal.CertificateRingHomMap.PNbhd2

theorem UpperTheory.Gal.CertificateRingHomMap.pNbhd2_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 := by
  intro E _ _ _ n O hO
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hfin : ∀ x : UA E n, x ∈ finU (E := E) (n := n) ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  have hKc := GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)
  have hKo := GlobalTheory.EulerTwRestr.isOpen_Kglob (E := E) (n := n)
  have hC : IsCompact {u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} :=
    IsCompact.of_isClosed_subset (hι.isCompact_preimage (hKc.image GlobalTheory.DefU.LocAdm.continuous_finGL))
      ((Subgroup.isClosed_of_isOpen _ hKo).preimage hp) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩
  have hL : ∀ w : Plc E, Continuous fun u : finU (E := E) (n := n) => cLoc w u.1 := fun w =>
    (show Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) from
      Continuous.units_map _ (Continuous.matrix_map continuous_id
        (show Continuous (pLoc E w) from RestrictedProduct.continuous_eval
          (R := fun w : Plc E => w.adicCompletion E)
          (A := fun w : Plc E => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) w))).comp hp
  let D : (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n)}) →
      Set (finU (E := E) (n := n)) := fun i => {u | cLoc i.1 u.1 ∈ i.2.1}
  have hD : ∀ i, IsClosed (D i) := fun i => (Subgroup.isClosed_of_isOpen _ i.2.2.1).preimage (hL i.1)
  have hone : ∀ u : finU (E := E) (n := n), (∀ i, u ∈ D i) → u = 1 := by
    intro u hu
    have h1 : ∀ w : Plc E, cLoc w u.1 = 1 := by
      intro w
      by_contra hne
      obtain ⟨V, hVo, hVK, hV⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_open_avoid w _ hne
      exact hV (hu ⟨w, V, hVo, hVK⟩)
    have h2 : p u = 1 := GlobalTheory.EulerTwRestr.gl_ext fun w => (h1 w).trans (map_one _).symm
    have h3 : GeneralLinearGroup.map (pInf E) (u.1 : GA E n) = 1 := u.2
    exact Subtype.ext (Subtype.ext (ga_ext (by rw [h3]; simp) (by simpa using (show GeneralLinearGroup.map (pFin E) (u.1 : GA E n) = 1 from h2))))
  have hemp : ({u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU (E := E) (n := n)))) ∩ ⋂ i, D i = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun u hu => ?_
    have := hone u (Set.mem_iInter.1 hu.2)
    exact hu.1.2 (this ▸ O.one_mem)
  obtain ⟨F, hF⟩ := (hC.diff hO).elim_finite_subfamily_closed D hD (Set.disjoint_iff_inter_eq_empty.mpr hemp)
  obtain ⟨Kw, hK1, hK2⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_Kw F
  refine ⟨F.image Sigma.fst, Kw, hK1, fun u hu hS => ?_⟩
  by_contra huO
  have hmem : u ∈ ({u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU (E := E) (n := n)))) ∩ ⋂ i ∈ F, D i :=
    ⟨⟨GlobalTheory.EulerTwRestr.mem_Kglob.2 hu, huO⟩,
      Set.mem_iInter₂.2 fun i hi => hK2 i hi (hS i.1 (Finset.mem_image_of_mem _ hi))⟩
  exact Set.disjoint_left.mp hF hmem.1 hmem.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PLevOpen
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isOpen_intA (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, Valued.v (a v) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => ((v.adicCompletionIntegers F : ValuationSubring _) : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

private theorem continuous_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (sim : GUf E n → AfQˣ) := continuous_snd.comp continuous_subtype_val

private theorem continuous_mat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (mat : GUf E n → GL (Fin n) (Af E)) := continuous_fst.comp continuous_subtype_val

private theorem continuous_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Plc E) :
    Continuous (comp w : GUf E n → GL (Fin n) (w.adicCompletion E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp continuous_mat

theorem UpperTheory.Gal.CertificateRingHomMap.pLevOpen_of :
    UpperTheory.Gal.CertificateRingHomMap.LevOpen := by
  intro E _ _ _ n S Kw hK
  have hI : IsOpen {a : Af E | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA E
  have hJ : IsOpen {a : AfQ | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA ℚ
  let A : Set (GUf E n) :=
    ((((fun k => ((sim k : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1}) ∩
      ((fun k => (((sim k)⁻¹ : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1})) ∩
    ((⋂ i, ⋂ j, (fun k => (mat k).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}) ∩
      (⋂ i, ⋂ j, (fun k => ((mat k)⁻¹).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}))) ∩
    ⋂ w ∈ S, comp w ⁻¹' (Kw w : Set (GLw n w))
  have hAo : IsOpen A := by
    refine ((IsOpen.inter ?_ ?_).inter (IsOpen.inter ?_ ?_)).inter ?_
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim)
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim.inv)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat).matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat.inv).matrix_elem i j)
    · exact isOpen_biInter_finset fun w hw => (hK w hw).preimage (continuous_comp w)
  have hone : ∀ (i j : Fin n) (v : Plc E), Valued.v (((1 : Matrix (Fin n) (Fin n) (Af E)) i j) v) ≤ 1 := by
    intro i j v
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq]
      change Valued.v (1 : v.adicCompletion E) ≤ 1
      rw [map_one]
    · rw [Matrix.one_apply_ne h]
      change Valued.v (0 : v.adicCompletion E) ≤ 1
      rw [map_zero]
      exact zero_le'
  have hQ : ∀ v : Plc ℚ, Valued.v ((1 : AfQ) v) ≤ 1 := fun v => by
    change Valued.v (1 : v.adicCompletion ℚ) ≤ 1
    rw [map_one]
  have h1 : (1 : GUf E n) ∈ A := by
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simpa using hQ
    · simpa using hQ
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one, inv_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun w _ => (Kw w).one_mem
  have hsub : A ⊆ (lev S Kw : Set (GUf E n)) := by
    rintro k ⟨⟨⟨hs, hs'⟩, hm, hm'⟩, hc⟩
    simp only [Set.mem_iInter, Set.mem_preimage] at hm hm' hc
    refine mem_lev.2 ⟨fun v => ?_, fun w hw => hc w hw, fun w _ _ => ?_⟩
    · have h : Valued.v (((sim k : AfQˣ) : AfQ) v * (((sim k)⁻¹ : AfQˣ) : AfQ) v) = 1 := by
        change Valued.v ((((sim k : AfQˣ) : AfQ) * (((sim k)⁻¹ : AfQˣ) : AfQ)) v) = 1
        rw [Units.mul_inv]
        exact map_one _
      rw [map_mul] at h
      refine le_antisymm (hs v) ?_
      calc (1 : _) = _ := h.symm
        _ ≤ Valued.v (((sim k : AfQˣ) : AfQ) v) * 1 := mul_le_mul' le_rfl (hs' v)
        _ = _ := mul_one _
    · rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
      refine ⟨fun i j => hm i j w, fun i j => ?_⟩
      have : (comp w k)⁻¹ = GeneralLinearGroup.map (pLoc E w) (mat k)⁻¹ := (map_inv _ _).symm
      rw [this]
      exact hm' i j w
  exact Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hAo.mem_nhds h1) hsub)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PKapOf
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL)
open scoped Classical

private theorem scal_mem_KGL {E : Type} [Field E] [NumberField E] {n : ℕ} {u : Plc E}
    (a b : GL (Fin n) (u.adicCompletion E)) (t q : u.adicCompletion E)
    (ha : a.val = t • (1 : Matrix (Fin n) (Fin n) _)) (hb : b.val = q • (1 : Matrix (Fin n) (Fin n) _))
    (hq : q ≠ 0) (hv : Valued.v t = Valued.v q) : a⁻¹ * b ∈ KGL u (n := n) := by
  have hq' : Valued.v q ≠ 0 := (Valuation.ne_zero_iff _).2 hq
  have ht : t ≠ 0 := by
    rintro rfl
    exact hq' (by rw [← hv, map_zero])
  have hai : (a⁻¹).val = t⁻¹ • (1 : Matrix (Fin n) (Fin n) _) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [ha]; simp [smul_smul, ht])
  have hbi : (b⁻¹).val = q⁻¹ • (1 : Matrix (Fin n) (Fin n) _) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hb]; simp [smul_smul, hq])
  have e1 : (a⁻¹ * b).val = (t⁻¹ * q) • (1 : Matrix (Fin n) (Fin n) _) := by
    rw [Units.val_mul, hai, hb]; simp [smul_smul, mul_comm]
  have e2 : ((a⁻¹ * b)⁻¹).val = (q⁻¹ * t) • (1 : Matrix (Fin n) (Fin n) _) := by
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hbi, ha]; simp [smul_smul, mul_comm]
  have v1 : Valued.v (t⁻¹ * q) = 1 := by
    rw [map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']
  have v2 : Valued.v (q⁻¹ * t) = 1 := by
    rw [map_mul, map_inv₀, hv, inv_mul_cancel₀ hq']
  have key : ∀ (c : u.adicCompletion E), Valued.v c = 1 → ∀ i j,
      Valued.v ((c • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E))) i j) ≤ 1 := by
    intro c hc i j
    rw [Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [hc]
  refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val u _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [e1]; exact key _ v1 i j
  · rw [e2]; exact key _ v2 i j

theorem UpperTheory.Gal.CertificateRingHomMap.pKapOf_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke → UpperTheory.Gal.CertificateRingHomMap.XiZeta → UpperTheory.Gal.CertificateRingHomMap.IntSim → UpperTheory.Gal.CertificateRingHomMap.LevOpen → UpperTheory.Gal.CertificateRingHomMap.KapOf := by
  intro hFH hXi hIS hLO E _ _ _ n hn x ζ hζ U W j Up w₀ S Kw hS χ hχ Φ ψ hΦ hψ
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, Φ g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ.ne (funext h)
  have cancel : ∀ a b : ℂ, a • Φ g₀ = b • Φ g₀ → a = b := fun a b h => smul_left_injective ℂ hg₀ h
  have A : ∀ k ∈ lev S Kw, ∀ h : comp w₀ k ∈ Kw w₀, χ ⟨comp w₀ k, h⟩ = 1 → ∀ g, Φ (g * k) = Φ g := by
    intro k hk h h1 g
    rw [hΦ.right k hk h g, h1]
    simp
  have B : ∀ y, (∀ g, Φ (g * ζ y) = Φ g) → ψ y = 1 := by
    intro y hy
    have h := hy g₀
    rw [hψ] at h
    exact Units.ext (cancel _ 1 (by simpa using h))
  have C : ∀ k : GUf E n, (∀ u, comp u k ∈ KGL u (n := n)) → (∀ u ∈ S, comp u k = 1) → k ∈ lev S Kw :=
    fun k h1 h2 => mem_lev.2 ⟨hIS E n hn k h1, fun u hu => by rw [h2 u hu]; exact one_mem _, fun u _ _ => h1 u⟩
  have D : ∀ k ∈ lev S Kw, comp w₀ k = 1 → ∀ g, Φ (g * k) = Φ g := by
    intro k hk h1 g
    have h : comp w₀ k ∈ Kw w₀ := by rw [h1]; exact one_mem _
    refine A k hk h ?_ g
    have e : (⟨comp w₀ k, h⟩ : Kw w₀) = 1 := Subtype.ext h1
    rw [e, map_one]

  have hKo : IsOpen ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) := by
    have e : ((χ.ker.map (Kw w₀).subtype : Subgroup (GLw n w₀)) : Set (GLw n w₀)) =
        Subtype.val '' {k : Kw w₀ | χ k = 1} := by
      ext a
      simp [Subgroup.mem_map, MonoidHom.mem_ker]
    rw [e]
    exact (hS.opn w₀ hS.mem).isOpenMap_subtype_val _ hχ
  have hK' := hLO E n S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype)) (by
    intro w hw
    by_cases h : w = w₀
    · subst h
      simpa using hKo
    · simpa [Function.update_of_ne h] using hS.opn w hw)
  have hker : IsOpen (((ψ⁻¹).ker : Subgroup (Af E)ˣ) : Set (Af E)ˣ) := by
    refine Subgroup.isOpen_mono (H₁ := (lev S (Function.update Kw w₀ (χ.ker.map (Kw w₀).subtype))).comap ζ) ?_
      (hK'.preimage hζ.cont)
    intro y hy
    have hy' := mem_lev.1 (Subgroup.mem_comap.1 hy)
    have h0 := hy'.2.1 w₀ hS.mem
    rw [Function.update_self] at h0
    obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 h0
    have hl : ζ y ∈ lev S Kw := by
      refine mem_lev.2 ⟨hy'.1, fun u hu => ?_, hy'.2.2⟩
      by_cases h : u = w₀
      · subst h
        rw [← hae]
        exact a.2
      · have := hy'.2.1 u hu
        rwa [Function.update_of_ne h] at this
    have h1 : ψ y = 1 := by
      refine B y fun g => A _ hl (by rw [← hae]; exact a.2) ?_ g
      have e : (⟨comp w₀ (ζ y), by rw [← hae]; exact a.2⟩ : Kw w₀) = a := Subtype.ext hae.symm
      rw [e]
      exact ha
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]
  have hprin : ∀ k : Eˣ, (((ψ⁻¹) (diagF E k) : ℂˣ) : ℂ) = (∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ)⁻¹ := by
    intro k
    obtain ⟨γ, h1, h2⟩ := hXi E n W j x ζ hζ k
    have e : ((ψ (diagF E k) : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, φ (k : E) ^ mOf x W j φ := by
      apply cancel
      rw [← hψ, ← hζ.central, h1, hΦ.left, h2]
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e]
  obtain ⟨κ, halg, hloc⟩ := hFH E (ψ⁻¹) (mOf x W j) hker hprin
  refine ⟨κ, halg, ?_, ?_⟩
  · intro w hw y hy
    have h1 : ψ (sgl w y) = 1 := by
      refine B _ fun g => D _ (C _ (hζ.unit w y hy) fun u hu => hζ.off w y u (hw u hu)) ?_ g
      exact hζ.off w y w₀ (hw w₀ hS.mem)
    rw [hloc, MonoidHom.inv_apply, h1, inv_one]
  · intro w hw hnw z hz g
    have hv : κ.val w = (ψ (sgl w (atFin w (unif w))))⁻¹ := by
      show κ.loc w (atFin w (unif w)) = _
      rw [hloc, MonoidHom.inv_apply]
    have hq : ∀ u : Plc E, ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion E) ≠ 0 := by
      intro u
      have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
        simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
      exact Nat.cast_ne_zero.2 h0
    have hc : ∀ u, comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) ∈ KGL u (n := n) ∧
        (¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1) := by
      intro u
      have hoff : ¬ SameK x (cj u) w → comp u ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) = 1 := by
        intro h
        rw [map_mul, map_inv, hζ.off w _ u h, (hz u).2 h, inv_one, one_mul]
      refine ⟨?_, hoff⟩
      by_cases h : SameK x (cj u) w
      · obtain ⟨t, ht, hvt⟩ := hζ.unif w _ (unif_spec w) hnw u h
        rw [map_mul, map_inv]
        exact scal_mem_KGL _ _ t _ ht ((hz u).1 h) (hq u) hvt
      · rw [hoff h]
        exact one_mem _
    have hk : (ζ (sgl w (atFin w (unif w))))⁻¹ * z ∈ lev S Kw :=
      C _ (fun u => (hc u).1) fun u hu => (hc u).2 (hw u hu)
    have e : z = ζ (sgl w (atFin w (unif w))) * ((ζ (sgl w (atFin w (unif w))))⁻¹ * z) := by
      rw [mul_inv_cancel_left]
    rw [e, ← mul_assoc, D _ hk ((hc w₀).2 (hw w₀ hS.mem)), hψ, hv]
    simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PRootsAlg
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem cpow_key (q n j : ℕ) (hq : 0 < q) :
    (q : ℂ) ^ (j.choose 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) =
      (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hρ : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (((n : ℂ) - 1) / 2) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [hρ, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast (q : ℂ) (j.choose 2), ← Complex.cpow_add _ _ hq0,
    Nat.cast_choose_two]
  congr 1
  ring

theorem UpperTheory.Gal.CertificateRingHomMap.pRootsAlg_of :
    UpperTheory.Gal.CertificateRingHomMap.RootsAlg := by
  intro q n hq B hB a c ϑ h
  refine ⟨?_, ?_⟩
  · have h0 := h 0 (Nat.zero_le n)
    simpa [GlobalTheory.LFun.satEig, Multiset.esymm] using h0
  · set ρ : ℂ := (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hρ
    set s : Multiset ℂ := B.map (fun b : ℂˣ => (b : ℂ)) with hs
    have hcard : Multiset.card s = n := by simp [hs, hB]
    have e1 : (UpperTheory.V.Af.algSat n q B).map (· * c) = s.map (fun x => (ρ * c) • x) := by
      have e0 : UpperTheory.V.Af.algSat n q B = s.map (fun α => ρ * α) := by
        show Multiset.map _ (B.bind fun b => ({(b : ℂ)} : Multiset ℂ)) = _
        rw [Multiset.bind_singleton]
      rw [e0, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      ring
    have e2 : Multiset.card (s.map (fun x => (ρ * c) • x)) = n := by simp [hcard]
    rw [e1, UpperTheory.Gal.crystallineComparison.rootPol, Multiset.prod_X_sub_X_eq_sum_esymm, e2, Finset.mul_sum, UpperTheory.Gal.crystallineComparison.heckePol]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hk : _ = ρ ^ j := cpow_key q n j hq
    rw [h j hjn, ← Multiset.pow_smul_esymm, smul_eq_mul]
    have e3 : (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (a * GlobalTheory.LFun.satEig q n B j * c ^ j) =
        a * ((-1) ^ j * ((ρ * c) ^ j * s.esymm j)) := by
      have e4 : GlobalTheory.LFun.satEig q n B j = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) * s.esymm j := rfl
      rw [e4, mul_pow]
      linear_combination ((-1) ^ j * a * s.esymm j * c ^ j) * hk
    rw [e3]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtEig
open Module

universe u v

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section

variable {Γ H A Z V J : Type} [Group Γ] [Group H] [Group A] [Group Z] [AddCommGroup V] [Module ℂ V]

end

end UpperTheory.Gal.CertificateRingHomMap

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExtZero
open Module
universe u v

namespace UpperTheory.Gal.CertificateRingHomMap

open GlobalTheory.LKDef.HeckeTraceForms

section
variable {Γ H A V : Type} [Group Γ] [Group H] [Group A] [AddCommGroup V] [Module ℂ V]
  {ι : Γ →* H} {K : Subgroup H} {ξ : Representation ℂ Γ V} {c : H →* A} {φ : H → V}

private theorem key (hφ : KerForm ι K ξ c φ) {γ γ' : Γ} {u u' k k' : H} (hu : c u = 1) (hu' : c u' = 1)
    (hk : k ∈ K) (hk' : k' ∈ K) (h : ι γ * u * k = ι γ' * u' * k') : ξ γ (φ u) = ξ γ' (φ u') := by
  obtain ⟨h1, h2, h3⟩ := hφ
  set δ := γ'⁻¹ * γ with hδ
  have hκ : k * k'⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk')
  have hu'eq : u' = ι δ * u * (k * k'⁻¹) := by
    have e1 : ι γ' * u' = ι γ * u * k * k'⁻¹ := by
      rw [h]
      group
    rw [hδ, map_mul, map_inv]
    calc u' = (ι γ')⁻¹ * (ι γ' * u') := by group
      _ = (ι γ')⁻¹ * ι γ * u * (k * k'⁻¹) := by
        rw [e1]
        group
  have hc : c (ι δ) * c (k * k'⁻¹) = 1 := by
    have e2 := congrArg c hu'eq
    rw [map_mul, map_mul, hu, hu', mul_one] at e2
    exact e2.symm
  have hcκ : c (k * k'⁻¹) = 1 := by
    apply h1 δ⁻¹ _ hκ
    rw [map_inv, map_inv, eq_inv_of_mul_eq_one_right hc]
  have hcδ : c (ι δ) = 1 := by
    rw [hcκ, mul_one] at hc
    exact hc
  rw [hu'eq, h3 _ hκ _ hcκ (by rw [map_mul, hcδ, hu, one_mul]), h2 δ u hcδ hu]
  rw [← Module.End.mul_apply, ← map_mul, hδ, mul_inv_cancel_left]

open Classical in
private noncomputable def ext0 (ι : Γ →* H) (K : Subgroup H) (ξ : Representation ℂ Γ V) (c : H →* A) (φ : H → V) (g : H) : V :=
  if h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ g = ι x.1 * x.2.1 * x.2.2 then
    ξ h.choose.1 (φ h.choose.2.1) else 0

private theorem extension_by_zero_double_coset (hφ : KerForm ι K ξ c φ) {γ : Γ} {u k : H} (hu : c u = 1) (hk : k ∈ K) :
    ext0 ι K ξ c φ (ι γ * u * k) = ξ γ (φ u) := by
  have h : ∃ x : Γ × H × H, c x.2.1 = 1 ∧ x.2.2 ∈ K ∧ ι γ * u * k = ι x.1 * x.2.1 * x.2.2 :=
    ⟨(γ, u, k), hu, hk, rfl⟩
  unfold ext0
  rw [dite_eq_left h]
  obtain ⟨s1, s2, s3⟩ := h.choose_spec
  exact key hφ s1 hu s2 hk s3.symm

private theorem extension_by_zero_outside_support {g : H} (h : ¬ ∃ γ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ * u * k) :
    ext0 ι K ξ c φ g = 0 := by
  unfold ext0
  rw [dite_eq_right]
  rintro ⟨x, hx1, hx2, hx3⟩
  exact h ⟨x.1, x.2.1, x.2.2, hx1, hx2, hx3⟩

end

theorem pExtZero_holds : ExtZero := by
  intro Γ H A V _ _ _ _ _ ι K ξ c φ hφ
  refine ⟨ext0 ι K ξ c φ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro γ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ * (ι γ₀ * u * k) = ι (γ * γ₀) * u * k := by rw [map_mul]; group
      rw [e, extension_by_zero_double_coset hφ hu hk, extension_by_zero_double_coset hφ hu hk, map_mul]; rfl
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ ι γ * g = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ⁻¹ * γ₀, u, k, hu, hk, ?_⟩
        rw [map_mul, map_inv]
        calc g = (ι γ)⁻¹ * (ι γ * g) := by group
          _ = (ι γ)⁻¹ * ι γ₀ * u * k := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg', map_zero]
  · intro k₁ hk₁ g
    by_cases hg : ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g = ι γ₀ * u * k
    · obtain ⟨γ₀, u, k, hu, hk, rfl⟩ := hg
      have e : ι γ₀ * u * k * k₁ = ι γ₀ * u * (k * k₁) := by group
      rw [e, extension_by_zero_double_coset hφ hu (K.mul_mem hk hk₁), extension_by_zero_double_coset hφ hu hk]
    · have hg' : ¬ ∃ γ₀ u k, c u = 1 ∧ k ∈ K ∧ g * k₁ = ι γ₀ * u * k := by
        rintro ⟨γ₀, u, k, hu, hk, e⟩
        refine hg ⟨γ₀, u, k * k₁⁻¹, hu, K.mul_mem hk (K.inv_mem hk₁), ?_⟩
        calc g = g * k₁ * k₁⁻¹ := by group
          _ = ι γ₀ * u * (k * k₁⁻¹) := by rw [e]; group
      rw [extension_by_zero_outside_support hg, extension_by_zero_outside_support hg']
  · intro u hu
    have := extension_by_zero_double_coset (γ := 1) hφ hu K.one_mem
    simpa using this
  · intro g hg
    by_contra h
    exact hg (extension_by_zero_outside_support h)

end UpperTheory.Gal.CertificateRingHomMap
end

namespace UpperTheory.Gal.CertificateRingHomMap

universe u v

theorem extZero_holds : ExtZero := pExtZero_holds
theorem centralEig2_holds : CentralEig2 := pCentralEig2_of
theorem extEig2_holds : ExtEig2 := pExtEig2_of extZero_holds centralEig2_holds
theorem locAdj_holds : LocAdj := pLocAdj_of
theorem rootsAlg_holds : RootsAlg := pRootsAlg_of
theorem finToHecke_holds : FinToHecke := pFinToHecke_of
theorem classFin_holds : ClassFin := pClassFin_of
theorem xiScalar_holds : XiScalar := pXiScalar_of
theorem xiZeta_holds : XiZeta := pXiZeta_of xiScalar_holds
theorem intConj_holds : IntConj := pIntConj_of
theorem intSim_holds : IntSim := pIntSim_of
theorem ofUBij_holds : OfUBij := pOfUBij_of
theorem locComm_holds : LocComm := pLocComm_of
theorem locMem_holds : LocMem := pLocMem_of intConj_holds locComm_holds
theorem levOpen_holds : LevOpen := pLevOpen_of
theorem intCompact_holds : IntCompact := pIntCompact_of
theorem levCompact_holds : LevCompact := pLevCompact_of intCompact_holds intConj_holds locComm_holds levOpen_holds
theorem nhds_basis_levelSubgroup : Nbhd2 := pNbhd2_of
theorem nbhdU_holds : NbhdU := pNbhdU_of nhds_basis_levelSubgroup intConj_holds locComm_holds ofUBij_holds
theorem sphType_holds : SphType := pSphType_of intConj_holds locComm_holds
theorem stepAt_holds : StepAt := pStepAt_of locAdj_holds locComm_holds ofUBij_holds
theorem vecU_holds : VecU := pVecU_of nbhdU_holds stepAt_holds sphType_holds locComm_holds
theorem satVal_holds : SatVal := pSatVal_of
theorem kerFormU_holds : KerFormU := pKerFormU_of ofUBij_holds
theorem heckePres_holds : HeckePres := pHeckePres_of locComm_holds locMem_holds
theorem kapOf_holds : KapOf := pKapOf_of finToHecke_holds xiZeta_holds intSim_holds levOpen_holds

theorem formGU_holds : FormGU :=
  pFormGU_of extEig2_holds classFin_holds xiZeta_holds kerFormU_holds heckePres_holds satVal_holds locMem_holds locComm_holds
    levOpen_holds ofUBij_holds

theorem seedGU_holds : SeedGU :=
  seedGU_of zetaEx_holds vecU_holds sphType_holds formGU_holds kapOf_holds levOpen_holds levCompact_holds

end UpperTheory.Gal.CertificateRingHomMap
