module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSubsingletonCohTwistTensLbPowStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerVanishingInductionBySectionSqTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerVanishingInductionBySectionSqTensor
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem twistConeVanishing_of_cut : ∀ {Y : Scheme.{0}} (A N : LB Y), A.IsLB → N.IsLB → ∀ (r : ℕ), 1 ≤ r → ∀ (hM : (lbPow (tens (lbPow N 2) A) r).IsLB) (s : (lbPow (tens (lbPow N 2) A) r).Sec) (G : Y.Modules), (∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < 2 * r → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)) → TwistConeVanishing A N (kernel (cutHom G hM s)) → TwistConeVanishing A N (cokernel (cutHom G hM s)) → TwistConeVanishing A N G := by
  intro Y A N hA hN r hr hM s G ⟨j₁, h₁⟩ ⟨jK, hK⟩ ⟨jC, hC⟩
  set φ := cutHom G hM s
  let ψ := Abelian.factorThruImage φ
  have hψ : ψ ≫ kernel.ι (cokernel.π φ) = φ := Abelian.image.fac φ
  have : Epi ψ := inferInstanceAs (Epi (Abelian.factorThruImage φ))
  have hS₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ)
      (kernel.condition _)).ShortExact := { exact := ShortComplex.exact_kernel _ }
  have hS₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  let eK : kernel ψ ≅ kernel φ := (kernelCompMono ψ _).symm ≪≫ kernelIsoOfEq hψ
  have arith : ∀ (a n : Pic Y) (j m : ℕ), r ≤ j → 2 * r ≤ m →
      (j - r) • a + (m - 2 * r) • n = (-1 : ℤ) • (r • (2 • n + a)) + (j • a + m • n) := by
    intro a n j m h₁ h₂
    obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le h₁
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le h₂
    simp only [Nat.add_sub_cancel_left]
    module
  set J := max j₁ (max jK jC) with hJ
  have hJ₁ : j₁ ≤ J := le_max_left _ _
  have hJK : jK ≤ J := (le_max_left _ _).trans (le_max_right _ _)
  have hJC : jC ≤ J := (le_max_right _ _).trans (le_max_right _ _)
  have key : ∀ m j, m ≤ j → 2 * J + m ≤ 2 * j → ∀ p, 0 < p →
      Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hmj hJj p hp
      by_cases hm : m < 2 * r
      · exact h₁ j m (by omega) hm p hp
      · push_neg at hm
        have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
        have e₁ := Twist.shortExact_map hT hS₁
        have e₂ := Twist.shortExact_map hT hS₂
        obtain ⟨iso⟩ : Nonempty (twist (twist G (lbZPow (lbPow (tens (lbPow N 2) A) r) (-1))) (tens (lbPow A j) (lbPow N m)) ≅
            twist G (tens (lbPow A (j - r)) (lbPow N (m - 2 * r)))) := by
          refine nonempty_twist_twist_iso_of_cls_eq G (isLB_lbZPow hM (-1)) hT
            (isLB_tens (isLB_lbPow hA _) (isLB_lbPow hN _)) ?_
          rw [cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _), cls_tens (isLB_lbPow hA _) (isLB_lbPow hN _),
            cls_lbZPow hM, cls_lbPow_tens_lbPow hN hA, cls_lbPow hA, cls_lbPow hN, cls_lbPow hA, cls_lbPow hN]
          exact arith _ _ j m (by omega) hm
        have hmid : Subsingleton (cohOn (twist (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1))
            (tens (lbPow A j) (lbPow N m))) ⊤ p) := by
          have := ih (m - 2 * r) (by omega) (j - r) (by omega) (by omega) p hp
          exact (cohOn.mapIso ℤ ⊤ p iso).toEquiv.subsingleton
        have hker : Subsingleton (cohOn (twist (kernel ψ) (tens (lbPow A j) (lbPow N m))) ⊤ (p + 1)) := by
          have := hK j m (by omega) hmj (p + 1) (by omega)
          exact @Equiv.subsingleton _ _ (cohOn.mapIso ℤ ⊤ (p + 1) ((twistFunctor _).mapIso eK)).toEquiv this
        have himg := cohOn.subsingleton₃ e₁ ⊤ p hmid hker
        exact cohOn.subsingleton₂ e₂ ⊤ p himg (hC j m (by omega) hmj p hp)
  exact ⟨2 * J, fun j m hj hmj p hp => key m j hmj (by omega) p hp⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerVanishingInductionBySectionSqTensorStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPowerVanishing_induction_by_section_sq_tensor : ∀ {Y : Scheme.{0}} (A N : LB Y), A.IsLB → N.IsLB → ∀ (r : ℕ), 1 ≤ r → ∀ (hM : (lbPow (tens (lbPow N 2) A) r).IsLB) (s : (lbPow (tens (lbPow N 2) A) r).Sec) (G : Y.Modules), (∃ j₁ : ℕ, ∀ j m : ℕ, j₁ ≤ j → m < 2 * r → ∀ p, 0 < p → Subsingleton (coh (twist G (tens (lbPow A j) (lbPow N m))) p)) → TwistConeVanishing A N (kernel (cutHom G hM s)) → TwistConeVanishing A N (cokernel (cutHom G hM s)) → TwistConeVanishing A N G := by
  first | exact @GlobalTheory.twistConeVanishing_of_cut | exact GlobalTheory.twistConeVanishing_of_cut | (intros; apply GlobalTheory.twistConeVanishing_of_cut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSupportKerMulSectionOfNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSupportKerMulSectionOfNonvanishing
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.KernelCut

private theorem subsingleton_kernel_sections_of_app_injective {Y : Scheme.{0}} {M N : Y.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (hφ : ∀ t, φ.app V t = 0 → t = 0) : Subsingleton Γ(kernel φ, V) := by
  have hmono : Mono ((kernel.ι φ).app V) := by
    have h1 : Mono ((Scheme.Modules.toPresheaf Y).map (kernel.ι φ)) := inferInstance
    exact (NatTrans.mono_iff_mono_app _).1 h1 (Opposite.op V)
  have hinj := (AddCommGrpCat.mono_iff_injective _).1 hmono
  have key : ∀ c : Γ(kernel φ, V), c = 0 := by
    intro c
    apply hinj
    rw [map_zero]
    apply hφ
    have h2 : (kernel.ι φ ≫ φ).app V c = 0 := by simp
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h2
    exact h2
  exact ⟨fun a b => by rw [key a, key b]⟩

private theorem notMem_support_of_subsingleton_sections {Y : Scheme.{0}} (K : Y.Modules) {x : Y} (W : Y.Opens)
    (hxW : x ∈ W) (h : ∀ V : Y.Opens, V ≤ W → Subsingleton Γ(K, V)) : x ∉ support K := by
  unfold support
  simp only [Set.mem_ofPred_eq, not_nontrivial_iff_subsingleton]
  have key : ∀ c : K.presheaf.stalk x, c = 0 := by
    intro c
    obtain ⟨U, hxU, t, rfl⟩ := K.presheaf.exists_germ_eq c
    rw [← K.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ W ≤ U)) x ⟨hxU, hxW⟩ t]
    have := h (U ⊓ W) inf_le_right
    rw [Subsingleton.elim (K.presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op t) 0, map_zero]
  exact ⟨fun a b => by rw [key a, key b]⟩

theorem notMem_support_kernel_cutHom : ∀ {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (s : L.Sec) (G : Y.Modules) [G.IsQuasicoherent], ∀ x ∈ Out.nonzeroLocus s, x ∉ support (kernel (cutHom G hL s)) := by
  intro Y L hL s G _ x hx
  have hx' : x ∈ ⨆ k, Y.basicOpen (s.f k) := by
    unfold Out.nonzeroLocus at hx
    exact hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
  have hle : Y.basicOpen (s.f k) ≤ Out.nonzeroLocus s := by
    unfold Out.nonzeroLocus
    exact le_iSup (fun j => Y.basicOpen (s.f j)) k
  refine notMem_support_of_subsingleton_sections _ (Y.basicOpen (s.f k)) hk fun V hV => ?_
  have hVU : V ≤ L.U k := hV.trans (Y.basicOpen_le _)
  have hmb := isMulBy_cutHom G hL s
  obtain ⟨e, he⟩ := hmb k V hVU
  have hunit : IsUnit (resG Y hVU (s.f k)) := by
    have h3 := isUnit_resG_zfun (zofSec s) k hVU
      (by rw [nonzeroLocus_zofSec hL s]; exact hV.trans hle)
    simpa using h3
  refine subsingleton_kernel_sections_of_app_injective _ V fun t ht => ?_
  rw [he] at ht
  have h4 : e t = 0 := hunit.smul_eq_zero.1 ht
  exact e.injective (h4.trans e.map_zero.symm)

end GlobalTheory.KernelCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSupportKerMulSectionOfNonvanishingStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.notMem_support_ker_mulSection_of_nonvanishing : ∀ {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (s : L.Sec) (G : Y.Modules) [G.IsQuasicoherent], ∀ x ∈ Out.nonzeroLocus s, x ∉ support (kernel (cutHom G hL s)) := by
  first | exact @GlobalTheory.KernelCut.notMem_support_kernel_cutHom | exact GlobalTheory.KernelCut.notMem_support_kernel_cutHom | (intros; apply GlobalTheory.KernelCut.notMem_support_kernel_cutHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushf
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushf
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false
noncomputable section

namespace GlobalTheory

theorem subsingleton_coh_twist_pushforward_iff {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    {A N : LB X} (hA : A.IsLB) (hN : N.IsLB) (G : Y.Modules) [G.IsQuasicoherent] (j m p : ℕ) :
    Subsingleton (coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p) ↔
      Subsingleton (coh (twist ((Scheme.Modules.pushforward g).obj G)
        (tens (lbPow A j) (lbPow N m))) p) := by
  have hT : (tens (lbPow A j) (lbPow N m)).IsLB := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  have hA' := LB.isLB_pull hA g
  have hN' := LB.isLB_pull hN g
  have hT' : (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m)).IsLB :=
    isLB_tens (isLB_lbPow hA' j) (isLB_lbPow hN' m)
  have hTp := LB.isLB_pull hT g
  have e : cls _ hT' = cls _ hTp := by
    apply (cls_eq_iff hT' hTp).2
    let a := chartPullPowPull A g j
    let b := chartPullPowPull N g m
    have c : ChartPull (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))
        (tens (lbPow A j) (lbPow N m)) g := by
      refine ⟨fun t => (a.idx t.1, b.idx t.2), fun t _ hz => ⟨a.le _ hz.1, b.le _ hz.2⟩, ?_⟩
      intro z i k hi hk
      exact (gm_tens _ _ (𝟙 Y) z i k hi hk).trans ((congrArg₂ (· * ·)
        (a.g z _ _ hi.1 hk.1) (b.g z _ _ hi.2 hk.2)).trans
          (gm_tens _ _ g z (a.idx i.1, b.idx i.2) (a.idx k.1, b.idx k.2)
            ⟨a.le _ hi.1, b.le _ hi.2⟩ ⟨a.le _ hk.1, b.le _ hk.2⟩).symm)
    exact LBIso.chartPull c (chartPullPull _ g) (PolBaseChange.lbIso_refl hT)
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq G hT' hTp e
  have := Twist.isQuasicoherent_twist (F := G) hTp
  have e₁ : coh (twist ((Scheme.Modules.pushforward g).obj G) (tens (lbPow A j) (lbPow N m))) p ≃ₗ[ℤ]
      coh (twist G (tens (lbPow (A.pull g) j) (lbPow (N.pull g) m))) p :=
    (cohOn.mapIso ℤ ⊤ p (Twist.projIso _ g G).symm).trans
      ((LinearEquiv.ofBijective (cohPushMap ℤ g (fun r => by simp) (twist G _) ⊤ p)
        (cohPushMap_bijective_of_isAffineHom ℤ g (fun r => by simp) (twist G _) ⊤ p)).trans (cohOn.mapIso ℤ ⊤ p i.symm))
  exact e₁.toEquiv.subsingleton_congr.symm

theorem twistConeVanishing_pull_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g]
    (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent],
    (TwistConeVanishing (A.pull g) (N.pull g) G ↔
      TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  intro X Y g _ A N hA hN G _
  unfold TwistConeVanishing
  simp only [subsingleton_coh_twist_pushforward_iff g hA hN G]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPowerHigherCohomVanishingPullbackIffPushfStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsAffineHom g] (A N : LB X), A.IsLB → N.IsLB → ∀ (G : Y.Modules) [G.IsQuasicoherent], (TwistConeVanishing (A.pull g) (N.pull g) G ↔ TwistConeVanishing A N ((Scheme.Modules.pushforward g).obj G)) := by
  first | exact @GlobalTheory.twistConeVanishing_pull_iff_pushforward | exact GlobalTheory.twistConeVanishing_pull_iff_pushforward | (intros; apply GlobalTheory.twistConeVanishing_pull_iff_pushforward <;> assumption)
end
end

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem TwistConeVanishing.of_isZero {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {F : X.Modules} (hF : IsZero F) : TwistConeVanishing A N F :=
  ⟨0, fun j m _ _ p _ => cohOn.subsingleton_of_isZero
    ((isZero_twist_iff (isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m))).2 hF) ⊤ p⟩

theorem TwistConeVanishing.of_shortExact {X : Scheme.{0}} {A N : LB X} (hA : A.IsLB) (hN : N.IsLB)
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (h₁ : TwistConeVanishing A N S.X₁)
    (h₃ : TwistConeVanishing A N S.X₃) : TwistConeVanishing A N S.X₂ := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₃
  refine ⟨max a b, fun j m hj hm p hp => ?_⟩
  have hT := isLB_tens (isLB_lbPow hA j) (isLB_lbPow hN m)
  exact cohOn.subsingleton₂ (Twist.shortExact_map hT hS) ⊤ p
    (ha j m (le_of_max_le_left hj) hm p hp) (hb j m (le_of_max_le_right hj) hm p hp)

theorem TwistConeVanishing.of_generic (k : Type) [Field k] {V : Scheme.{0}} [IsIntegral V]
    (f : V ⟶ Sp k) (hf : IsProjOver f) (A N : LB V) (hA : IsAmpleLB A) (hN : IsPsEff N)
    (G : V.Modules) [IsFiniteQC G]
    (h : ∀ E : V.Modules, IsFiniteQC E → genericPoint V ∉ support E → TwistConeVanishing A N E) :
    TwistConeVanishing A N G := by
  have : AlgebraicGeometry.IsNoetherian V := isNoetherian_of_isProjOver hf
  obtain ⟨r, hr, s, hs⟩ := hN.exists_hasNonzeroSec hA (m := 2) (by norm_num)
  have hM : (lbPow (tens (lbPow N 2) A) r).IsLB :=
    isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB 2) hA.isLB) r
  have hgen : genericPoint V ∈ Out.nonzeroLocus s := (sec_ne_zero_iff s).1 hs
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.T.exists_subsingleton_coh_twist_tens_lbPow' k f hf A N hA hN.isLB G (2 * r)
  have hCf : IsFiniteQC (cokernel (cutHom G hM s)) := ((cut_by_regular_section.{0} G hM).1 s).2.2.1
  have hCs : support (cokernel (cutHom G hM s)) = support G \ ↑(Out.nonzeroLocus s) :=
    ((cut_by_regular_section.{0} G hM).1 s).2.2.2.1
  haveI : IsFiniteQC (twistZ G (lbPow (tens (lbPow N 2) A) r) (-1)) :=
    isFiniteQC_twist (isLB_lbZPow hM (-1))
  refine GlobalTheory.T.twistedPowerVanishing_induction_by_section_sq_tensor A N hA.isLB hN.isLB r hr hM s G ⟨j₁, hj₁⟩ (h _ inferInstance ?_)
    (h _ hCf ?_)
  · exact GlobalTheory.T.notMem_support_ker_mulSection_of_nonvanishing hM s G _ hgen
  · rw [hCs]
    exact fun h' => h'.2 hgen

end GlobalTheory

namespace GlobalTheory

theorem eventually_subsingleton_coh_ample_psEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → ∀ F : X.Modules, IsFiniteQC F → ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p → Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p) := by
  intro k _ X f hf A N hA hN hpe F hF
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  refine devissage X (TwistConeVanishing A N) (fun _ h => .of_isZero hA.isLB hN h)
    (fun _ hS _ _ h₁ h₃ => .of_shortExact hA.isLB hN hS h₁ h₃) ?_ F hF
  intro Z hZ hsmall G hG
  haveI := hG
  haveI := isIntegral_red hZ
  have hAV : IsAmpleLB (A.pull (redι Z)) := hA.pull_of_isClosedImmersion _
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN G).1 ?_
  refine TwistConeVanishing.of_generic k (redι Z ≫ f)
    (ProjSpace.isProjOver_comp_of_isClosedImmersion _ hf) _ _ hAV (hpe Z hZ) G ?_
  intro E hE hη
  haveI := hE
  have hE' : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj E) :=
    ProperFinite.isFiniteQC_pushforward (redι Z) hAV E
  refine (GlobalTheory.T.twistedPowerHigherCohomVanishing_pullback_iff_pushforward (redι Z) A N hA.isLB hN E).2 (hsmall _ hE' ?_)
  have hsub := GlobalTheory.T.support_pushforward_subset_image (redι Z) E
  refine ⟨hsub.trans ((Set.image_subset_range _ _).trans (range_redι Z).le), fun hle => hη ?_⟩
  have hηZ : (redι Z) (genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ∈ (Z : Set X) :=
    (range_redι Z).le ⟨_, rfl⟩
  obtain ⟨y, hy, hyη⟩ := hsub (hle hηZ)
  rwa [(redι Z).isClosedEmbedding.injective hyη] at hy

end GlobalTheory
