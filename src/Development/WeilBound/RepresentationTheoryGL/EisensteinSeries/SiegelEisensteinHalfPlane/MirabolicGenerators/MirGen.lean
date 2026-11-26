module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMul

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssembly
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.EisCore

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem avg_const_mul {K : Subgroup G} [MeasurableSpace K] (μ : Measure K) (ρ : K →* (W →L[ℂ] W)) (a : ℂ) (f : K → ℂ) :
    avg μ ρ (fun κ => a * f κ) = a • avg μ ρ f := by
  simp only [avg, mul_smul]
  exact integral_smul a _

theorem eis_const_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (a : ℂ) (w : W) :
    eis Γ K P c ρ Λ g (a • w) = a • eis Γ K P c ρ Λ g w := by
  simp only [eis, map_smul]
  rw [← tsum_const_smul'']
  exact tsum_congr fun q => smul_comm _ _ _

theorem rep_mem {P Γ : Subgroup G} (q : Cos P Γ) : rep q ∈ Γ := (Quotient.out q).2

theorem ht_rep {Γ K : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {P : Subgroup G} (q : Cos P Γ) (g : G) :
    l (rep q * g) = l g := by
  rw [hl.left _ (Subgroup.mem_top _), hl.rat _ (rep_mem q) (Subgroup.mem_top _), zero_add]

theorem eis_add_ht {Γ K : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (P : Subgroup G) (c : G → ℂ)
    (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (w : W) :
    eis Γ K P c ρ (fun x => (l x : ℂ) + Λ x) g w = Complex.exp (l g) • eis Γ K P c ρ Λ g w := by
  simp only [eis]
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [ht_rep hl, Complex.exp_add, mul_smul]

theorem conv_add_ht {Γ K : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {P : Subgroup G} {f : G → ℝ}
    (h : Conv Γ P f) : Conv Γ P fun g => l g + f g := by
  intro g
  refine ((h g).mul_left (Real.exp (l g))).congr fun q => ?_
  show _ = Real.exp (l (rep q * g) + f (rep q * g))
  rw [ht_rep hl, Real.exp_add]

end Abstract

section ModPow

variable {k : Type} [Field k] [NumberField k]

theorem modPow_differentiable (x : IdeleGroup k) : Differentiable ℂ (modPow x) := by
  unfold modPow
  exact differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule k x).2.ne'))

theorem modPow_strip (x : IdeleGroup k) (b c : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖modPow x z‖ ≤ M := by
  have hr : (0 : ℝ) < (IdeleGroup.ideleModule k x : ℝ) := (IdeleGroup.ideleModule k x).2
  set r : ℝ := (IdeleGroup.ideleModule k x : ℝ) with hrdef
  refine ⟨r ^ b + r ^ c, by positivity, fun z hb hc => ?_⟩
  have e : ‖modPow x z‖ = r ^ z.re := Complex.norm_cpow_eq_rpow_re_of_pos hr z
  rw [e]
  have h1 : 0 ≤ r ^ b := by positivity
  have h2 : 0 ≤ r ^ c := by positivity
  rcases le_total 1 r with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hc
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hr h hb
    linarith

theorem polyEnt_mul_modPow (u : ℂ) (x : IdeleGroup k) {a : ℂ → ℂ} (ha : PolyEnt a) :
    PolyEnt fun z => u * modPow x z * a z := by
  refine ⟨((differentiable_const u).mul (modPow_differentiable x)).mul ha.1, fun b c => ?_⟩
  obtain ⟨M₁, h₁, hM₁⟩ := modPow_strip x b c
  obtain ⟨M₂, hM₂⟩ := ha.2 b c
  refine ⟨‖u‖ * M₁ * M₂, fun z hb hc => ?_⟩
  rw [norm_mul, norm_mul, mul_assoc (‖u‖ * M₁)]
  have := hM₂ z hb hc
  have := hM₁ z hb hc
  gcongr

end ModPow

section Fam

variable {G : Type} [Group G] [TopologicalSpace G] {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem polyFam_of {π : G →* GL ι 𝔸[k]} (hπ : Continuous π) {Ψ : (ι → 𝔸[k]) → ℂ} {ω : HeckeCharacter k}
    {F : ℂ → GL ι 𝔸[k] → ℂ} (h : IsEpCont Ψ ω F) (D : GL ι 𝔸[k]) :
    PolyFam fun z g => F z (π g * D) := by
  have hc : Continuous fun g => π g * D := hπ.mul continuous_const
  refine ⟨fun g => h.entire _, ?_, fun a b C hC => ?_⟩
  · exact h.cont.comp (continuous_fst.prodMk (hc.comp continuous_snd))
  · obtain ⟨M, hM⟩ := h.strip a b _ (hC.image hc)
    exact ⟨M, fun z h1 h2 g hg => hM z h1 h2 _ (Set.mem_image_of_mem _ hg)⟩

theorem leftFam_of {T : Type} [TopologicalSpace T] {t : ℂ → T → ℂ} (x : IdeleGroup k) (A B : ℂ) {N : ℝ} (hN : 3 / 2 ≤ N)
    (h1 : ∀ κ, DifferentiableOn ℂ (fun s => t s κ) {s | 1 < s.re})
    (h2 : ContinuousOn (fun y : ℂ × T => t y.1 y.2) ({s | 1 < s.re} ×ˢ Set.univ))
    (h3 : ∀ a b : ℝ, 1 < a → ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ κ, ‖t s κ‖ ≤ M) :
    LeftFam fun z κ => -A * ((N : ℂ) - z) * B * modPow x ((N : ℂ) - z) * t ((N : ℂ) - z) κ := by
  have hmaps : ∀ z : ℂ, z.re < 1 / 2 → 1 < ((N : ℂ) - z).re := fun z hz => by
    simp only [Complex.sub_re, Complex.ofReal_re]; linarith
  have hd : Differentiable ℂ fun z : ℂ => (N : ℂ) - z := by fun_prop
  have hp : Differentiable ℂ fun z : ℂ => -A * ((N : ℂ) - z) * B * modPow x ((N : ℂ) - z) :=
    (((differentiable_const _).mul hd).mul (differentiable_const _)).mul ((modPow_differentiable x).comp hd)
  refine ⟨fun κ => ?_, ?_, fun b c hc => ?_⟩
  · exact hp.differentiableOn.mul ((h1 κ).comp hd.differentiableOn fun z hz => hmaps z hz)
  · refine ContinuousOn.mul (hp.continuous.comp continuous_fst).continuousOn ?_
    refine h2.comp (f := fun y : ℂ × T => ((N : ℂ) - y.1, y.2)) (by fun_prop) fun y hy => ?_
    exact ⟨hmaps y.1 hy.1, Set.mem_univ _⟩
  · obtain ⟨M, hM⟩ := h3 (N - c) (N - b) (by linarith)
    obtain ⟨M₁, h₁, hM₁⟩ := modPow_strip x (N - c) (N - b)
    refine ⟨‖A‖ * (|N| + 1) * ‖B‖ * M₁ * |M|, fun z hb hcz κ => ?_⟩
    have hre : N - c ≤ ((N : ℂ) - z).re := by simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    have hre' : ((N : ℂ) - z).re ≤ N - b := by simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    have ht : ‖t ((N : ℂ) - z) κ‖ ≤ |M| := (hM _ hre hre' κ).trans (le_abs_self M)
    have hm := hM₁ _ hre hre'
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hn : ‖(N : ℂ) - z‖ ≤ (|N| + 1) * (1 + ‖z‖) ^ 2 := by
      have e1 : ‖(N : ℂ) - z‖ ≤ |N| + ‖z‖ := by
        refine (norm_sub_le _ _).trans ?_
        simp
      have e0 : 0 ≤ |N| := abs_nonneg N
      nlinarith [mul_nonneg e0 hz0, mul_nonneg hz0 hz0, mul_nonneg e0 (mul_nonneg hz0 hz0)]
    simp only [norm_mul, norm_neg]
    calc ‖A‖ * ‖(N : ℂ) - z‖ * ‖B‖ * ‖modPow x ((N : ℂ) - z)‖ * ‖t ((N : ℂ) - z) κ‖
        ≤ ‖A‖ * ((|N| + 1) * (1 + ‖z‖) ^ 2) * ‖B‖ * M₁ * |M| := by gcongr
      _ = _ := by ring

end Fam

theorem wall_core : EpMain → DGood → Master → SideOf → Term → ZetaK → SideUnfold → SideConv → ZetaOne → Core := by
  intro hEp hDG hMa hSO hTe hZK hSU hSC hZ1 G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hP k _ _ ι _ _ π Γ i₀ i₁ ω d c η η' l hM
    Ψ Ψ₁ φ L J hΨ hΨ₁ hzt hne hL hJ
  haveI : Nonempty ι := ⟨i₀⟩
  obtain ⟨V, hV, hEk⟩ := hEp k
  obtain ⟨F, F', hF, hF', hFE, hval⟩ := hEk ι Ψ ω hΨ hM.sq
  obtain ⟨hS, hS', htr, hdet⟩ := hSO G K hK k ι π Γ i₀ i₁ ω d c η η' l hM
  obtain ⟨a₁, ha₁, ha₁eq⟩ := hZ1 k Ψ₁ ω hΨ₁ hM.sq
  have hΨh : GJMatrix.adelicFourierPi k Ψ ∈ GJMatrix.schwartzBruhatPi (K := k) (ι := ι) :=
    GJMatrix.adelicFourierPi_mem_schwartzBruhatPi hΨ
  generalize hΨhd : GJMatrix.adelicFourierPi k Ψ = Ψh at hF' hval hΨh
  generalize hd' : (fun i => (d i)⁻¹ : ι → IdeleGroup k) = d' at hS' htr
  have hpar' : IsPar Γ K ((stab 𝔸[k] {i₁}ᶜ).comap π) c := hM.par'
  obtain ⟨Nr, hNr⟩ : ∃ Nr : ℝ, Nr = (Fintype.card ι : ℝ) := ⟨_, rfl⟩
  have hN2 : (2 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast hM.two
  have hcast : ((Fintype.card ι : ℕ) : ℂ) = (Nr : ℂ) := by rw [hNr]; simp
  rw [← hNr]
  simp only [hcast] at hFE hval
  have hFeq : ∀ z : ℂ, Nr < z.re → ∀ m, F z m = z * (z - Nr) * epstein Ψ ω z m := fun z hz m => by
    rw [hF.eq z (hNr ▸ hz) m, hcast]
  have hF'eq : ∀ z : ℂ, Nr < z.re → ∀ m, F' z m = z * (z - Nr) * epstein Ψh ω z m := fun z hz m => by
    rw [hF'.eq z (hNr ▸ hz) m, hcast]
  have hlK : ∀ g (κ : K), l (g * κ) = l g := fun g κ => hM.htl.right g κ κ.2
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = (ω.toIdele (d i₀) : ℂ) := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu]; exact Circle.coe_ne_zero _
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = modPow (Matrix.GeneralLinearGroup.det (dgl d)) 1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = (ω.toIdele (d' i₁) : ℂ) := ⟨_, rfl⟩
  let a : ℂ → ℂ := fun z => u * modPow (d i₀) z * a₁ z
  let Φ : ℂ → G → ℂ := fun z g => F z (π g * dgl d)
  let ζ : ℂ → K → ℂ := fun z κ => -A * ((Nr : ℂ) - z) * B * modPow (d' i₁) ((Nr : ℂ) - z) *
    zt (tInv.comp π) d' i₁ Ψh ω ((Nr : ℂ) - z) κ
  have hPE : PolyEnt a := polyEnt_mul_modPow u (d i₀) ha₁
  have hPF : PolyFam Φ := polyFam_of hM.cont hF (dgl d)
  obtain ⟨hz1, hz2, hz3⟩ := hZK G K hK k ι (tInv.comp π) Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω d' c η' hS' Ψh hΨh
  have hLF : LeftFam ζ := leftFam_of (d' i₁) A B (by linarith) hz1 hz2 hz3
  have hLaw : ∀ z, Law K ((stab 𝔸[k] {i₁}ᶜ).comap π) c (ζ z) := fun z r κ hr => by
    have := (hTe G K hK k ι (tInv.comp π) Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω d' c η' hS').2 Ψh ((Nr : ℂ) - z)
    have h2 : zt (tInv.comp π) d' i₁ Ψh ω ((Nr : ℂ) - z) ((r * κ : K) : G) = c r * zt (tInv.comp π) d' i₁ Ψh ω ((Nr : ℂ) - z) (κ : G) := this.2.1 r κ hr
    show _ * zt _ _ _ _ _ _ ((r * κ : K) : G) = c r * (_ * zt _ _ _ _ _ _ (κ : G))
    rw [h2]; ring
  have hconvR : ∀ x : ℝ, Nr < x → Conv Γ ((stab 𝔸[k] {i₀}).comap π) fun g => x * η g := fun x hx =>
    hSC G K hK k ι π Γ ((stab 𝔸[k] {i₀}).comap π) i₀ ω d c η hS x (hNr ▸ hx)
  have hconvL : ∀ x : ℝ, x < -Nr → Conv Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) fun g => (l g + Nr * η' g) - x * η' g := fun x hx => by
    have h := conv_add_ht hM.htl (hSC G K hK k ι (tInv.comp π) Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω d' c η' hS' (Nr - x) (by rw [← hNr]; linarith))
    convert h using 2
    ring
  obtain ⟨z₀, hz₀, ht₀⟩ := hne
  rw [← hNr] at hz₀
  have hne' : ∃ z, z ≠ (Nr : ℂ) ∧ a z ≠ 0 := by
    refine ⟨z₀, fun h => ?_, ?_⟩
    · rw [h, Complex.ofReal_re] at hz₀; exact lt_irrefl _ hz₀
    · have hre : 1 < z₀.re := by linarith
      have n0 : z₀ ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
      have n1 : z₀ - 1 ≠ 0 := fun h => by
        rw [sub_eq_zero] at h; rw [h] at hre; simp at hre
      show u * modPow (d i₀) z₀ * a₁ z₀ ≠ 0
      rw [ha₁eq z₀ hre]
      exact mul_ne_zero (mul_ne_zero hu0 (modPow_ne_zero _ _)) (mul_ne_zero (mul_ne_zero n0 n1) ht₀)
  have hRight : ∀ z : ℂ, Nr < z.re → ∀ g (w : L), (z - 1) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) =
      ((z - Nr) * a z) • eis Γ K ((stab 𝔸[k] {i₀}).comap π) c ρ (fun x => z * η x) g w := by
    intro z hz g w
    have hre : 1 < z.re := by linarith
    have e1 : (fun κ : K => Φ z (g * κ)) = fun κ : K => (z * (z - Nr)) * epstein Ψ ω z (π (g * κ) * dgl d) :=
      funext fun κ => hFeq z hz _
    have hU := hSU G W K ρ hK hρ μ hμ hP k ι π Γ ((stab 𝔸[k] {i₀}).comap π) i₀ ω d c η hS Ψ hΨ z (hNr ▸ hz) g (J w)
    have e2 : (fun κ : K => zt π d i₀ Ψ ω z κ) = fun κ => tate Ψ₁ ω z * φ κ := funext (hzt z)
    rw [e2, avg_const_mul, ContinuousLinearMap.smul_apply, hJ, eis_const_smul, ← hu] at hU
    rw [e1, avg_const_mul, ContinuousLinearMap.smul_apply, hU]
    simp only [smul_smul]
    congr 1
    show _ = (z - Nr) * (u * modPow (d i₀) z * a₁ z)
    rw [ha₁eq z hre]; ring
  have hLeft : ∀ z : ℂ, z.re < -Nr → ∀ g (w : W), avg μ ρ (fun κ => Φ z (g * κ)) w =
      z • eis Γ K ((stab 𝔸[k] {i₁}ᶜ).comap π) c ρ (fun x => ((l x + Nr * η' x : ℝ) : ℂ) - z * η' x) g (avg μ ρ (ζ z) w) := by
    intro z hz g w
    have hs : Nr < ((Nr : ℂ) - z).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]; linarith
    have e1 : (fun κ : K => Φ z (g * κ)) = fun κ : K => (Complex.exp (l g) * A * (((Nr : ℂ) - z) * (-z))) *
        epstein Ψh ω ((Nr : ℂ) - z) ((tInv.comp π) (g * κ) * dgl d') := by
      funext κ
      show F z (π (g * κ : G) * dgl d) = _
      rw [hFE, hdet, htr, hF'eq _ hs, hlK, ← hA]
      ring
    have hU := hSU G W K ρ hK hρ μ hμ hP k ι (tInv.comp π) Γ ((stab 𝔸[k] {i₁}ᶜ).comap π) i₁ ω d' c η' hS' Ψh hΨh ((Nr : ℂ) - z) (hNr ▸ hs) g w
    have e2 : (fun x => ((l x + Nr * η' x : ℝ) : ℂ) - z * η' x) = fun x => (l x : ℂ) + ((Nr : ℂ) - z) * η' x := by
      funext x; push_cast; ring
    have e3 : ζ z = fun κ : K => (-A * ((Nr : ℂ) - z) * B * modPow (d' i₁) ((Nr : ℂ) - z)) *
        zt (tInv.comp π) d' i₁ Ψh ω ((Nr : ℂ) - z) κ := rfl
    rw [e1, avg_const_mul, ContinuousLinearMap.smul_apply, hU, e2, eis_add_ht hM.htl, e3, avg_const_mul,
      ContinuousLinearMap.smul_apply, eis_const_smul, ← hB]
    simp only [smul_smul]
    congr 1
    ring
  obtain ⟨Op, H, hWall, hH, O, hO, hOp⟩ := hMa G W K ρ hK hρ μ hμ hP Γ ((stab 𝔸[k] {i₀}).comap π) ((stab 𝔸[k] {i₁}ᶜ).comap π) c η η' (fun g => l g + Nr * η' g) L J Nr Nr Φ a ζ
    hpar' hL (by linarith) hconvR hconvL hPF hPE hne' hLF hLaw hRight hLeft
  refine ⟨Nr, fun z => (z - Nr) * (Complex.exp (z ^ 2) * a z), Op, H, hWall,
    ⟨fun z => Complex.exp (z ^ 2) * a z, (hDG a Nr hPE).1, fun z => rfl, fun ht => ?_⟩, ⟨O, hO, hOp⟩, fun hω => ?_⟩
  · have hre : 1 < ((Nr : ℂ)).re := by rw [Complex.ofReal_re]; linarith
    have n0 : (Nr : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; linarith
    have n1 : (Nr : ℂ) - 1 ≠ 0 := by
      have : (Nr - 1 : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    show Complex.exp ((Nr : ℂ) ^ 2) * (u * modPow (d i₀) Nr * a₁ Nr) ≠ 0
    rw [ha₁eq _ hre]
    exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (mul_ne_zero hu0 (modPow_ne_zero _ _))
      (mul_ne_zero (mul_ne_zero n0 n1) ht))
  · have hv := hval hω
    have hav : ∀ (C : ℂ), avg μ ρ (fun _ : K => C) = C • avg μ ρ (fun _ => 1) := fun C => by
      have := avg_const_mul μ ρ C (fun _ => 1)
      simpa using this
    refine ⟨⟨-(Nr * V), ?_, fun g w => ?_⟩, ⟨Complex.exp ((Nr : ℂ) ^ 2) * ((Nr : ℂ) - 1) * (Nr * V * A * Ψh 0), fun g w => ?_⟩⟩
    · have : (Nr : ℂ) * V ≠ 0 := by
        have h1 : Nr * V ≠ 0 := by
          have := mul_pos (by linarith : (0 : ℝ) < Nr) hV
          exact this.ne'
        exact_mod_cast h1
      exact neg_ne_zero.2 this
    · rw [hH]
      have e1 : (fun κ : K => Φ 0 (g * κ)) = fun _ => (Nr : ℂ) * V * Ψ 0 := funext fun κ => (hv _).1
      rw [e1, hav, ContinuousLinearMap.smul_apply, smul_smul]
      congr 1
      simp
    · rw [hH]
      have e1 : (fun κ : K => Φ Nr (g * κ)) = fun _ => (Nr : ℂ) * V * (Complex.exp (l g) * A) * Ψh 0 := funext fun κ => by
        show F Nr (π (g * κ : G) * dgl d) = _
        rw [(hv _).2, hdet, hlK, ← hA]
      rw [e1, hav, ContinuousLinearMap.smul_apply, smul_smul]
      congr 1
      ring

end GlobalTheory.CompanionTheory.EisCore
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssemblyStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_identity_assembly : EpMain → DGood → Master → SideOf → Term → ZetaK → SideUnfold → SideConv → ZetaOne → Core := by
  first | exact @GlobalTheory.CompanionTheory.EisCore.wall_core | exact GlobalTheory.CompanionTheory.EisCore.wall_core | (intros; apply GlobalTheory.CompanionTheory.EisCore.wall_core <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverage
noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisUnfold

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem integrable_of_continuous (μ : Measure K) [IsProbabilityMeasure μ] {F : K → (W →L[ℂ] W)}
    (hF : Continuous F) : Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem exists_avgCLM (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)}
    (hρ : Continuous ρ) :
    ∃ A : C(K, ℂ) →L[ℂ] (W →L[ℂ] W), ∀ f : C(K, ℂ), A f = avg μ ρ f := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • ρ κ) μ := fun f =>
    integrable_of_continuous μ (f.continuous.smul hρ)
  let A₀ : C(K, ℂ) →ₗ[ℂ] (W →L[ℂ] W) :=
    { toFun := fun f => avg μ ρ f
      map_add' := fun f g => by
        simp only [avg, ContinuousMap.coe_add, Pi.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨A₀.mkContinuous C fun f => ?_, fun f => rfl⟩
  have h : ∀ᵐ κ ∂μ, ‖f κ • ρ κ‖ ≤ C * ‖f‖ := Eventually.of_forall fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (hC κ (Set.mem_univ _)) (f.norm_coe_le_norm κ) (norm_nonneg _)
      ((norm_nonneg _).trans (hC κ (Set.mem_univ _)))
  have := norm_integral_le_of_norm_le_const h
  simpa [avg, A₀] using this

theorem avg_translate (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) {φ : K → ℂ} (hφ : Continuous φ) (κ₁ : K) :
    avg μ ρ (fun κ => φ (κ₁ * κ)) = ρ κ₁⁻¹ * avg μ ρ φ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hc : Continuous fun κ : K => κ₁ * κ := continuous_const.mul continuous_id
  have hI : Integrable (fun κ => φ (κ₁ * κ) • ρ (κ₁ * κ)) μ :=
    integrable_of_continuous μ ((hφ.comp hc).smul (hρ.comp hc))
  have h1 : avg μ ρ φ = ∫ κ, φ (κ₁ * κ) • ρ (κ₁ * κ) ∂μ :=
    (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) κ₁).symm
  have h2 := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹)) hI
  rw [h1]
  refine Eq.trans ?_ h2
  unfold avg
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  have h3 : (ρ κ₁⁻¹).comp (ρ (κ₁ * κ)) = ρ κ := by
    change ρ κ₁⁻¹ * ρ (κ₁ * κ) = ρ κ
    rw [← map_mul, inv_mul_cancel_left]
  change φ (κ₁ * κ) • ρ κ = ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹) (φ (κ₁ * κ) • ρ (κ₁ * κ))
  rw [map_smul, ContinuousLinearMap.compL_apply, h3]

end SlopeTestRemainingChoices

theorem unfold : SecLaw → AvgMem → Unfold := by
  intro hSec hAvg G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hpr Γ P c hpar φ Λ T hφ hLaw hΛ hT g u hu
    hb w
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hsec := (hSec G W K ρ hK hρ Γ P c hpar).1
  have hmem := hAvg G W K ρ hK hρ μ hμ hpr Γ P c hpar φ hφ hLaw w
  have key : ∀ q : Cos P Γ, ∃ (p : G) (κ₁ : K), p ∈ P ∧ rep q * g = p * κ₁ := fun q => by
    obtain ⟨p, hp, k, hk, e⟩ := hpar.iwa (rep q * g)
    exact ⟨p, ⟨k, hk⟩, hp, e⟩
  choose p κ₁ hp hpk using key
  have hterm : ∀ q (κ : K), T (rep q * (g * κ)) =
      (c (p q) * Complex.exp (Λ (p q))) * φ (κ₁ q * κ) := fun q κ => by
    have e : rep q * (g * (κ : G)) = p q * ((κ₁ q * κ : K) : G) := by
      rw [← mul_assoc, hpk q, Subgroup.coe_mul, mul_assoc]
    rw [e]
    exact hT _ (hp q) _
  have hc : ∀ q, Continuous fun κ : K => φ (κ₁ q * κ) := fun q =>
    hφ.comp (continuous_const.mul continuous_id)
  let f' : Cos P Γ → C(K, ℂ) := fun q => ⟨fun κ => φ (κ₁ q * κ), hc q⟩
  let f : Cos P Γ → C(K, ℂ) := fun q => (c (p q) * Complex.exp (Λ (p q))) • f' q
  have hfa : ∀ q κ, f q κ = T (rep q * (g * κ)) := fun q κ => by
    rw [hterm]
    simp [f, f']
  have hu0 : ∀ q, 0 ≤ u q := fun q => (norm_nonneg _).trans (hb q 1)
  have hsum : Summable f := Summable.of_norm_bounded hu fun q =>
    (ContinuousMap.norm_le _ (hu0 q)).2 fun κ => by
      rw [hfa]
      exact hb q κ
  obtain ⟨A, hA⟩ := exists_avgCLM μ hρ
  have hF : (fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ))) = ⇑(∑' q, f q) := by
    funext κ
    rw [← ContinuousMap.tsum_apply hsum]
    exact tsum_congr fun q => (hfa q κ).symm
  rw [hF, ← hA]
  have hL := ((ContinuousLinearMap.apply ℂ W w).comp A).map_tsum hsum
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hL
  rw [hL]
  unfold eis
  refine tsum_congr fun q => ?_
  have e1 : A (f q) w = (c (p q) * Complex.exp (Λ (p q))) • (ρ (κ₁ q)⁻¹ (avg μ ρ φ w)) := by
    have : A (f' q) = ρ (κ₁ q)⁻¹ * avg μ ρ φ := by
      rw [hA]
      exact avg_translate μ hρ hφ (κ₁ q)
    have e2 : A (f q) = (c (p q) * Complex.exp (Λ (p q))) • A (f' q) := map_smul A _ _
    rw [e2, this]
    rfl
  rw [e1, hpk q, hΛ _ _ (κ₁ q).2, hsec _ hmem _ (hp q), smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisUnfold
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverageStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_of_average : SecLaw → AvgMem → Unfold := by
  first | exact @GlobalTheory.CompanionTheory.RgEisUnfold.unfold | exact GlobalTheory.CompanionTheory.RgEisUnfold.unfold | (intros; apply GlobalTheory.CompanionTheory.RgEisUnfold.unfold <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentity
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisMG

open MeasureTheory Topology

section SlopeTestRemainingChoices

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem leftGood_map {f : ℂ → X} {a : ℝ} (T : X →L[ℂ] Y) (h : LeftGood f a) :
    LeftGood (fun z => T (f z)) a := by
  refine ⟨T.differentiable.comp_differentiableOn h.1, fun b c hc => ?_⟩
  obtain ⟨M, hM⟩ := h.2 b c hc
  exact ⟨‖T‖ * M, fun z h1 h2 =>
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM z h1 h2) (norm_nonneg _))⟩

theorem leftGood_mono {f : ℂ → X} {a b : ℝ} (hab : b ≤ a) (h : LeftGood f a) : LeftGood f b :=
  ⟨h.1.mono fun _ hz => lt_of_lt_of_le hz hab, fun b' c hc => h.2 b' c (lt_of_lt_of_le hc hab)⟩

end SlopeTestRemainingChoices

section Eis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G)
    (t : ℂ) (w : W) : eis Γ K P c ρ Λ g (t • w) = t • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [map_smul, smul_comm]

end Eis

theorem master : AvgMem → DGood → HGood → BGood → Master := by
  intro hM hD hH hB
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar hProb Γ P P' c η η' β L J R N Φ a ζ hpar hLe hR
    hcR hcL hΦ ha haN hζ hLaw hEqR hEqL
  obtain ⟨pr, hpr⟩ : (secSp K P' c ρ).ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional _
  let T : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] secSp K P' c ρ) :=
    ((ContinuousLinearMap.compL ℂ L W _).flip J).comp (ContinuousLinearMap.compL ℂ W W _ pr)
  let TJ : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] W) := (ContinuousLinearMap.compL ℂ L W W).flip J
  obtain ⟨hHd, hHc, hHb⟩ := hH G W K ρ hK hρ μ hHaar hProb Φ hΦ
  obtain ⟨hB1, hB2⟩ := hB G W K ρ hK hρ μ hHaar hProb ζ hζ
  obtain ⟨-, hD2⟩ := hD a N ha
  have hop : LeftGood (fun z : ℂ =>
      z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) (-R) := by
    have h2 := leftGood_map T hB2
    have e : (fun z : ℂ => T (z • (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) =
        fun z : ℂ => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)) :=
      funext fun z => map_smul T z _
    rw [e] at h2
    exact leftGood_mono (by linarith) h2
  refine ⟨fun z => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)),
    fun z g => TJ ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ fun κ => Φ z (g * κ)), ?_,
    fun _ _ _ => rfl, fun z => T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)),
    leftGood_map T hB1, fun _ _ => rfl⟩
  refine
    { le := hLe, pos := hR, convR := hcR, convL := hcL, dEnt := hD2, dNe := ?_, op := hop
      hol := fun g => TJ.differentiable.comp (hHd g)
      cont := TJ.continuous.comp hHc
      bdd := ?_, eqR := ?_, eqL := ?_ }
  · obtain ⟨z, hz, haz⟩ := haN
    exact ⟨z, mul_ne_zero (sub_ne_zero.2 hz) (mul_ne_zero (Complex.exp_ne_zero _) haz)⟩
  · intro b a' g
    obtain ⟨U, hU, M, hMb⟩ := hHb b a' g
    exact ⟨U, hU, ‖TJ‖ * M, fun z h1 h2 g' hg' =>
      (TJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hMb z h1 h2 g' hg') (norm_nonneg _))⟩
  · intro z hz g w
    have h := hEqR z hz g w
    change (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) = _
    rw [mul_smul, h, smul_smul]
    congr 1
    ring
  · intro z hz g w
    have hz' : z.re < 1 / 2 := by linarith
    have hcont : Continuous (ζ z) := by
      have h1 : Continuous fun t : K => (z, t) := by fun_prop
      exact hζ.cont.comp_continuous h1 fun t => ⟨hz', Set.mem_univ _⟩
    have hmem : avg μ ρ (ζ z) (J w) ∈ secSp K P' c ρ :=
      hM G W K ρ hK hρ μ hHaar hProb Γ P' c hpar (ζ z) hcont (hLaw z) (J w)
    have hOp : (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W) =
        (z * (Complex.exp (z ^ 2) * (z - 1))) • avg μ ρ (ζ z) (J w) := by
      have hp : ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) =
          (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w) :=
        congrArg Subtype.val
          (hpr ⟨_, (secSp K P' c ρ).smul_mem (Complex.exp (z ^ 2) * (z - 1)) hmem⟩)
      change z • ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) = _
      rw [hp, mul_smul z]
    change (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) =
      eis Γ K P' c ρ (fun x => β x - z * η' x) g
        (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W)
    rw [hOp, eis_smul, hEqL z hz g (J w), smul_smul, mul_comm z]

end GlobalTheory.CompanionTheory.RgEisMG
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentityStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.master_identity : AvgMem → DGood → HGood → BGood → Master := by
  first | exact @GlobalTheory.CompanionTheory.RgEisMG.master | exact GlobalTheory.CompanionTheory.RgEisMG.master | (intros; apply GlobalTheory.CompanionTheory.RgEisMG.master <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
noncomputable section

open MeasureTheory Filter Topology Metric PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisLeft

lemma gauss_strip (b c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
    ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 4 ≤ C := by
  set X := max |b| |c| with hX
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨8 * Real.exp ((1 + X) ^ 2 + X ^ 2), by positivity, fun z hb hc => ?_⟩
  have hx : |z.re| ≤ X := by
    rw [abs_le]
    constructor
    · have h1 := neg_abs_le b
      have h2 := le_max_left |b| |c|
      linarith
    · have h1 := le_abs_self c
      have h2 := le_max_right |b| |c|
      linarith
  have hn : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re]
  have hz : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  obtain ⟨t, ht⟩ : ∃ t, t = 1 + ‖z‖ := ⟨_, rfl⟩
  rw [← ht, hn]
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hta : t ≤ (1 + X) + |z.im| := by linarith
  have ht2 : t ^ 2 ≤ 2 * (1 + X) ^ 2 + 2 * z.im ^ 2 := by
    have h1 : t ^ 2 ≤ ((1 + X) + |z.im|) ^ 2 := pow_le_pow_left₀ ht0 hta 2
    have h2 : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
    nlinarith [sq_nonneg ((1 + X) - |z.im|)]
  have h4 : t ^ 4 ≤ 8 * Real.exp (t ^ 2 / 2) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := t ^ 2 / 2) (by positivity)
    have h2 : t ^ 4 = 8 * ((t ^ 2 / 2) ^ 2 / 2) := by ring
    have h3 : 0 ≤ t ^ 2 / 2 := by positivity
    linarith
  have hx2 : z.re ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs z.re]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  calc Real.exp (z.re ^ 2 - z.im ^ 2) * t ^ 4
      ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * (8 * Real.exp (t ^ 2 / 2)) := by gcongr
    _ = 8 * Real.exp (z.re ^ 2 - z.im ^ 2 + t ^ 2 / 2) := by rw [Real.exp_add]; ring
    _ ≤ 8 * Real.exp ((1 + X) ^ 2 + X ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

lemma leftGood_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℂ → E}
    (hd : DifferentiableOn ℂ A {z | z.re < 1 / 2})
    (hb : ∀ b c : ℝ, c < 1 / 2 → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖A z‖ ≤ M * (1 + ‖z‖) ^ 2) :
    LeftGood (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) (1 / 2) ∧
    LeftGood (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) (1 / 2) := by
  have hd1 : DifferentiableOn ℂ (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2} :=
    DifferentiableOn.smul
      (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * (z - 1)).differentiableOn hd
  have hd2 : DifferentiableOn ℂ (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2} :=
    DifferentiableOn.smul differentiableOn_id hd1
  have key : ∀ b c : ℝ, c < 1 / 2 → ∃ B : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
      ‖(Complex.exp (z ^ 2) * (z - 1)) • A z‖ * (1 + ‖z‖) ≤ B := by
    intro b c hc
    obtain ⟨M, hM⟩ := hb b c hc
    obtain ⟨C, hC0, hC⟩ := gauss_strip b c
    refine ⟨|M| * C, fun z h1 h2 => ?_⟩
    have hA : ‖A z‖ ≤ |M| * (1 + ‖z‖) ^ 2 :=
      (hM z h1 h2).trans (by gcongr; exact le_abs_self M)
    have hz1 : ‖z - 1‖ ≤ 1 + ‖z‖ := by
      have := norm_sub_le z 1
      simp only [norm_one] at this
      linarith
    have ht : 0 ≤ 1 + ‖z‖ := by positivity
    rw [norm_smul, norm_mul]
    calc ‖Complex.exp (z ^ 2)‖ * ‖z - 1‖ * ‖A z‖ * (1 + ‖z‖)
        ≤ ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) * (|M| * (1 + ‖z‖) ^ 2) * (1 + ‖z‖) := by gcongr
      _ = |M| * (‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 4) := by ring
      _ ≤ |M| * C := by
          gcongr
          exact hC z h1 h2
  refine ⟨⟨hd1, fun b c hc => ?_⟩, ⟨hd2, fun b c hc => ?_⟩⟩
  · obtain ⟨B, hB⟩ := key b c hc
    refine ⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩
    have : 1 ≤ 1 + ‖z‖ := by simp
    exact le_mul_of_one_le_right (norm_nonneg _) this
  · obtain ⟨B, hB⟩ := key b c hc
    refine ⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩
    rw [norm_smul, mul_comm]
    have : ‖z‖ ≤ 1 + ‖z‖ := by simp
    gcongr

theorem differentiableOn_integral {T E : Type} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E] (μ : Measure T) [IsFiniteMeasure μ] {r : T → E} (hr : Continuous r)
    {ζ : ℂ → T → ℂ} (hζ : LeftFam ζ) :
    DifferentiableOn ℂ (fun z => ∫ κ, ζ z κ • r κ ∂μ) {z | z.re < 1 / 2} := by
  have hopen : IsOpen {z : ℂ | z.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  intro z₀ hz₀
  have hz₀' : z₀.re < 1 / 2 := hz₀
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (1 / 2 - z₀.re) / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hball : ∀ w ∈ closedBall z₀ (2 * ε), w.re < 1 / 2 ∧ z₀.re - 2 * ε ≤ w.re ∧ w.re ≤ z₀.re + 2 * ε ∧
      ‖w‖ ≤ ‖z₀‖ + 2 * ε := by
    intro w hw
    have h1 : ‖w - z₀‖ ≤ 2 * ε := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z₀).re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
    have h3 := abs_le.mp (h2.trans h1)
    have h4 : ‖w‖ ≤ ‖z₀‖ + ‖w - z₀‖ := by
      have := norm_add_le z₀ (w - z₀)
      simpa using this
    simp only [Complex.sub_re] at h3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hsub : closedBall z₀ (2 * ε) ⊆ {z : ℂ | z.re < 1 / 2} := fun w hw => (hball w hw).1
  obtain ⟨M, hM⟩ := hζ.strip (z₀.re - 2 * ε) (z₀.re + 2 * ε) (by rw [hε]; linarith)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |M| * (1 + (‖z₀‖ + 2 * ε)) ^ 2 := ⟨_, rfl⟩
  have hbd : ∀ w ∈ closedBall z₀ (2 * ε), ∀ t, ‖ζ w t‖ ≤ B := by
    intro w hw t
    obtain ⟨-, h2, h3, h4⟩ := hball w hw
    refine (hM w h2 h3 t).trans ?_
    rw [hB]
    gcongr
    exact le_abs_self M
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hr.continuousOn
  have hR' : ∀ t, ‖r t‖ ≤ R := fun t => hR t (Set.mem_univ t)
  have hcont : ∀ z : ℂ, z.re < 1 / 2 → Continuous (ζ z) := by
    intro z hz
    have h := hζ.cont.comp_continuous (f := fun t : T => (z, t)) (by fun_prop)
      (fun t => ⟨hz, Set.mem_univ t⟩)
    exact h
  have hmeasF : ∀ z : ℂ, z.re < 1 / 2 → AEStronglyMeasurable (fun κ => ζ z κ • r κ) μ := fun z hz =>
    ((hcont z hz).measurable.aestronglyMeasurable).smul hr.aestronglyMeasurable
  have hdiff : ∀ (t : T) (z : ℂ), z.re < 1 / 2 → HasDerivAt (ζ · t) (deriv (ζ · t) z) z := fun t z hz =>
    (((hζ.hol t) z hz).differentiableAt (hopen.mem_nhds hz)).hasDerivAt
  have hd0 : Measurable fun t => deriv (ζ · t) z₀ := by
    let h : ℕ → ℂ := fun n => ((ε / (n + 1) : ℝ) : ℂ)
    have hh0 : ∀ n, h n ≠ 0 := fun n => by
      have : ε / ((n : ℝ) + 1) ≠ 0 := by positivity
      exact Complex.ofReal_ne_zero.mpr this
    have hhs : ∀ n, z₀ + h n ∈ closedBall z₀ (2 * ε) := by
      intro n
      have h1 : ε / ((n : ℝ) + 1) ≤ ε := div_le_self hε0.le (by simp)
      have h2 : 0 ≤ ε / ((n : ℝ) + 1) := by positivity
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, h, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg h2]
      linarith
    have hlim : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hh0⟩
      have h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
        simpa [div_eq_mul_inv] using h0
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa [h, Function.comp_def] using h2
    refine measurable_of_tendsto_metrizable
      (f := fun (n : ℕ) t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t)) (fun n => ?_) ?_
    · have hc : Continuous fun t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t) :=
        (continuous_const_smul (h n)⁻¹).comp
          (show Continuous fun t => ζ (z₀ + h n) t - ζ z₀ t from
            (hcont _ (hsub (hhs n))).sub (hcont _ hz₀'))
      exact hc.measurable
    · rw [tendsto_pi_nhds]
      intro t
      exact (hasDerivAt_iff_tendsto_slope_zero.mp (hdiff t z₀ hz₀')).comp hlim
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ)
    (F := fun z κ => ζ z κ • r κ) (F' := fun z κ => deriv (ζ · κ) z • r κ) (x₀ := z₀)
    (s := ball z₀ ε) (bound := fun _ => B / ε * R)
    (ball_mem_nhds z₀ hε0)
    (by
      filter_upwards [hopen.mem_nhds hz₀] with z hz using hmeasF z hz)
    (by
      refine Integrable.of_bound (hmeasF z₀ hz₀') (B * R) (Eventually.of_forall fun t => ?_)
      rw [norm_smul]
      have h1 := hbd z₀ (mem_closedBall_self (by positivity)) t
      have h0 : 0 ≤ B := (norm_nonneg _).trans h1
      exact mul_le_mul h1 (hR' t) (norm_nonneg _) h0)
    (hd0.aestronglyMeasurable.smul hr.aestronglyMeasurable)
    (Eventually.of_forall fun t z hz => by
      have hz' : dist z z₀ < ε := hz
      have hsph : closedBall z ε ⊆ closedBall z₀ (2 * ε) := by
        intro w hw
        have h1 : dist w z ≤ ε := hw
        have h2 := dist_triangle w z z₀
        show dist w z₀ ≤ 2 * ε
        linarith
      have hder : ‖deriv (ζ · t) z‖ ≤ B / ε :=
        Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε0
          (((hζ.hol t).mono hsub).mono hsph |>.diffContOnCl_ball subset_rfl)
          (fun w hw => hbd w (hsph (sphere_subset_closedBall hw)) t)
      rw [norm_smul]
      exact mul_le_mul hder (hR' t) (norm_nonneg _) ((norm_nonneg _).trans hder))
    (integrable_const _)
    (Eventually.of_forall fun t z hz => by
      have hz' : z ∈ closedBall z₀ (2 * ε) := by
        have : dist z z₀ < ε := hz
        show dist z z₀ ≤ 2 * ε
        linarith
      exact (hdiff t z (hsub hz')).smul_const (r t))
  exact hmain.2.differentiableAt.differentiableWithinAt

theorem bGood : BGood := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP ζ hζ
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  haveI : ProperSpace (W →L[ℂ] W) := FiniteDimensional.proper ℂ _
  haveI : IsProbabilityMeasure μ := hP
  obtain ⟨R, hR⟩ := (isCompact_univ (X := K)).exists_bound_of_continuousOn hρ.continuousOn
  refine leftGood_of (A := fun z => avg μ ρ (ζ z)) (differentiableOn_integral μ hρ hζ) ?_
  intro b c hc
  obtain ⟨M, hM⟩ := hζ.strip b c hc
  refine ⟨|M| * |R|, fun z h1 h2 => ?_⟩
  have hpt : ∀ κ : K, ‖ζ z κ • ρ κ‖ ≤ |M| * |R| * (1 + ‖z‖) ^ 2 := by
    intro κ
    rw [norm_smul]
    have h3 : ‖ζ z κ‖ ≤ |M| * (1 + ‖z‖) ^ 2 :=
      (hM z h1 h2 κ).trans (by gcongr; exact le_abs_self M)
    have h4 : ‖ρ κ‖ ≤ |R| := (hR κ (Set.mem_univ κ)).trans (le_abs_self R)
    calc ‖ζ z κ‖ * ‖ρ κ‖ ≤ (|M| * (1 + ‖z‖) ^ 2) * |R| :=
          mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
      _ = |M| * |R| * (1 + ‖z‖) ^ 2 := by ring
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpt)
  simpa [avg] using this

end GlobalTheory.CompanionTheory.RgEisLeft
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGoodStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_term_good : BGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisLeft.bGood | exact GlobalTheory.CompanionTheory.RgEisLeft.bGood | (intros; apply GlobalTheory.CompanionTheory.RgEisLeft.bGood <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembership
open MeasureTheory PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMirGen

theorem avgMem : AvgMem := by
  unfold AvgMem ForRep
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar _ _Γ P c _ φ hφ hLaw w
  haveI := hHaar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  change ∀ r : K, (r : G) ∈ P → c r • ρ r (avg μ ρ φ w) = avg μ ρ φ w
  intro r hr
  have hcont : Continuous fun κ : K => φ κ • ρ κ := hφ.smul hρ
  have hint : Integrable (fun κ : K => φ κ • ρ κ) μ :=
    hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
  have key : avg μ ρ φ = c r • (ρ r).comp (avg μ ρ φ) := by
    show ∫ κ, φ κ • ρ κ ∂μ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ)
    calc ∫ κ, φ κ • ρ κ ∂μ = ∫ κ, φ (r * κ) • ρ (r * κ) ∂μ :=
          (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) r).symm
      _ = ∫ κ, c r • (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := by
          congr 1
          funext κ
          rw [hLaw r κ hr, map_mul]
          ext x
          simp [mul_smul]
      _ = c r • ∫ κ, (ContinuousLinearMap.compL ℂ W W W (ρ r)) (φ κ • ρ κ) ∂μ := integral_smul _ _
      _ = c r • (ρ r).comp (∫ κ, φ κ • ρ κ ∂μ) := by
          rw [(ContinuousLinearMap.compL ℂ W W W (ρ r)).integral_comp_comm hint]
          rfl
  have hw := congrArg (fun T : W →L[ℂ] W => T w) key
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply] at hw
  exact hw.symm

end GlobalTheory.CompanionTheory.EisMirGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembershipStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_membership : AvgMem := by
  first | exact @GlobalTheory.CompanionTheory.EisMirGen.avgMem | exact GlobalTheory.CompanionTheory.EisMirGen.avgMem | (intros; apply GlobalTheory.CompanionTheory.EisMirGen.avgMem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOne
noncomputable section

open NumberField Matrix MeasureTheory
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.EisMG

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

variable {k : Type} [Field k] [NumberField k]

theorem lineZeta_ratV_unit (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ)
    (ξ : Unit → k) (hξ : ξ ≠ 0) : lineZeta Ψ₁ ω z (ratV ξ) = tate Ψ₁ ω z := by
  have h0 : ξ () ≠ 0 := fun h => hξ (funext fun i => by cases i; exact h)
  haveI := isHaarMeasure_ideleMeasure k
  haveI := IdeleGroup.borelSpace k
  have key := integral_mul_left_eq_self (μ := ideleMeasure k)
    (fun x : IdeleGroup k => Ψ₁ (fun _ => (x : 𝔸[k])) * ((ω.toIdele x : Circle) : ℂ) *
      ((((IdeleGroup.ideleModule k x : {r : ℝ // 0 < r}) : ℝ) : ℂ) ^ z))
    (IdeleGroup.diagonal k (Units.mk0 (ξ ()) h0))
  refine Eq.trans ?_ key
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : ((x : 𝔸[k]) • ratV ξ) =
      fun _ => ((IdeleGroup.diagonal k (Units.mk0 (ξ ()) h0) * x : IdeleGroup k) : 𝔸[k]) := by
    funext i
    cases i
    simp [ratV, IdeleGroup.diagonal, mul_comm]
  simp only [hx, map_mul, HeckeCharacter.toIdele_diagonal, IdeleGroup.ideleModule_diagonal, one_mul]

theorem proj_unit_eq (l l' : Projectivization k (Unit → k)) : l = l' := by
  induction l using Projectivization.ind
  rename_i v hv
  induction l' using Projectivization.ind
  rename_i w hw
  rw [Projectivization.mk_eq_mk_iff']
  have hw0 : w () ≠ 0 := fun h => hw (funext fun i => by cases i; exact h)
  exact ⟨v () / w (), funext fun i => by cases i; simp [div_mul_cancel₀ _ hw0]⟩

theorem epstein_unit_one (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ) :
    epstein Ψ₁ ω z 1 = tate Ψ₁ ω z := by
  have hne : (fun _ : Unit => (1 : k)) ≠ 0 := fun h => one_ne_zero (congrFun h ())
  unfold epstein
  rw [tsum_eq_single (Projectivization.mk k (fun _ : Unit => (1 : k)) hne)
    (fun b hb => absurd (proj_unit_eq b _) hb)]
  simp only [inv_one, Units.val_one, Matrix.one_mulVec]
  exact lineZeta_ratV_unit Ψ₁ ω z _ (Projectivization.rep_nonzero _)

theorem zetaOne_of_epMain : EpMain → ZetaOne := by
  intro h
  unfold EpMain at h
  unfold ZetaOne
  intro k _ _ Ψ₁ ω hΨ hω
  obtain ⟨V, -, hV⟩ := h k
  obtain ⟨F, F', hF, -, -, -⟩ := hV Unit Ψ₁ ω hΨ hω
  refine ⟨fun z => F z 1, ?_, fun z hz => ?_⟩
  · unfold PolyEnt
    refine ⟨hF.entire 1, fun b c => ?_⟩
    obtain ⟨M, hM⟩ := hF.strip b c {1} isCompact_singleton
    exact ⟨M, fun z h1 h2 => hM z h1 h2 1 rfl⟩
  · show F z 1 = _
    rw [hF.eq z (by simpa using hz) 1, epstein_unit_one]
    simp

end GlobalTheory.CompanionTheory.EisMG
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOneStatement
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_value_at_one : EpMain → ZetaOne := by
  first | exact @GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain | exact GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain | (intros; apply GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain <;> assumption)
end
end

namespace PositivityTheory.RgEis.MG

theorem mirGen : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen :=
  fun hS hG hB hC hM hT hSph =>
    have hO := GlobalTheory.T.side_term_identity hG hB
    have hZ := GlobalTheory.T.zeta_integral_of_epstein_conv hC
    GlobalTheory.T.mirabolic_generation hS hSph GlobalTheory.T.average_membership (GlobalTheory.T.average_invariance GlobalTheory.T.average_membership) hO (GlobalTheory.T.test_function_spherical_K hG hB hT)
      (GlobalTheory.T.principal_identity_assembly hM GlobalTheory.T.diagonal_term_good (GlobalTheory.T.master_identity GlobalTheory.T.average_membership GlobalTheory.T.diagonal_term_good GlobalTheory.T.height_term_good GlobalTheory.T.boundary_term_good) hO GlobalTheory.T.block_term_identity hZ
        (GlobalTheory.T.side_term_unfolding hC (GlobalTheory.T.unfolding_of_average hS GlobalTheory.T.average_membership) GlobalTheory.T.lines_decomposition GlobalTheory.T.block_term_identity hZ) (GlobalTheory.T.side_term_convergence hC hSph GlobalTheory.T.lines_decomposition GlobalTheory.T.block_term_identity) (GlobalTheory.T.zeta_value_at_one hM))

end PositivityTheory.RgEis.MG
