module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.HdFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFormal
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.zigFormal :
    ZigFormal := by
  intro Γ V S I _ _ _ _ d G
  refine ⟨fun q k u u' c h hz => ?_, fun ι hι q => ?_⟩
  · cases q with
    | zero => exact fun x hx => (h x hx).symm.trans (hz x hx)
    | succ q =>
      obtain ⟨b, hb, hdb, hz⟩ := hz
      exact ⟨b, hb, fun x hx => (hdb x hx).trans (h x hx), hz⟩
  · induction q with
    | zero => exact fun k u c hz x hx => hz (x.map ι) (by rw [List.length_map, hx])
    | succ q ih =>
      rintro k u c ⟨b, hb, hdb, hz⟩
      refine ⟨fun x => b (x.map ι), fun γ x hx => ?_, fun x hx => hdb (x.map ι) (by rw [List.length_map, hx]), ?_⟩
      · have h := hb γ (x.map ι) (by rw [List.length_map, hx])
        refine Eq.trans ?_ h
        simp only [List.map_map]
        congr 2
        funext δ
        exact hι γ δ
      · have h := ih (k + 1) _ c hz
        have e : (fun x : List Γ => UpperTheory.V.Lit.Geo.hd b (x.map ι)) = UpperTheory.V.Lit.Geo.hd (fun x : List Γ => b (x.map ι)) :=
          funext fun x => (hdFacts.2.2.1 I Γ _ ι b x).symm
        rw [e] at h
        exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFwd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.FwdStep
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.RelPrim
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.RelPoin
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

theorem UpperTheory.V.Cj.A.relPoin :
    RelPoin := by
  intro V F _ _ _ _ _ _ Y C hY hconv hC hCY q w hw hd hwC
  rcases C.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀C⟩
  · obtain ⟨η, h1, h2⟩ := poincare V F Y hY hconv q w hw hd
    exact ⟨η, h1, h2, fun p hp => hp.elim⟩
  have hp₀ : p₀ ∈ Y := hCY hp₀C
  have hseg : ContDiff ℝ ∞ (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) := by fun_prop
  set U : Set (V × ℝ) := (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) ⁻¹' Y with hU
  have hUo : IsOpen U := hY.preimage hseg.continuous
  have hmem : ∀ p ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, p₀ + t • (p - p₀) ∈ Y :=
    fun p hp t ht => hconv.add_smul_sub_mem hp₀ hp ht
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p₀ + z.2 • (z.1 - p₀))).curryLeft (z.1 - p₀)
  have hΦ : ContDiffOn ℝ ∞ Φ U := by
    have h1 : ContDiffOn ℝ ∞ (fun z : V × ℝ => w (p₀ + z.2 • (z.1 - p₀))) U :=
      hw.comp hseg.contDiffOn fun z hz => hz
    have h2 : ContDiffOn ℝ ∞ (fun z : V × ℝ => (w (p₀ + z.2 • (z.1 - p₀))).curryLeft) U :=
      (curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap.contDiff.comp_contDiffOn h1
    exact (contDiff_snd.pow q).contDiffOn.smul
      (h2.clm_apply (contDiff_fst.sub contDiff_const).contDiffOn)
  refine ⟨fun p => ∫ t in (0 : ℝ)..1, Φ (p, t),
    paramSmooth V _ Y U Φ hY hUo (fun z hz => hmem z.1 hz.1 z.2 hz.2) hΦ, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨hc, hD⟩ := paramDeriv V _ p U Φ hUo (hmem p hp) hΦ
    have hI := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
    have hI' := ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p₀ + r • (p - p₀)))
        (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => Φ (x, t)) p)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hm := hmem p hp t ht
      exact poinPt V F q w p₀ p t
        ((hw.contDiffAt (hY.mem_nhds hm)).differentiableAt (by simp)) (hd _ hm)
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI'
    rw [(alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hI, ← hD.fderiv] at h3
    refine Eq.trans h3 ?_
    simp
  · have h0 : ∀ t ∈ uIcc (0 : ℝ) 1, Φ (p, t) = (fun _ => 0) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hz : w (p₀ + t • (p - p₀)) = 0 := hwC _ (hC.add_smul_sub_mem hp₀C hp ht)
      show t ^ q • (w (p₀ + t • (p - p₀))).curryLeft (p - p₀) = 0
      rw [hz]
      ext v
      simp
    show ∫ t in (0 : ℝ)..1, Φ (p, t) = 0
    rw [intervalIntegral.integral_congr h0]
    simp
end

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.relPrim :
    RelPrim := by
  intro Γ V S _ _ _ _ d G hc C hC q w hw hv
  have h0 : ∀ s, ∀ p ∈ G.Y, extDeriv (w.1 s) p = 0 := fun s p hp => by
    rw [← G.dOm_apply w s hp, hw]; rfl
  choose η hη hd hz using fun s =>
    relPoin V (Fin d → ℂ) G.Y (C s) G.isOpen hc (hC s).1 (hC s).2 q (w.1 s) (w.2 s).1 (h0 s) (hv s)
  refine ⟨⟨fun s => G.Y.indicator (η s), fun s =>
    ⟨(hη s).congr fun p hp => Set.indicator_of_mem hp _,
      fun p hp => Set.indicator_of_notMem hp _⟩⟩, ?_, ?_⟩
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · rw [G.dOm_apply _ s hp, ← hd s p hp]
      refine Filter.EventuallyEq.extDeriv_eq ?_
      filter_upwards [G.isOpen.mem_nhds hp] with x hx using Set.indicator_of_mem hx _
    · rw [((G.dOm q _).2 s).2 p hp, (w.2 s).2 p hp]
  · intro s p hp
    exact (Set.indicator_of_mem ((hC s).2 hp) _).trans (hz s p hp)
end

open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.fwdStep :
    FwdStep := by
  intro Γ V S I _ _ _ _ _ d G hY r hr C hC q k u hu hcl hvan
  classical
  have hex : ∀ y : List I, y.length = k + 1 → ∃ η : G.Om q, G.dOm q η = u y ∧
      ∀ s, ∀ p ∈ {p | ∀ i ∈ y, p ∈ C i s}, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := by
    intro y hy
    obtain ⟨i0, t, rfl⟩ : ∃ i t, y = i :: t := by
      cases y with
      | nil => simp at hy
      | cons i t => exact ⟨i, t, rfl⟩
    refine relPrim Γ V S d G hY (fun s => {p | ∀ i ∈ i0 :: t, p ∈ C i s}) (fun s => ⟨?_, ?_⟩) q
      (u (i0 :: t)) (hcl _ hy) ?_
    · intro a ha b hb t1 t2 h1 h2 h i hi
      exact hC.convex i s (ha i hi) (hb i hi) h1 h2 h
    · intro p hp
      exact hC.sub i0 s (hp i0 List.mem_cons_self)
    · intro s p hp
      exact hvan _ hy s p (Set.mem_univ _) hp
  choose η hη using hex
  have hηc : ∀ (y y' : List I) (h : y.length = k + 1) (h' : y'.length = k + 1), y = y' → η y h = η y' h' := by
    rintro y _ h h' rfl
    rfl
  let g : List I → Γ := fun x => (x.head?.map r).getD 1
  have hg : ∀ (γ : Γ) (x : List I), x ≠ [] → g (x.map (γ • ·)) = γ * g x := by
    intro γ x hx
    cases x with
    | nil => exact absurd rfl hx
    | cons i t => simp [g, hr]
  have hlen : ∀ x : List I, (x.map ((g x)⁻¹ • ·)).length = x.length := fun x => List.length_map ..
  refine ⟨fun x => if h : x.length = k + 1 then
      G.act q (g x) (η (x.map ((g x)⁻¹ • ·)) ((hlen x).trans h)) else 0, ?_, ?_, ?_⟩
  · intro γ x hx
    have hx' : (x.map (γ • ·)).length = k + 1 := by simpa using hx
    have hne : x ≠ [] := by
      rintro rfl
      simp at hx
    simp only [dif_pos hx, dif_pos hx']
    have hn : (x.map (γ • ·)).map ((g (x.map (γ • ·)))⁻¹ • ·) = x.map ((g x)⁻¹ • ·) := by
      rw [hg γ x hne, List.map_map]
      congr 1
      funext i
      simp [smul_smul]
    rw [hηc _ _ _ ((hlen x).trans hx) hn, hg γ x hne, map_mul]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    rw [UpperTheory.V.Lit.Dr.dEquiv Γ V S d G q, (hη _ _).1, ← hu (g x) _ ((hlen x).trans hx)]
    congr 1
    simp [List.map_map, Function.comp_def, smul_smul]
  · intro x hx s p _ hp
    simp only [dif_pos hx]
    have hp' : G.ρ (g x)⁻¹ p ∈ {p | ∀ i ∈ x.map ((g x)⁻¹ • ·), p ∈ C i ((G.σ (g x)⁻¹) s)} := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      exact (hC.equiv _ j s p).2 (hp j hj)
    ext v
    rw [UpperTheory.V.Lit.Dr.Geo.act_apply, (hη _ _).2 _ _ hp']
    simp
end

open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.zigFwd :
    ZigFwd := by
  intro Γ V S I _ _ _ _ _ d G hc hne r hr C hC q
  obtain ⟨hdd, -, -, hmap, hloc, heq⟩ := hdFacts
  obtain ⟨hact, hinj, hex⟩ := inclFacts Γ V S d G hc hne
  induction q with
  | zero =>
    intro k n hn u hu hd0 hh hv
    obtain rfl : k = n := by simpa using hn
    have key : ∀ x : List I, ∃ f, x.length = k + 1 → u x = G.incl f := fun x => by
      by_cases hx : x.length = k + 1
      · obtain ⟨f, hf⟩ := (hex (u x)).1 (hd0 x hx)
        exact ⟨f, fun _ => hf.symm⟩
      · exact ⟨0, fun h => absurd h hx⟩
    choose c hcu using key
    refine ⟨c, hcu, fun γ x hx => hinj ?_, fun x hx => hinj ?_, fun x hx s p hp => ?_⟩
    · rw [hact, ← hcu x hx, ← hcu _ (by simpa using hx), hu γ x hx]
    · have h1 := hmap I _ _ G.incl.toAddMonoidHom c x
      have h2 := hloc I _ (fun y => G.incl.toAddMonoidHom (c y)) u x
        (fun y hy _ => (hcu y (by omega)).symm)
      rw [map_zero, ← hh x hx, ← h2, h1]
      rfl
    · obtain ⟨i, hi⟩ := List.exists_mem_of_length_eq_add_one hx
      have hY : p ∈ G.Y := hC.sub i s (hp i hi)
      rw [← G.incl_apply (c x) s hY Fin.elim0, ← hcu x hx, hv x hx s p trivial hp]
      rfl
  | succ q ih =>
    intro k n hn u hu hd0 hh hv
    obtain ⟨b, hb, hdb, hvb⟩ := fwdStep Γ V S I d G hc r hr C hC q k u hu hd0 hv
    obtain ⟨c, hz, hrest⟩ := ih (k + 1) n (by omega) (hd b) (heq Γ I _ (G.act q) k b hb)
      (fun x hx => by
        have h1 := hmap I _ _ (G.dOm q).toAddMonoidHom b x
        have h2 := hloc I _ (fun y => (G.dOm q).toAddMonoidHom (b y)) u x
          (fun y hy _ => hdb y (by omega))
        rw [← hh x hx, ← h2, h1]
        rfl)
      (fun x _ => hdd I _ b x)
      (fun x hx s p _ hp => by
        let ev : G.Om q →+ (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
          { toFun := fun w => w.1 s p, map_zero' := rfl, map_add' := fun _ _ => rfl }
        have h1 := hmap I _ _ ev b x
        have h2 := hloc I _ (fun y => ev (b y)) (fun y => ev ((fun _ => (0 : G.Om q)) y)) x
          (fun y hy hyx => hvb y (by omega) s p trivial fun i hi => hp i (hyx i hi))
        change ev (hd b x) = 0
        rw [← h1, h2]
        simp [hd])
    exact ⟨c, ⟨b, hb, hdb, hz⟩, hrest⟩
end
