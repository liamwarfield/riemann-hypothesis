module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DcAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DetRoot
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eq_one_of_cong {L : Type} [Field L] [NumberField L] [IsCMField L] (m : ℕ) (hm : 3 ≤ m) (δ : L)
    (hδ : δ * IsCMField.complexConj L δ = 1)
    (h : ∀ w : HeightOneSpectrum (𝓞 L), ∃ a ∈ w.adicCompletionIntegers L,
      algebraMap L (w.adicCompletion L) δ - 1 = (m : w.adicCompletion L) * a) : δ = 1 := by
  have hm0 : (m : L) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  have hx : ∀ v : HeightOneSpectrum (𝓞 L), v.valuation L ((δ - 1) / m) ≤ 1 := by
    intro v
    obtain ⟨a, ha, e⟩ := h v
    have hma : (m : v.adicCompletion L) = algebraMap L (v.adicCompletion L) (m : L) := by simp
    have hm0' : (m : v.adicCompletion L) ≠ 0 := by
      rw [hma]
      exact (map_ne_zero _).2 hm0
    have hxa : algebraMap L (v.adicCompletion L) ((δ - 1) / m) = a := by
      rw [map_div₀, map_sub, map_one, e, ← hma]
      field_simp
    have hval : Valued.v (algebraMap L (v.adicCompletion L) ((δ - 1) / m)) = v.valuation L ((δ - 1) / m) :=
      v.valuedAdicCompletion_eq_valuation' _
    rw [← hval, hxa]
    exact ha
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one L _ hx
  by_contra hne
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    have : δ - 1 = 0 := by
      have := hy.symm
      rwa [div_eq_zero_iff, or_iff_left hm0] at this
    exact hne (sub_eq_zero.1 this)
  have hlt : ∀ z : InfinitePlace L, z ((y : 𝓞 L) : L) < 1 := by
    intro z
    have hyx : ((y : 𝓞 L) : L) = (δ - 1) / m := hy
    have hn : ‖z.embedding δ‖ = 1 := by
      have e1 : z.embedding δ * (starRingEnd ℂ) (z.embedding δ) = 1 := by
        rw [← IsCMField.complexEmbedding_complexConj, ← map_mul, hδ, map_one]
      have e2 := congrArg norm e1
      rw [norm_mul, Complex.norm_conj, norm_one] at e2
      nlinarith [norm_nonneg (z.embedding δ)]
    rw [← InfinitePlace.norm_embedding_eq, hyx, map_div₀, map_sub, map_one, map_natCast, norm_div,
      Complex.norm_natCast]
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_lt_one (by linarith)]
    have := norm_sub_le (z.embedding δ) 1
    rw [hn, norm_one] at this
    linarith
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace L) := inferInstance
  have := InfinitePlace.one_le_of_lt_one (w := w₀) hy0 (fun z _ => hlt z)
  linarith [hlt w₀]

private theorem det_cong {L : Type} [Field L] [NumberField L] [IsCMField L] {m : ℕ} {w : HeightOneSpectrum (𝓞 L)}
    (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion L))
    (h : ∀ i j, ∃ a ∈ w.adicCompletionIntegers L, (M - 1) i j = (m : w.adicCompletion L) * a) :
    ∃ a ∈ w.adicCompletionIntegers L, M.det - 1 = (m : w.adicCompletion L) * a := by
  obtain ⟨a, ha, ea⟩ := h 0 0
  obtain ⟨b, hb, eb⟩ := h 0 1
  obtain ⟨c, hc, ec⟩ := h 1 0
  obtain ⟨d, hd, ed⟩ := h 1 1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at ea eb ec ed
  have hmO : (m : w.adicCompletion L) ∈ w.adicCompletionIntegers L := natCast_mem _ m
  refine ⟨a + d + m * (a * d - b * c), add_mem (add_mem ha hd) (mul_mem hmO (sub_mem (mul_mem ha hd) (mul_mem hb hc))), ?_⟩
  have e0 : M 0 0 = 1 + m * a := by rw [← ea]; ring
  have e3 : M 1 1 = 1 + m * d := by rw [← ed]; ring
  rw [Matrix.det_fin_two, e0, e3, eb, ec]
  ring

theorem UpperTheory.V.Z.Sym.So.detRoot :
    UpperTheory.V.Z.Sym.So.DetRoot := by
  intro L _ _ _ m hm U hU f hf k hk hr u hu hfu
  obtain ⟨γ₀, hγ₀'⟩ := hr
  have hγ₀ : ratGL L 2 γ₀ = ((f * k : UA L 2) : GA L 2) := hγ₀'
  have hg : Formalism.UG.cT (conjAd L) ((f * k : UA L 2) : GA L 2).val * 1 * ((f * k : UA L 2) : GA L 2).val = 1 := (f * k).2
  rw [← hγ₀, mul_one] at hg
  have hv : (ratGL L 2 γ₀).val = γ₀.val.map (algebraMap L (Ad L)) := rfl
  rw [hv, GlobalTheory.DefU.ClassFin.cT_map (algebraMap L (Ad L)) (IsCMField.complexConj L).toRingEquiv.toRingHom (conjAd L)
    (fun y => (conjAd_algebraMap y).symm), ← Matrix.map_mul] at hg
  haveI hnt : Nontrivial (Ad L) := show Nontrivial (InfiniteAdeleRing L × FiniteAdeleRing (𝓞 L) L) from inferInstance
  have hUL : Formalism.UG.cT (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val * γ₀.val = 1 := by
    ext i j
    have := congrFun₂ hg i j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    apply (algebraMap L (Ad L)).injective
    rw [this]
    split_ifs <;> simp
  have hδ : γ₀.val.det * IsCMField.complexConj L γ₀.val.det = 1 := by
    have := congrArg Matrix.det hUL
    rw [Matrix.det_mul, Matrix.det_one] at this
    have hc : (Formalism.UG.cT (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val).det = IsCMField.complexConj L γ₀.val.det := by
      simp only [Formalism.UG.cT, Matrix.det_transpose]
      exact (RingHom.map_det (IsCMField.complexConj L).toRingEquiv.toRingHom γ₀.val).symm
    rw [hc] at this
    rw [mul_comm]
    exact this
  have hD : (f : GA L 2).val.det * (k : GA L 2).val.det = algebraMap L (Ad L) γ₀.val.det := by
    rw [RingHom.map_det]
    have h2 : (γ₀.val.map (algebraMap L (Ad L))) = ((f * k : UA L 2) : GA L 2).val := by rw [← hv, hγ₀]
    change _ = (γ₀.val.map (algebraMap L (Ad L))).det
    rw [h2, ← Matrix.det_mul]
    rfl
  have hkF : pFin L (k : GA L 2).val.det = 1 := by
    have hk' : Matrix.GeneralLinearGroup.map (pFin L) (k : GA L 2) = 1 := hk
    rw [RingHom.map_det]
    have := congrArg (fun g : GL (Fin 2) (Af L) => g.val.det) hk'
    simpa using this
  have hfI : pInf L (f : GA L 2).val.det = 1 := by
    have hf' : Matrix.GeneralLinearGroup.map (pInf L) (f : GA L 2) = 1 := hf
    rw [RingHom.map_det]
    have := congrArg (fun g : GL (Fin 2) (Cinf L) => g.val.det) hf'
    simpa using this
  have hdu : (f : GA L 2).val.det * (u : GA L 2).val.det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det ((f * u : UA L 2) : GA L 2) = 1 := hfu
    have := congrArg Units.val h1
    simpa using this
  have huv : (u : GA L 2).val.det * ((u⁻¹ : UA L 2) : GA L 2).val.det = 1 := by
    rw [← Matrix.det_mul]
    have : (u : GA L 2).val * ((u⁻¹ : UA L 2) : GA L 2).val = 1 := by
      have := congrArg (fun x : UA L 2 => (x : GA L 2).val) (mul_inv_cancel u)
      simpa using this
    rw [this, Matrix.det_one]
  have hfv : (f : GA L 2).val.det = ((u⁻¹ : UA L 2) : GA L 2).val.det := by
    calc _ = (f : GA L 2).val.det * ((u : GA L 2).val.det * ((u⁻¹ : UA L 2) : GA L 2).val.det) := by rw [huv, mul_one]
      _ = _ := by rw [← mul_assoc, hdu, one_mul]
  have hcong : ∀ w : HeightOneSpectrum (𝓞 L), ∃ a ∈ w.adicCompletionIntegers L,
      algebraMap L (w.adicCompletion L) γ₀.val.det - 1 = (m : w.adicCompletion L) * a := by
    intro w
    have hmem := ((hU (u⁻¹)).1 (U.inv_mem hu)).2 w
    obtain ⟨a, ha, e⟩ := det_cong (mL w (u⁻¹ : UA L 2)) hmem
    refine ⟨a, ha, ?_⟩
    rw [← e]
    have e1 : (mL w (u⁻¹ : UA L 2)).det = pLoc L w (pFin L ((u⁻¹ : UA L 2) : GA L 2).val.det) := by
      rw [← RingHom.comp_apply, RingHom.map_det]
      rfl
    have e2 : algebraMap L (w.adicCompletion L) γ₀.val.det = pLoc L w (pFin L (algebraMap L (Ad L) γ₀.val.det)) := rfl
    rw [e1, e2, ← hD, hfv, map_mul, hkF, mul_one]
  have h1 : γ₀.val.det = 1 := eq_one_of_cong m hm _ hδ hcong
  rw [h1, map_one] at hD
  have hfF : pFin L (f : GA L 2).val.det = 1 := by
    have := congrArg (pFin L) hD
    rwa [map_mul, hkF, mul_one, map_one] at this
  have hf1 : (f : GA L 2).val.det = 1 := by
    refine Prod.ext ?_ hfF
    apply (infEq L).symm.injective
    have e : (infEq L).symm ((1 : Ad L).1) = 1 := map_one _
    exact hfI.trans e.symm
  have hk1 : (k : GA L 2).val.det = 1 := by rwa [hf1, one_mul] at hD
  refine ⟨?_, ?_⟩
  · refine MonoidHom.mem_ker.2 (Units.ext ?_)
    exact hf1
  · refine MonoidHom.mem_ker.2 (Units.ext ?_)
    exact hk1

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ProdEig
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

section Grp

variable {G H : Type} [Group G] [Group H]

private theorem finOrb_one (U : Subgroup G) : AlgebraTools.FinOrb U U (1 : G) := by
  refine Set.Finite.subset (Set.finite_singleton ((1 : G) : G ⧸ U)) ?_
  rintro _ ⟨u, rfl⟩
  refine Set.mem_singleton_iff.2 ?_
  change (((u : G) * 1 : G) : G ⧸ U) = ((1 : G) : G ⧸ U)
  exact QuotientGroup.eq.2 (by simpa using U.inv_mem u.2)

private theorem finOrb_mul (U : Subgroup G) {a b : G} (ha : AlgebraTools.FinOrb U U a) (hb : AlgebraTools.FinOrb U U b) :
    AlgebraTools.FinOrb U U (a * b) := by
  classical
  refine Set.Finite.subset ((Set.Finite.prod ha hb).image
    (fun q : (G ⧸ U) × (G ⧸ U) => ((q.1.out * q.2.out : G) : G ⧸ U))) ?_
  rintro _ ⟨u, rfl⟩
  obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul U ((u : G) * a)
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul U (((t : G))⁻¹ * b)
  refine ⟨((((u : G) * a : G) : G ⧸ U), ((((t : G))⁻¹ * b : G) : G ⧸ U)), ⟨⟨u, rfl⟩, ⟨t⁻¹, rfl⟩⟩, ?_⟩
  change (((((((u : G) * a : G) : G ⧸ U)).out * ((((t : G))⁻¹ * b : G) : G ⧸ U).out : G)) : G ⧸ U) =
    (((u : G) * (a * b) : G) : G ⧸ U)
  rw [ht, hs]
  have e : (u : G) * a * t * ((t : G)⁻¹ * b * s) = (u : G) * (a * b) * s := by group
  rw [e]
  exact QuotientGroup.mk_mul_of_mem _ s.2

private theorem uf_split (j : H →* G) (p : G →* H) (U : Subgroup G) (hpj : ∀ h, p (j h) = h)
    (hU : ∀ u ∈ U, j (p u) ∈ U) (hC : ∀ u ∈ U, ∀ h, (j (p u))⁻¹ * u * j h = j h * ((j (p u))⁻¹ * u))
    (d : H) (b : G) (hb : ∀ h, b * j h = j h * b) (hpb : p b = 1) : UF U (j d) b := by
  have hv : ∀ u ∈ U, (j (p u))⁻¹ * u ∈ U := fun u hu => U.mul_mem (U.inv_mem (hU u hu)) hu

  have hA : ∀ y ∈ DC U (j d), (j (p y))⁻¹ * y ∈ U := by
    rintro y ⟨u, hu, u', hu', rfl⟩
    have e : (j (p (u * j d * u')))⁻¹ * (u * j d * u') =
        (j (p u'))⁻¹ * ((j d)⁻¹ * (((j (p u))⁻¹ * u) * j d)) * u' := by
      simp only [map_mul, hpj]
      group
    rw [e, hC u hu d, inv_mul_cancel_left]
    exact U.mul_mem (U.mul_mem (U.inv_mem (hU u' hu')) (hv u hu)) hu'
  have hB : ∀ y ∈ DC U b, ∃ m ∈ U, p y = p m := by
    rintro y ⟨u, hu, u', hu', rfl⟩
    exact ⟨u * u', U.mul_mem hu hu', by simp [hpb]⟩
  have key : ∀ g y₁ y₂, y₁ ∈ DC U (j d) → y₂ ∈ DC U (j d) → y₁⁻¹ * g ∈ DC U b → y₂⁻¹ * g ∈ DC U b → y₂⁻¹ * y₁ ∈ U := by
    intro g y₁ y₂ h₁ h₂ k₁ k₂
    obtain ⟨m₁, hm₁, e₁⟩ := hB _ k₁
    obtain ⟨m₂, hm₂, e₂⟩ := hB _ k₂
    have e : p (y₂⁻¹ * y₁) = p (m₂ * m₁⁻¹) := by
      have : y₂⁻¹ * y₁ = (y₂⁻¹ * g) * (y₁⁻¹ * g)⁻¹ := by group
      rw [this, map_mul, map_inv, e₁, e₂, map_mul, map_inv]
    have e' : y₂⁻¹ * y₁ = ((j (p y₂))⁻¹ * y₂)⁻¹ * j (p (m₂ * m₁⁻¹)) * ((j (p y₁))⁻¹ * y₁) := by
      rw [← e]
      simp only [map_mul, map_inv]
      group
    rw [e']
    exact U.mul_mem (U.mul_mem (U.inv_mem (hA _ h₂)) (hU _ (U.mul_mem hm₂ (U.inv_mem hm₁)))) (hA _ h₁)
  intro g
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu, u', hu', rfl⟩
    obtain ⟨t, ht⟩ := QuotientGroup.mk_out_eq_mul U (u * j d)
    have h₁ : (((u * j d : G) : G ⧸ U)).out ∈ DC U (j d) := by
      rw [ht]
      exact ⟨u, hu, t, t.2, rfl⟩
    have h₂ : (((u * j d : G) : G ⧸ U)).out⁻¹ * (u * (j d * b) * u') ∈ DC U b := by
      rw [ht]
      exact ⟨(t : G)⁻¹, U.inv_mem t.2, u', hu', by group⟩
    refine ⟨((u * j d : G) : G ⧸ U), ⟨h₁, h₂⟩, ?_⟩
    rintro y ⟨k₁, k₂⟩
    have := key _ _ _ k₁ h₁ k₂ h₂
    rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' (((u * j d : G) : G ⧸ U))]
    exact (QuotientGroup.eq.2 this).symm
  · rintro y ⟨u, hu, u', hu', rfl⟩ ⟨s, hs, s', hs', e⟩
    have hg : g = u * j d * (u' * s) * b * s' := by
      have : g = (u * j d * u') * ((u * j d * u')⁻¹ * g) := by group
      rw [this, e]
      group
    have hm : u' * s ∈ U := U.mul_mem hu' hs
    set m := u' * s
    set v := (j (p m))⁻¹ * m with hvd
    have hmv : m = j (p m) * v := by simp [hvd]
    have hcomm : v * j (d * p m) = j (d * p m) * v := hC m hm _
    refine ⟨u * v, U.mul_mem hu (hv m hm), j (p m) * s', U.mul_mem (hU m hm) hs', ?_⟩
    have hbm : b * j (p m) = j (p m) * b := hb _
    calc g = u * (j d * j (p m) * v) * b * s' := by rw [hg, hmv]; simp only [mul_assoc, hvd, mul_inv_cancel_left]
      _ = u * (v * j (d * p m)) * b * s' := by rw [hcomm, map_mul j]
      _ = u * v * j d * (j (p m) * b) * s' := by simp only [map_mul, mul_assoc]
      _ = u * v * (j d * b) * (j (p m) * s') := by rw [← hbm]; simp only [mul_assoc]

end Grp

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.prodEig :
    UpperTheory.V.Z.Sym.So.ProdEig := by
  classical
  intro L _ _ _ n U₀ S VL hS hF d
  obtain ⟨hsec, hcomm, -, -, hext, hfi, hfac, hK⟩ := UpperTheory.V.Z.Sym.Dict.Br.uaFacts L n
  have hloc0 : ∀ (w : Plc L), ∀ y ∈ locU n w, ∀ u : Plc L, un u ≠ un w → cLoc u y = 1 := fun w y hy u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hy).2 u) hu)
  have hlocF : ∀ (w : Plc L), ∀ y ∈ locU n w, y ∈ finU (E := L) (n := n) := fun w y hy => (Subgroup.mem_inf.1 hy).1
  have hne : ∀ w ∈ S, ∀ w' ∈ S, w' ≠ w → un w' ≠ un w := fun w hw w' hw' hww e =>
    hww (hS.inj (by exact_mod_cast hw') (by exact_mod_cast hw) e)

  have hlev : ∀ w ∈ S, ∀ u ∈ lev U₀ S VL, secW n w (cLoc w u) ∈ lev U₀ S VL := by
    intro w hw u hu
    have hsp : IsSplitAt w := hS.split w (by exact_mod_cast hw)
    have hu₀ : u ∈ U₀ := (Subgroup.mem_inf.1 hu).1
    have huJ : ∀ w' ∈ S, cLoc w' u ∈ (VL w').J n := fun w' hw' =>
      Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hu).2 w') hw')
    have huK : cLoc w u ∈ GlobalTheory.LFun.KGL w (n := n) :=
      Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (hF.1 hu₀)).2 w)
    have htl := (hsec w hsp).1 (cLoc w u)
    have htc := (hsec w hsp).2.1 (cLoc w u)
    have htK : secW n w (cLoc w u) ∈ Kall L n := by
      refine Subgroup.mem_inf.2 ⟨hlocF w _ htl, Subgroup.mem_iInf.2 fun w' => Subgroup.mem_comap.2 ?_⟩
      by_cases h : un w' = un w
      · exact hK w hsp _ (by rw [htc]; exact huK) w' h
      · rw [hloc0 w _ htl w' h]
        exact one_mem _
    refine Subgroup.mem_inf.2 ⟨hF.2 w hw (Subgroup.mem_inf.2 ⟨htl, htK⟩), Subgroup.mem_iInf.2 fun w' =>
      Subgroup.mem_iInf.2 fun hw' => Subgroup.mem_comap.2 ?_⟩
    by_cases h : w' = w
    · subst h
      rw [htc]
      exact huJ _ hw'
    · rw [hloc0 w _ htl w' (hne w hw w' hw' h)]
      exact one_mem _
  have hcm : ∀ w ∈ S, ∀ u ∈ lev U₀ S VL, ∀ h, (secW n w (cLoc w u))⁻¹ * u * secW n w h = secW n w h * ((secW n w (cLoc w u))⁻¹ * u) := by
    intro w hw u hu h
    have hsp : IsSplitAt w := hS.split w (by exact_mod_cast hw)
    have hfu : u ∈ finU (E := L) (n := n) := (Subgroup.mem_inf.1 (hF.1 (Subgroup.mem_inf.1 hu).1)).1
    obtain ⟨a, hal, hau⟩ := hfac w u hfu
    have haeq : a = secW n w (cLoc w u) := by
      rw [(hsec w hsp).2.2.2 a hal, hau w rfl]
    refine (hcomm w _ ((hsec w hsp).1 h) _ fun u' hu' => ?_).symm.eq
    rw [map_mul, map_inv, ← haeq, hau u' hu', inv_mul_cancel]
  suffices P : ∀ S' : Finset (Plc L), S' ⊆ S → ∀ x : UA L n, OnS S' x → (∀ w ∈ S', cLoc w x = Sig.dg (d w)) →
      AlgebraTools.FinOrb (lev U₀ S VL) (lev U₀ S VL) x ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (φ : UA L n → V),
        (∀ u ∈ lev U₀ S VL, ∀ g, φ (g * u) = φ g) → ∀ c : Plc L → ℂ, (∀ w ∈ S', EigAt φ w (VL w) (d w) (c w)) →
        dcF (lev U₀ S VL) x φ = (∏ w ∈ S', c w) • φ from
    fun x hx hd => P S subset_rfl x hx hd
  intro S'
  induction S' using Finset.induction_on with
  | empty =>
    intro _ x hx _
    have hx1 : x = 1 := hext x 1 (fun w => by rw [hx.2 w (by simp), map_one])
      (fun τ => by rw [(hfi x).1.1 hx.1 τ, map_one])
    subst hx1
    refine ⟨finOrb_one _, fun V _ _ φ hφ c _ => ?_⟩
    have := (dcBasic _ V _ _ (finOrb_one (lev U₀ S VL)) φ hφ).2.2.2.1 (one_mem _)
    simpa using this
  | insert w S'' hw ih =>
    intro hsub x hx hd
    have hwS : w ∈ S := hsub (Finset.mem_insert_self _ _)
    have hsub' : S'' ⊆ S := fun y hy => hsub (Finset.mem_insert_of_mem hy)
    have hsp : IsSplitAt w := hS.split w (by exact_mod_cast hwS)
    have hdw := hd w (Finset.mem_insert_self _ _)
    obtain ⟨a, hal, hax⟩ := hfac w x hx.1
    have haeq : a = secW n w (Sig.dg (d w)) := by
      rw [(hsec w hsp).2.2.2 a hal, hax w rfl, hdw]
    subst haeq
    set a := secW n w (Sig.dg (d w)) with ha
    set b := a⁻¹ * x with hb
    have hxab : x = a * b := by simp [hb]
    have habove : ∀ u : Plc L, un u = un w → cLoc u b = 1 := fun u hu => by
      rw [hb, map_mul, map_inv, hax u hu, inv_mul_cancel]
    have hbOn : OnS S'' b := by
      refine ⟨mul_mem (inv_mem (hlocF w _ hal)) hx.1, fun u hu => ?_⟩
      by_cases h : un u = un w
      · exact habove u h
      · have h1 : cLoc u x = 1 := hx.2 u fun w' hw' => by
          rcases Finset.mem_insert.1 hw' with rfl | hw'
          · exact h
          · exact hu w' hw'
        rw [hb, map_mul, map_inv, h1, hloc0 w _ hal u h]
        simp
    have hbd : ∀ w' ∈ S'', cLoc w' b = Sig.dg (d w') := fun w' hw' => by
      have hww : w' ≠ w := fun e => hw (e ▸ hw')
      rw [hb, map_mul, map_inv, hloc0 w _ hal w' (hne w hwS w' (hsub' hw') hww), hd w' (Finset.mem_insert_of_mem hw')]
      simp
    obtain ⟨ihF, ihE⟩ := ih hsub' b hbOn hbd
    have hFw : Full U₀ {w} := ⟨hF.1, fun w' hw' => by
      rw [Finset.mem_singleton.1 hw']
      exact hF.2 w hwS⟩
    have hat := dcAt L n U₀ S VL hS w hwS hFw (d w)
    have hUF : UF (lev U₀ S VL) a b :=
      uf_split (secW n w) (cLoc w) (lev U₀ S VL) (hsec w hsp).2.1 (hlev w hwS) (hcm w hwS) (Sig.dg (d w)) b
        (fun h => (hcomm w _ ((hsec w hsp).1 h) b habove).symm.eq) (by
          exact habove w rfl)
    have hFab := finOrb_mul (lev U₀ S VL) hat.1 ihF
    rw [hxab]
    refine ⟨hFab, fun V _ _ φ hφ c hc => ?_⟩
    have hsm : dcF (lev U₀ S VL) a ((∏ w ∈ S'', c w) • φ) = (∏ w ∈ S'', c w) • dcF (lev U₀ S VL) a φ :=
      map_smul (dc (rightReg ℂ (UA L n) V) (lev U₀ S VL) (lev U₀ S VL) a) _ φ
    rw [← uFMul _ V _ a b hat.1 ihF hFab hUF φ hφ, ihE V φ hφ c fun w' hw' => hc w' (Finset.mem_insert_of_mem hw'),
      hsm, (hat.2 V φ hφ (c w)).1 (hc w (Finset.mem_insert_self _ _)), smul_smul, Finset.prod_insert hw, mul_comm]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LevelStep
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finOrb_sub {G : Type} [Group G] (U H : Subgroup G) (x : H)
    (h : UpperTheory.V.AlgebraTools.FinOrb U U (x : G)) : UpperTheory.V.AlgebraTools.FinOrb (U.subgroupOf H) (U.subgroupOf H) x := by
  let f : H ⧸ U.subgroupOf H → G ⧸ U := fun q => Quotient.liftOn' q (fun y => ((y : G) : G ⧸ U)) (by
    intro y z hyz
    have hyz' : y⁻¹ * z ∈ U.subgroupOf H := QuotientGroup.leftRel_apply.1 hyz
    exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hyz'))
  have hf : Function.Injective f := by
    intro q q'
    induction q using QuotientGroup.induction_on with | _ y => ?_
    induction q' using QuotientGroup.induction_on with | _ z => ?_
    intro hyz
    have hyz' : (y : G)⁻¹ * z ∈ U := QuotientGroup.eq.1 hyz
    exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hyz')
  refine Set.Finite.of_finite_image (f := f) (Set.Finite.subset h ?_) hf.injOn
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact ⟨⟨(u.1 : G), u.2⟩, rfl⟩

section
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem fin_uniq (f f' : finU (E := L) (n := 3)) (k k' : UA L 3) (hk : k ∈ infU L 3) (hk' : k' ∈ infU L 3)
    (he : (f : UA L 3) * k = (f' : UA L 3) * k') : f = f' ∧ k = k' := by
  obtain ⟨-, -, -, -, hext, hfi, -, -⟩ := Br.uaFacts L 3
  have hff : (f : UA L 3) = f' := by
    refine hext _ _ (fun w => ?_) (fun τ => ?_)
    · have h1 := congrArg (cLoc w) he
      rw [map_mul, map_mul, ((hfi k).2.1 hk) w, ((hfi k').2.1 hk') w, mul_one, mul_one] at h1
      exact h1
    · rw [((hfi _).1.1 f.2) τ, ((hfi _).1.1 f'.2) τ]
  refine ⟨Subtype.ext hff, ?_⟩
  rw [hff] at he
  exact mul_left_cancel he

private theorem inf_eq (B : Bridge L) (j : ℕ) (γ : U3 B.Δ) (k : UA L 3)
    (hτ : ∀ τ, cEmb τ k = cEmb τ (B.rG γ : UA L 3)) :
    Wt.cG (em B) j γ = Wt.repG _ j (infC L 3 k) := by
  have hinf : infC L 3 k = Wt.infG (em B) 3 (Unitary.toUnits γ) := by
    funext v
    refine Units.ext ?_
    show (cEmb v.embedding k : Matrix (Fin 3) (Fin 3) ℂ) = _
    rw [hτ v.embedding, B.rG_inf]
    rfl
  rw [hinf]
  rfl

private theorem left_step (B : Bridge L) (hB : B.Ok) (A : SD B.Δ) (j : ℕ) (ch : Lp L → ℂ)
    (C : Base (U3 B.Δ) (GA B.Δ) (Wt.VG (InfinitePlace L) j)) (s : C.Tw) (hBG : A.dat.IsBG ch C s)
    (hW : C.W = Wt.cG (em B) j) (ψ : GA B.Δ → Wt.VG (InfinitePlace L) j) (hψ : ψ ∈ C.Forms)
    (f : finU (E := L) (n := 3)) (k : UA L 3) (hk : k ∈ infU L 3) (hfk : (f : UA L 3) * k ∈ ratU L 3) (g : finU (E := L) (n := 3)) :
    ψ (B.bG.symm (f * g)) = Wt.repG _ j (infC L 3 k) (ψ (B.bG.symm g)) := by
  obtain ⟨γ, hγ⟩ : ∃ γ : U3 B.Δ, (B.rG γ : UA L 3) = f * k :=
    ⟨B.rG.symm ⟨_, hfk⟩, by rw [MulEquiv.apply_symm_apply]⟩
  obtain ⟨k', hk', he, hτ⟩ := hB.finG γ (C.ι γ) (fun v => hBG.ι γ v)
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 = C.ι γ := ⟨_, rfl⟩
  rw [← hg0] at he
  obtain ⟨h1, h2⟩ := fin_uniq f (B.bG g0) k k' hk hk' (hγ.symm.trans he)
  subst h2
  rw [h1, map_mul, MulEquiv.symm_apply_apply, hg0, hψ.1, hW, inf_eq B j γ k hτ]

private theorem level_step (B : Bridge L) (A : SD B.Δ) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w))
    (hlG : ∀ g : GA B.Δ, g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall (L := L) 3) S VL) (j : ℕ) (ch : Lp L → ℂ)
    (C : Base (U3 B.Δ) (GA B.Δ) (Wt.VG (InfinitePlace L) j)) (s : C.Tw) (hBG : A.dat.IsBG ch C s)
    (ψ : GA B.Δ → Wt.VG (InfinitePlace L) j) (hψ : ψ ∈ C.Forms)
    (u : finU (E := L) (n := 3)) (hu : (u : UA L 3) ∈ lev (Kall (L := L) 3) S VL) (g : finU (E := L) (n := 3)) :
    ψ (B.bG.symm (g * u)) = ψ (B.bG.symm g) := by
  have hm : B.bG.symm u ∈ C.U := by
    rw [hBG.U, hlG, MulEquiv.apply_symm_apply]
    exact hu
  have h1 := hψ.2 (B.bG.symm g) ⟨_, hm⟩
  rw [map_mul]
  rw [hBG.ω] at h1
  simpa using h1

private def pull {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) :
    Fin 3 → (Kv (un w))ˣ := fun i => Units.map ((T w h).i.symm : Kw w →* Kv (un w)) (d i)

open Classical in
private def ddf {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) :
    ParN (Lp L) 3 := Function.update 1 (un w) (pull T w h d)

private theorem iu_pull {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) (i : Fin 3) :
    iu T w h (pull T w h d i) = d i := by
  refine Units.ext ?_
  simp [pull, iu]

private theorem ddf_self {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) :
    ddf T w h d (un w) = pull T w h d := by
  simp [ddf]

open Classical in
private theorem ddf_ne {B : Bridge L} (T : Spl B) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ)
    {v : Pl (Lp L)} (hv : v ≠ un w) : ddf T w h d v = 1 := by
  simp [ddf, Function.update_of_ne hv]

private theorem is_el {B : Bridge L} (T : Spl B) (S : Finset (Plc L)) (A : SD B.Δ)
    (hEl : ∀ (g : GA B.Δ) d, A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧ ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i))
    (hpl : Places (S : Set (Plc L))) (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ)
    (x : finU (E := L) (n := 3)) (hx : (x : UA L 3) = secW 3 w (Sig.dg d)) : A.IsElG (B.bG.symm x) (ddf T w h d) := by
  obtain ⟨hsec, -⟩ := Br.uaFacts L 3
  have hloc := (hsec w h).1 (Sig.dg d)
  have hc := (hsec w h).2.1 (Sig.dg d)
  rw [← hx] at hloc hc
  have hoff : ∀ u, un u ≠ un w → cLoc u (x : UA L 3) = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hloc.2 u) hu)
  rw [hEl, MulEquiv.apply_symm_apply]
  refine ⟨⟨x.2, fun u hu => hoff u (hu w hw)⟩, fun w' hw' h' => ?_⟩
  by_cases hww : w' = w
  · subst hww
    rw [hc]
    have e : (fun i => iu T w' h' (ddf T w' h d (un w') i)) = d :=
      funext fun i => by rw [ddf_self]; exact iu_pull T w' h d i
    rw [e]
  · have hne : un w' ≠ un w := fun e => hww (hpl.inj (by exact_mod_cast hw') (by exact_mod_cast hw) e)
    rw [hoff w' hne]
    have e : (fun i => iu T w' h' (ddf T w h d (un w') i)) = 1 :=
      funext fun i => by rw [ddf_ne T w h d hne]; simp
    rw [e]
    simp

private theorem dom_ddf {B : Bridge L} (T : Spl B) (A : SD B.Δ) (w : Plc L) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ)
    (hd : Sig.SDom d) : A.DomS (ddf T w h d) := by
  intro v _
  by_cases hv : v = un w
  · subst hv
    rw [ddf_self]
    intro i k hik
    rcases hik.lt_or_eq with h1 | rfl
    · refine ((T w h).val_le _ _).1 ?_
      have e : ∀ i, (T w h).i ((pull T w h d i : (Kv (un w))ˣ) : Kv (un w)) = (d i : Kw w) := fun i =>
        congrArg Units.val (iu_pull T w h d i)
      rw [e, e]
      exact (hd i k h1).le
    · exact le_rfl
  · rw [ddf_ne T w h d hv]
    intro i k _
    simp

private theorem ex_ddf {B : Bridge L} (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hF : Fit T S VL A) (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hab : FitCh T S a b)
    (hEx : ∀ w (h : IsSplitAt w) (n : ℕ) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) (d : Fin n → (Kv (un w))ˣ), n = 2 ∨ n = 3 →
      expo ψ (fun i => iu T w h (d i)) = expo (fun i => (ψ i).comp (iu T w h)) d)
    (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) :
    A.exG b (ddf T w h d) = expo ![a w, 1, (a w)⁻¹] d := by
  have hmem : un w ∈ A.Sg := (hF.sg _).2 ⟨w, hw, rfl⟩
  unfold SD.exG
  rw [Finset.prod_eq_single_of_mem (un w) hmem]
  · rw [ddf_self, hab w hw h]
    have e1 := hEx w h 3 ![a w, 1, (a w)⁻¹] (pull T w h d) (Or.inr rfl)
    have e2 : (fun i => iu T w h (pull T w h d i)) = d := funext (iu_pull T w h d)
    rw [e2] at e1
    rw [e1]
    congr 1
    funext i
    fin_cases i <;> rfl
  · intro v _ hv
    rw [ddf_ne T w h d hv]
    exact ((So.expoEq (Kv v) (b v)).2.2 3 _).2.1

private theorem dc_step {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] (e : G ≃* G')
    (U' : Subgroup G') (U : Subgroup G) (hU : U'.comap e.toMonoidHom = U) (ψ : G → V) (g : G) (c : ℂ)
    (hfo : UpperTheory.V.AlgebraTools.FinOrb U' U' (e g)) (hlev : ∀ u ∈ U', ∀ x, ψ (e.symm (x * u)) = ψ (e.symm x))
    (h : dcF U g ψ = c • ψ) : dcF U' (e g) (ψ ∘ e.symm) = c • (ψ ∘ e.symm) := by
  have t := (So.dcMap G G' V e.toMonoidHom e.bijective U' g g).2.2.2 hfo (ψ ∘ e.symm) hlev
  have e1 : (ψ ∘ e.symm) ∘ e.toMonoidHom = ψ := funext fun y => by simp
  rw [e1, hU, h] at t
  funext y
  have := congrFun t (e.symm y)
  simpa using this.symm

private theorem lev_G (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hA : A.Ok) (hF : Fit T S VL A) : ∀ g : GA B.Δ, g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall (L := L) 3) S VL :=
  (So.levG L B hB T S VL A hA hF).1

private theorem lev_El (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hA : A.Ok) (hF : Fit T S VL A) : ∀ (g : GA B.Δ) d, A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧ ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i) :=
  (So.levG L B hB T S VL A hA hF).2.2.1

private theorem lev_Ex (B : Bridge L) (hB : B.Ok) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hA : A.Ok) (hF : Fit T S VL A) : ∀ w (h : IsSplitAt w) (n : ℕ) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) (d : Fin n → (Kv (un w))ˣ), n = 2 ∨ n = 3 →
      expo ψ (fun i => iu T w h (d i)) = expo (fun i => (ψ i).comp (iu T w h)) d :=
  (So.levG L B hB T S VL A hA hF).2.2.2.2

private theorem eig_fin (B : Bridge L) (T : Spl B) (S : Finset (Plc L)) (VL : ∀ w : Plc L, Lev (Kw w)) (A : SD B.Δ)
    (hF : Fit T S VL A)
    (hlG : ∀ g : GA B.Δ, g ∈ A.dat.UG ↔ (B.bG g : UA L 3) ∈ lev (Kall (L := L) 3) S VL)
    (hEl : ∀ (g : GA B.Δ) d, A.IsElG g d ↔ OnS S (B.bG g : UA L 3) ∧ ∀ w ∈ S, ∀ h, cLoc w (B.bG g : UA L 3) = Sig.dg fun i => iu T w h (d (un w) i))
    (hEx : ∀ w (h : IsSplitAt w) (n : ℕ) (ψ : Fin n → (Kw w)ˣ →* ℂˣ) (d : Fin n → (Kv (un w))ˣ), n = 2 ∨ n = 3 →
      expo ψ (fun i => iu T w h (d i)) = expo (fun i => (ψ i).comp (iu T w h)) d)
    (j : ℕ) (ch : Lp L → ℂ) (C : Base (U3 B.Δ) (GA B.Δ) (Wt.VG (InfinitePlace L) j)) (s : C.Tw) (hBG : A.dat.IsBG ch C s)
    (ψ : GA B.Δ → Wt.VG (InfinitePlace L) j) (hψ : ψ ∈ C.Forms)
    (a : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (b : Chs (Lp L)) (hab : FitCh T S a b) (hE : A.EigG ψ b)
    (w : Plc L) (hw : w ∈ S) (h : IsSplitAt w) (d : Fin 3 → (Kw w)ˣ) (hd : Sig.SDom d)
    (x : finU (E := L) (n := 3)) (hx : (x : UA L 3) = secW 3 w (Sig.dg d))
    (hfo : UpperTheory.V.AlgebraTools.FinOrb ((lev (Kall (L := L) 3) S VL).subgroupOf (finU (E := L) (n := 3))) ((lev (Kall (L := L) 3) S VL).subgroupOf (finU (E := L) (n := 3))) x) :
    dcF ((lev (Kall (L := L) 3) S VL).subgroupOf (finU (E := L) (n := 3))) x (fun y => ψ (B.bG.symm y)) =
      expo ![a w, 1, (a w)⁻¹] d • (fun y => ψ (B.bG.symm y)) := by
  have hg := is_el T S A hEl hF.pl w hw h d x hx
  have hcomap : ((lev (Kall (L := L) 3) S VL).subgroupOf (finU (E := L) (n := 3))).comap B.bG.toMonoidHom = A.dat.UG := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hlG]
    rfl
  have hE' := hE _ _ (dom_ddf T A w h d hd) hg
  rw [ex_ddf T S VL A hF a b hab hEx w hw h d] at hE'
  have hfo2 : UpperTheory.V.AlgebraTools.FinOrb ((lev (Kall (L := L) 3) S VL).subgroupOf (finU (E := L) (n := 3))) ((lev (Kall (L := L) 3) S VL).subgroupOf (finU (E := L) (n := 3))) (B.bG (B.bG.symm x)) := by
    rw [MulEquiv.apply_symm_apply]
    exact hfo
  have hstep := dc_step B.bG ((lev (Kall (L := L) 3) S VL).subgroupOf (finU (E := L) (n := 3))) A.dat.UG hcomap ψ (B.bG.symm x) _ hfo2
    (fun u hu g => level_step B A S VL hlG j ch C s hBG ψ hψ u (Subgroup.mem_subgroupOf.1 hu) g) hE'
  rw [MulEquiv.apply_symm_apply] at hstep
  exact hstep

end

theorem UpperTheory.V.Z.Sym.So.outG :
    UpperTheory.V.Z.Sym.So.OutG := by
  intro L _ _ _ B hB T S VL A hA hF j a b hab ch C s hBG hW ψ hψ hne hE
  have hsec := (Br.uaFacts L 3).1
  have hlG := lev_G B hB T S VL A hA hF
  have hEl := lev_El B hB T S VL A hA hF
  have hExpo := lev_Ex B hB T S VL A hA hF
  have hU : lev (Kall (L := L) 3) S VL ≤ finU (E := L) (n := 3) := inf_le_left.trans inf_le_left
  have hf := So.finToAF L 3 (Wt.VG (InfinitePlace L) j) (Wt.repG _ j) _ hU (fun x => ψ (B.bG.symm x))
    (fun f k hk hfk g => left_step B hB A j ch C s hBG hW ψ hψ f k hk hfk g)
    (fun u hu g => level_step B A S VL hlG j ch C s hBG ψ hψ u hu g)
  obtain ⟨φ, hAF, hφ, hdc⟩ := hf
  refine ⟨φ, ?_, hAF, ?_⟩
  · intro h0
    refine hne (funext fun g => ?_)
    have h1 := hφ (B.bG g)
    rw [h0] at h1
    simpa using h1.symm
  · intro w hw d hd
    have h := hF.pl.split w hw
    have hx0 : secW 3 w (Sig.dg d) ∈ finU (E := L) (n := 3) := ((hsec w h).1 _).1
    have hat := So.dcAt L 3 (Kall (L := L) 3) S VL hF.pl w hw ⟨le_rfl, fun _ _ => inf_le_right⟩ d
    have hfo := hat.1
    refine (hat.2 _ φ hAF.level _).2 ?_
    exact hdc ⟨_, hx0⟩ _ hfo (eig_fin B T S VL A hF hlG hEl hExpo j ch C s hBG ψ hψ a b hab hE w hw h d hd ⟨_, hx0⟩ rfl
      (finOrb_sub _ _ (⟨_, hx0⟩ : finU (E := L) (n := 3)) hfo))

end
end
