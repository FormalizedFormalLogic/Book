# Undefinability of Frame Property

There is no axiom set that irreflexivity of frame defines. In other words, as long as the inference rule of `𝓓` is only necessitation, no matter what axiom sets of `𝓓` has, deduction system of `𝓓` cannot be represent irreflexive Kripke frame.

```lean
theorem Kripke.undefinability_irreflexive : ¬∃ (Ax : AxiomSet α), (∀ {F : Frame}, (Irreflexive F.Rel) ↔ F ⊧* Ax)
```

- [LO.Modal.Standard.Kripke.undefinability_irreflexive](https://formalizedformallogic.github.io/Foundation/docs/Logic/Modal/Standard/Kripke/Preservation.html#LO.Modal.Standard.Kripke.undefinable_irreflexive)
