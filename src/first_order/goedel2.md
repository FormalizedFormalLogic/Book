# Gödel's Second Incompleteness Theorem

_These results are/will be included in [Arithmetization](https://github.com/iehality/Arithmetization/tree/master)._

Recall that inside $\mathsf{I}\Sigma_1$ we can do basic set theory and primitive recursion.
Many inductive notions and functions on them are defined in $\Delta_1$ or $\Sigma_1$ using 
the [fixpoint construction](./isigma1.md#fixpoint).

We work inside an arbitrary model $V$ of $\mathsf{I}\Sigma_1$.

## Coding of Terms and Formulae

### Term
Define $T_C$ as follows.

$$
\begin{align*}
  u \in T_C &\iff
      && (\exists z)[u = \widehat{\#z}] \lor {}  \\
    & && (\exists x) [u = \widehat{\&x}] \lor {} \\
    & && (\exists k, f, v) [\mathrm{Func}_k(f) \land \mathrm{Seq}(v) \land k = \mathrm{lh}(v) \land (\forall i, z)[\braket{i, z} \in v \to z \in C] \land u = \widehat{f^k(v)}] \\
\end{align*}
$$

$\widehat{\bullet}$ is a quasi-quotation.
$$
\begin{align*}
  \text{bounded variable: }&& \widehat{\#z} &\coloneqq \braket{0, z} + 1 \\
  \text{free variable: }&&\widehat{\&x} &\coloneqq \braket{1, x} + 1 \\
  \text{function: }&&\widehat{f^k(v)} &\coloneqq \braket{2, f, k, v} + 1 \\
\end{align*}
$$

$T_C$ is $\Delta_1$ (if $C$ is a finite set) and monotone. Let $\mathrm{UTerm}(t)$ be a fixpoint of $T_C$.
It is $\Delta_1$ since $T_C$ satisfies strong finiteness.
Define the function $\mathrm{termBV}(t)$ inductively on $\mathrm{UTerm}$ meaning the largest bounded variable $+1$ that appears in the term.
Define $\mathrm{Semiterm}(n, t) := \mathrm{UTerm}(t) \land \mathrm{termBV}(t) \le n$.

### Formula
Similarly, Define $F_C$:

$$
\begin{align*}
  u \in F_C &\iff
      && (\exists k, R, v)[\mathrm{Rel}_k(R) \land \text{$v$ is a list of $\mathrm{UTerm}$ of length $k$} \land u = \widehat{R^k (v)}] \lor {}  \\
    & && (\exists k, R, v)[\mathrm{Rel}_k(R) \land \text{$v$ is a list of $\mathrm{UTerm}$ of length $k$} \land u = \widehat{\lnot R^k (v)}] \lor {}  \\
    & && [u = \widehat{\top}] \lor {} \\
    & && [u = \widehat{\bot}] \lor {} \\
    & && (\exists p \in C, q \in C) [u = \widehat{p \land q}] \lor {} \\
    & && (\exists p \in C, q \in C) [u = \widehat{p \lor q}] \lor {} \\
    & && (\exists p \in C) [u = \widehat{\forall p}] \lor {} \\
    & && (\exists p \in C) [u = \widehat{\exists p}] 
\end{align*}
$$

The quasi-quotations are defined as follows:

$$
\begin{align*}
  \widehat{R^k(v)}       &\coloneqq \braket{0, R, k, v} + 1\\
  \widehat{\lnot R^k(v)} &\coloneqq \braket{1, R, k, v} + 1 \\
  \widehat{\top}         &\coloneqq \braket{2, 0} + 1\\
  \widehat{\bot}         &\coloneqq \braket{3, 0} + 1\\
  \widehat{p \land q}    &\coloneqq \braket{4, p, q} + 1\\
  \widehat{p \lor q}     &\coloneqq \braket{5, p, q} + 1\\
  \widehat{\forall p}    &\coloneqq \braket{6, p} + 1\\
  \widehat{\exists p}    &\coloneqq \braket{7, p} + 1\\
\end{align*}
$$

$F_C$ is $\Delta_1$ and monotone. Let $\mathrm{UFormula}(p)$ be a fixpoint of $F_C$ and define

$$
\mathrm{Semiformula}(n, p) \iff \mathrm{UFormula}(p) \land \mathrm{bv}(p) \le n
$$

The function $\mathrm{bv}(p)$ is defined inductively on $\mathrm{UFormula}$ meaning the largest bounded variable $+1$ that appears in the formula.

$\mathrm{UFormula}(p)$ and $\mathrm{Semiormula}(n, p)$ are again $\Delta_1$ since $F_C$ satisfies strong finiteness.


## Formalized Provability

Let $T$ be $\Delta_1$-definable theory.
Define $D_C$:

$$
\begin{align*}
  d \in D_C &\iff
    &&(\forall p \in \mathrm{sqt}(d))[\mathrm{Semiformula}(0, p)] \land {} \\
    && [
    & (\exists s, p)[d = \widehat{\text{AXL}(s, p)} \land p \in s \land \hat\lnot p \in s] \lor {} \\
    & && (\exists s)[d = \widehat{\top\text{-INTRO}(s)} \land \widehat{\top} \in s] \lor {}  \\
    & && (\exists s, p, q)(\exists d_p, d_q \in C)[
      d = \widehat{\land\text{-INTRO} (s, p, q, d_p, d_q)} \land
      \widehat{p \land q} \in s \land
      \mathrm{sqt}(d_p) = s \cup \{p\} \land \mathrm{sqt}(d_q) = s \cup \{q\}] \lor {}  \\
    & && (\exists s, p, q)(\exists d \in C)[
      d = \widehat{\lor\text{-INTRO}(s, p,q,d)} \land
      \widehat{p \lor q} \in s \land \mathrm{sqt}(d) = s \cup \{p, q\}] \lor {} \\
    & && (\exists s, p)(\exists d \in C)[
      d = \widehat{\forall\text{-INTRO}(s, p, d)} \land
      \widehat{\forall p} \in s \land \mathrm{sqt}(d) = s^+ \cup \{p^+[\&0]\}] \lor {} \\
    & && (\exists s, p, t)(\exists d \in C)[
      d = \widehat{\exists\text{-INTRO}(s, p, t, d)} \land
      \widehat{\exists p} \in s \land \mathrm{sqt}(d) = s \cup \{p(t)\}] \lor {} \\
    & && (\exists s)(\exists d' \in C)[
      d = \widehat{\mathrm{WK}(s, d')} \land
      s \supseteq \mathrm{sqt}(d') ] \\
    & && (\exists s)(\exists d' \in C)[
      d = \widehat{\mathrm{SHIFT}(s, d')} \land
      s = \mathrm{sqt}(d')^+ ] \\
    & && (\exists s, p)(\exists d_1, d_2 \in C)[
      d = \widehat{\mathrm{CUT}(s, p, d_1, d_2)} \land
      \mathrm{sqt}(d_1) = s \cup \{p\} \land \mathrm{sqt}(d_2) = s \cup \{\lnot p\}] \\
    & && (\exists s, p)[
      d = \widehat{\mathrm{ROOT}(s, p)} \land
      p \in s \land p \in T ] 
     ]\end{align*}
$$

$$
\begin{align*}
  \widehat{\text{AXL}(s, p)}       &\coloneqq \braket{s, 0, p} + 1\\
  \widehat{\top\text{-INTRO}(s)} &\coloneqq \braket{s, 1, 0} + 1 \\
  \widehat{\land\text{-INTRO}(s, p, q, d_p, d_q)}         &\coloneqq \braket{s,2, p, q, d_p, d_q} + 1\\
  \widehat{\lor\text{-INTRO}(s, p, q, d)}         &\coloneqq \braket{s, 3,p, q, d} + 1\\
  \widehat{\forall\text{-INTRO}(s, p, d)}    &\coloneqq \braket{s, 4, p, d} + 1\\
  \widehat{\exists\text{-INTRO}(s, p, t, d)}     &\coloneqq \braket{s, 5, p, t, d} + 1\\
  \widehat{\text{WK}(s, d)}    &\coloneqq \braket{s, 6, d} + 1\\
  \widehat{\text{SHIFT}(s, d)}    &\coloneqq \braket{s, 7, d} + 1\\
  \widehat{\text{CUT}(s, p, d_1, d_2)}    &\coloneqq \braket{s, 8, p, d_1, d_2} + 1\\
  \widehat{\text{ROOT}(s, p)}    &\coloneqq \braket{s, 9, p} + 1 \\
  \mathrm{sqt}(d) &\coloneqq \pi_1(d - 1)
\end{align*}
$$

$p^+$ is a *shift* of a formula $p$. $s^+$ is a image of *shift* of $s$.
Take fixpoint $\mathrm{Derivation}_T(d)$.

$$
\begin{align*}
  \mathrm{Derivable}_T(\Gamma) &\coloneqq (\exists d)[\mathrm{Derivation}_T(d) \land \mathrm{sqt}(d) = \Gamma] \\
  \mathrm{Bew}_T(p) &\coloneqq \mathrm{Derivable}_T(\{p\})
\end{align*}
$$

Following holds for all formula (not coded one) $\varphi$ and finite set $\Gamma$.

- *Sound*: $\N \models \mathrm{Bew}_T(\ulcorner \varphi \urcorner) \implies T \vdash \varphi$
  ```lean
  lemma LO.Arith.Language.Theory.Provable.sound : (T.codeIn ℕ).Provable ⌜p⌝ → T ⊢! p 
  ```
- *D1*: $T \vdash \varphi \implies V \models \mathrm{Bew}_T(\ulcorner \varphi \urcorner)$
  ```lean
  theorem LO.Arith.provable_of_provable : T ⊢! p → (T.codeIn V).Provable ⌜p⌝ 
  ```
- *D2*: $\mathrm{Bew}_T(\ulcorner \varphi \to \psi \urcorner)\ \&\ \mathrm{Bew}_T(\ulcorner \varphi \urcorner)
    \implies \mathrm{Bew}_T(\ulcorner \psi \urcorner)$
- *Formalized $\Sigma_1$-completeness*: Let $\sigma$ be a $\Sigma_1$-sentence. $V \models \sigma \implies
    V \models \mathrm{Bew}_{T + \mathsf{R_0}} (\ulcorner \sigma \urcorner)$
  ```lean
  theorem LO.Arith.sigma₁_complete (hσ : Hierarchy 𝚺 1 σ) : V ⊧ₘ₀ σ → T.Provableₐ (⌜σ⌝ : V)
  ```

Now assume that $T$ is a theory of arithmetic stronger than $\mathsf{R_0}$ and
$U$ be a theory  of arithmetic stronger than $\mathsf{I}\Sigma_1$.
Thanks to the completeness theorem, the following holds.
- $U \vdash \mathrm{Bew}_T(\ulcorner \sigma \urcorner) \implies T \vdash \ulcorner \sigma \urcorner$
- $T \vdash \ulcorner \sigma \urcorner \implies U \vdash \mathrm{Bew}_T(\ulcorner \sigma \urcorner)$
- $U \vdash \mathrm{Bew}_T(\ulcorner \sigma \to \pi \urcorner) \to \mathrm{Bew}_T(\ulcorner \sigma \urcorner) \to \mathrm{Bew}_T(\ulcorner \pi \urcorner)$
- $U \vdash \sigma \to \mathrm{Bew}_T(\ulcorner \sigma \urcorner)$ if $\sigma \in \Sigma_1\text{-sentence}$





