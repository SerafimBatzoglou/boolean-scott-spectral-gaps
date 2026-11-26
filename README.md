# Unbounded minimum Scott ranks for Boolean algebras

GPT 6.2 Astra (Codex) with Serafim Batzoglou

How hard is it to identify a single countable Boolean algebra up to isomorphism? A sentence can describe a class of algebras in relatively simple terms even when every countable member requires a much more complex description to identify individually. [One-page explanation](RESULT.md) · [Printable introduction](paper/result-in-one-page.pdf)

**Theorem.** For every countable ordinal $b$, there is a pure Boolean $\Pi_{\omega+4}$ sentence with at least one countable model. Every countable model of that sentence has Scott rank greater than $b$. Here Scott rank is the least $r$ for which a $\Pi_{r+1}$ sentence identifies the structure up to isomorphism. The defining sentence may depend on $b$. Its complexity stays bounded by $\Pi_{\omega+4}$.

This answers the existence part of Gonzalez and Harrison-Trainor’s Question 1.9 negatively. The theorem gives $\omega+4$ as an upper bound on the first level of failure. [Original question](https://arxiv.org/html/2411.12084v1)

## Read the proof

| Resource | Contents |
| --- | --- |
| [Manuscript (PDF)](paper/boolean-scott-spectral-gaps.pdf) · [LaTeX source](paper/boolean-scott-spectral-gaps.tex) | The full proof in 16 pages, from definitions and worked examples through the all-model absorption theorem and rank lower bound. |
| [Formal theorem](BooleanScott/PureCounterexample.lean#L61) | The exact statement in Lean, including the Boolean laws, the existence of a countable model, and the rank bound for every countable model. |
| [Guide to the formal proof](PROOF_GUIDE.md) | The correspondence between the mathematical arguments and the Lean modules. |
| [Rank and syntax](BooleanScott/Infinitary.lean) · [Absorption theorem](BooleanScott/NegativeResolution.lean) | The infinitary language and the geometric criterion used in the proof. |

The proof constructs a fixed Boolean factor $B$ and a sentence for each tree $T$. Every countable Boolean algebra $A$ satisfying that sentence obeys the same criterion: $A\cong A\times B$ precisely when $T$ has an infinite branch. A projection argument supplies a branchless tree for which every satisfying $A$ agrees with its product on all $\Pi_{b+1}$ sentences. The two structures are nonisomorphic, so none of those sentences isolates $A$. [Formal projection argument](BooleanScott/Reduction.lean)

## Check the proof

Install [elan](https://github.com/leanprover/elan) and Git. From the root of a fresh clone, run

```sh
lake exe cache get
./scripts/verify.sh
```

The first command obtains the pinned dependencies and their available build cache. The script builds the project, runs the [transitive axiom audit](Audit.lean), and uses `leanchecker` to replay each of the 85 proof modules in a separate process. The [verification transcript](verification.txt) records an audit of **955** declarations and **85** successful module replays. The allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`. [Verifier script](scripts/verify.sh) · [Lean version](lean-toolchain) · [Dependency revisions](lake-manifest.json)

To inspect the literal statement and its dependencies after building, run

```sh
printf '%s\n' 'import BooleanScott' \
  '#print BooleanScott.pure_boolean_counterexample' \
  '#print axioms BooleanScott.pure_boolean_counterexample' | lake env lean --stdin
```

To rebuild both PDFs, install Pandoc 3 and a TeX Live distribution with `pdflatex` and `latexmk`, then run `./scripts/build-paper.sh`. The files are written to `dist/paper-build/`.

## Contributions and review

OpenAI Codex developed the mathematical argument and Lean formalization under the direction of Serafim Batzoglou. Batzoglou directed the proof search and requested adversarial checks. The formalization passed the documented Lean verification. Batzoglou has not yet read the proof in full or independently verified that the formal theorem resolves the original question. Independent expert review is pending. [Citation metadata](CITATION.cff)

The proof code is available under Apache-2.0. The manuscript, one-page introduction, README and proof guide are available under CC BY 4.0. [License texts and scope](LICENSE.md)
