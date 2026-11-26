# How hard is it to describe one Boolean algebra?

If a class of mathematical objects is easy to describe, must at least one member be easy to identify? For countable Boolean algebras, the answer is no.

A **Boolean algebra** behaves like a family of sets with union, intersection, complement, an empty set $0$, and a whole set $1$. It is **countable** if a finite list or a sequence numbered $0,1,2,\ldots$ contains all its elements. Two algebras are **isomorphic** if their elements can be put in one-to-one correspondence preserving these operations and constants.

A **formula** can leave a variable, such as $x$, unspecified. A **sentence** leaves none unspecified, so it is true or false of a given structure. A structure satisfying it is a **model**. For example, “there are at least four elements” describes many algebras. The Boolean algebra laws together with “$0$ and $1$ are distinct, and every element equals one of them” pick out the two-element Boolean algebra up to isomorphism. A **Scott sentence** for a countable algebra picks it out in just this way among countable systems equipped with these three operations and two constants.

**How is a description measured?** We allow countably many clauses joined by “and” or “or.” Their complexity is indexed by *countable ordinals*, stages with at most countably many predecessors. After $0,1,2,\ldots$ comes $\omega$, the first infinite stage. The stage $\omega+4$ is four steps later.

At stage zero we use equations and finite combinations of them with “and,” “or,” and “not.” At a higher stage $\alpha$, a $\Pi_\alpha$ formula joins clauses by “and.” Each clause says “for every choice of these elements” followed by a lower-stage $\Sigma$ formula. A $\Sigma_\alpha$ formula joins clauses by “or,” using “there exist elements” followed by a lower-stage $\Pi$ formula. Both forms start with the same stage zero. Each clause can quantify over finitely many elements, or none. Thus “every element equals $0$ or $1$” has form $\Pi_1$. At stage $\omega$, different clauses can use arbitrarily high finite stages.

The **Scott rank** of a countable algebra is the least ordinal $b$ for which it has a $\Pi_{b+1}$ Scott sentence. Higher rank means that identifying the algebra requires a more complex sentence.

**The result.** Choose any countable ordinal $b$. There is a $\Pi_{\omega+4}$ sentence that has countable Boolean algebras satisfying it, and **every one of them has Scott rank greater than $b$**. Pick any such algebra $A$. Every $\Pi_{b+1}$ sentence true of $A$ is also true of some countable Boolean algebra that is not isomorphic to $A$.

**Why it matters.** For linear orders, where every two elements can be compared, a sentence with countable models always has one whose Scott rank is bounded in terms of the sentence’s complexity. Gonzalez and Harrison-Trainor asked whether Boolean algebras obey a similar bound. Here the sentence can change with $b$ while its complexity stays bounded by $\Pi_{\omega+4}$. Even the least Scott rank among its countable models can exceed any prescribed countable ordinal. [Original question, §1.9](https://arxiv.org/html/2411.12084v1)

GPT 6.2 Astra (Codex) with Serafim Batzoglou · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
