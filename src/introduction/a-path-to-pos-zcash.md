# A Path to Proof-of-Stake Zcash

The [TFL](../terminology.md#definition-tfl) design provides a possible first step in transitioning [Zcash](https://z.cash) to a [PoS](../terminology.md#definition-pos) protocol. Here we describe how a transition to PoS relates to "the Zcash roadmap" and how TFL fits into one approach to a PoS transition.

## The Zcash Tech-Tree

There are multiple developer orgs working on different proposed features for Zcash. Some of these involve multiple large distinct upgrade steps, and several of these steps depend on other such steps. This could be represented as a directed acyclic graph. We have begun referring to this space of possible future improvements as the *Zcash Tech-Tree*, taking inspiration from an analogous concept in gaming.[^tech-tree-history]

We envision a *proof-of-stake transition path* as one of the potential paths within this tech-tree which is the primary protocol focus of this proposal. An example visualization of this Zcash Tech-Tree might look like this:

```dot process
{{#include ../diagrams/zcash-tech-tree-generic.dot}}
```

## A Proof-of-Stake Transition Path

Given that context, we envision a "path" within the Zcash Tech-Tree for transitioning Zcash to PoS. At the top level we propose that this path contain at least two major milestones:

1. Transitioning from current Zcash PoW to a hybrid PoW/PoS system.
2. Transitioning from a hybrid PoW/PoS system to pure PoS.

After this transition to pure PoS, there are likely to be future improvements to the PoS protocol, or the consensus protocol more generally. This TFL book focuses almost exclusively on the first step in this sequence.

Our primary motivation for proposing (at least) two steps is to minimize disruption to usability, safety, security, and the ecosystem during each step.

With this approach, the Zcash Tech Tree with the [TFL](../terminology.md#definition-tfl) approach might look something like this:

```dot process
{{#include ../diagrams/zcash-tech-tree-tfl-steps.dot}}
```

## Design Goals for a Hybrid PoW/PoS System

We are refining the design of TFL with several design goals. As we refine the design and make various trade-offs, we may not be able to achieve all of these goals.

- We want minimal-to-no disruption for existing wallet use cases and UX. For example, nothing should change for the user flows for storing or transferring funds, the format of addresses, etc.
- We want a security analysis of the proposed protocol to be as simple as possible given existing security analyses of current Zcash.
- We want to enable new use cases around PoS that allow mobile shielded wallet users to earn a return on delegated ZEC.
- We want to enable trust-minimized bridges and other benefits by providing a protocol with [assured finality](../terminology.md#definition-assured-finality).
- We want to improve the _modularity_ of the consensus protocol. That is, it should be possible to understand some consensus properties only given knowledge of a "component" of the protocol, and it should be possible to implement consensus rules in modular code components with clean interfaces.

We will be refining these goals and potentially adding more as we continue to develop this proposal.

With the motivation and goals for a first-step hybrid PoW/PoS protocol in mind, we introduce the specifics of TFL in the next subchapter.

---

[^tech-tree-history]: See [Wikipedia's Technology Tree - History](https://en.wikipedia.org/wiki/Technology_tree#History) section for details.
