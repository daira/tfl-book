# Questions about Crosslink

### Why don’t we have a bc‑block‑validity rule snapshot(LF(H)) ⪯<sub>bc</sub> H ?

Rationale: Can we outright prevent rollbacks > $\sigma$ from ever appearing in $\Ch_i^t$ ?

```admonish info
This document analyzes the effect of this rule *on its own*. For the effect in combination with an additional [**Linearity rule**](#linearity-rule), see the [Linearity and Last Final Snapshot rules](potential-changes.html#linearity-and-last-final-snapshot-rules) section of [Potential changes for Crosslink 2](potential-changes.html).
```

Daira-Emma: In a variant of Crosslink with this rule, an adversary’s strategy would be to keep the $\contextbft$ fields in its blocks as $C$ such that $B = \bftlastfinal(C)$ when the attack starts, and then fork from the bc‑best‑chain that extends $\snapshot(B)$. If its private chain falls behind the public bc‑best‑chain, it resets, just like in a conventional private mining attack.

Note that the proposed rule does *not* prevent the adversary’s private chain from just staying at the same $\contextbft$ block. The reason is that Crosslink does not change the fork-choice rule of $\Pi_{\bc}$. That is, even if the adversary’s chain has a $\contextbft$ that is far behind the current bft‑block, it is still allowed to become the bc‑best‑chain.

(Eventually the adversary’s chain using this strategy will hit the finality gap bound of $L$ blocks. But that must be significantly greater than $\sigma$, to avoid availability problems. So it does not prevent the adversary from performing a rollback longer than $\sigma$ blocks before they hit the bound. Also, going into Stalled Mode for new blocks does not prevent the attacker’s chain from having included harmful transactions before that point.)

It is possible to change the fork-choice rule, for example so that the bc‑best‑chain for a node $i$ is required to extend $\snapshot(B)$ where $B$ is the last final block for any bft-chain in node $i$’s view.

This would break the current safety and liveness arguments for Crosslink. But for the sake of argument, suppose we did it anyway.

The adversary’s strategy would change slightly: it resets if *either* its private chain falls behind the public bc‑best‑chain, or its private chain is invalidated because it forks before $\snapshot(B)$ for some new last final block $B$ of a bft-chain. During the attack, it also attempts to impede progress of the BFT protocol as far as possible.

In that case, the proposed rule still does not preclude a rollback of more than $\sigma$ blocks, for several reasons:
* In general we can’t say anything about how many bc‑blocks are mined in any given interval, so it could be the case that more than $\sigma$ blocks are mined on both the honest chain and the adversary’s chain before it would be realistically possible to go through even a single round of the BFT protocol.
* Nor can we say anything about how quickly those blocks are finalized, unless we enforce it, which we don’t. (In Crosslink we do enforce a finalization gap bound $L$, but as explained above $L$ must be significantly greater than $\sigma$, so that doesn’t really help.)
  * In particular, the adversary could be suppressing publication of final bft‑blocks, or attacking the *liveness* of the BFT protocol in other ways. An attack against BFT liveness is potentially easier than an attack against BFT safety, and it would be difficult to characterize exactly how much this rule gains you in terms of security given that (at best) it’s dependent on that.
* $\snapshotlf{H}$ will typically be at least $\sigma + 1$ blocks back from $H$.
  The argument for that goes:
  > None of the block hashes in $\LF(H)\dot\headersbc$ can point to $H$ because that would be a hash cycle. In a typical case where no block withholding and no *other* rollback (not caused by the adversary) occurs on the honestly mined chain, the proposer of the last final block before a context bft‑block that $H$ can point to will have, at the latest, $H \trunc_{\bc}^1$ as $\tip(B)$. Under these conditions, $\snapshotlf{H}$ will point, at the latest, to $\sigma$ blocks before $H \trunc_{\bc}^1$, i.e. $\sigma + 1$ blocks before $H$.
  >
  This means that by the time $\snapshotlf{H}$ could catch up to $H$, on average $\sigma + 1$ block times will have occurred. So, roughly speaking, the rule that $\snapshotlf{H} \preceq_{\bc} H$ does not usefully constrain the adversary until <span style="white-space: nowrap">after $\sigma + 1$ block times.</span> <span style="white-space: nowrap">Wlog let’s assume $\Pi_{\bc}$</span> <span style="white-space: nowrap">uses PoW: if $\sigma$</span> is chosen reasonably, then being able to do <span style="white-space: nowrap">a $\sigma + 1$-block rollback</span> at all probably requires having somewhere close to 50% of network hash rate. And so in $\sigma + 1$ block times the adversary has a significant chance of being able to do the required rollback before the suggested rule “kicks in”. (Much additional latency is added by the BFT protocol, which is simultaneously under attack to maximize this latency.)

All that said, does the suggested rule help? First we have to ask whether it introduces any weaknesses.
  * One potential issue is that the rule cuts both ways: if an adversarial rollback of more than $\sigma$ blocks *does* occur, then the adversary can make a proposal that will “lock in” its success. But it can be argued that this is intended behaviour anyway: the adversary has a confirmed chain, and is entitled to propose to finalize it.
  * What happens if $\Pi_{\bft}$ is broken?
    * **Edit: the answer below refers to Crosslink before the Increasing Score rule was added.**
    * This could definitely be a problem. If either an adversary has a two‑thirds supermajority of validators, *or* $\Pi_{\bft}$ is completely broken (e.g. by a bug in the implementation of the validation signature scheme), then they can add a final block to the bft-chain with a $\headersbc$ field that does not satisfy the honest voting condition. They do not need this to be bft-valid (although greater vulnerability to bugs in the implementation of bft-validity are also an issue). Then they can use the proposed rule to prevent an arbitrary bc-valid-chain from being extended (e.g. by mining $\sigma + 1$ blocks from $\Origin_{\bc}$ at the genesis difficulty, then getting that chain into a final bft‑block). **[Edit: they would no longer be able to do this using a chain mined at a much lower difficulty, because of the Increasing Score rule.]**
      * In Crosslink, this is very carefully avoided. The only similar rule that depends on $\snapshotlf{H}$ and that could potentially affect liveness of $\Pi_{\bc}$ is the [**Finality depth**](./construction.md#%CE%A0bc‑block-validity) rule. But that rule *always* allows the alternative of producing a Stalled Mode block on the current bc‑best‑chain — and honest block producers will do so. Therefore, the effect of trying to exploit even a catastrophic break in $\Pi_{\bft}$ in order to cause a rollback of $\LOG_{\fin}$, as long as $\Pi_{\bc}$ has not also been broken, is to go into Stalled Mode.
      * This does not mean that a break of $\Pi_{\bft}$ is not a problem for Crosslink. In particular, an adversary that can violate safety of $\Pi_{\bft}$ can violate safety of $\LOG_{\ba}$ (and of $\LOG_{\fin}$ if there is also <span style="white-space: nowrap">a $\sigma$‑block rollback</span> in some node’s bc‑best‑chain).
      * The difference is that a safety violation of $\Pi_{\bft}$ can be directly observed by nodes *without any chance of false positives*, which is not necessarily the case for all possible attacks against $\Pi_{\bft}$. (The attack described above does *not* violate safety of $\Pi_{\bft}$; it just adds a final bft‑block with a suspiciously long $\Pi_{\bc}$ rollback. It could alternatively have added a block with a less suspiciously long rollback, say exactly $\sigma + 1$ blocks. That is, in pursuit of preventing an attack against $\Pi_{\bc}$, we have enabled attacks against $\Pi_{\bft}$ to achieve the same effect — precisely what Crosslink is designed to prevent.)
      * This raises an interesting idea: if any node sees a rollback in the chain of final bft‑blocks, it could provide objective evidence of that rollback in the form of a “bft-final-vee”: two final bft‑blocks with the same parent. Similarly, if any node sees more than one third of stake vote for conflicting blocks in a given epoch, then the assumption bounding the adversary’s stake must have been violated. This evidence can be posted in a transaction to the bc-chain. In that case, any node that is synced to the bc-chain can see that the bft-chain suffered a violation of safety or of a safety assumption, without needing to have seen that violation itself. This can be generalized to allow other proofs of flaws in $\Pi_{\bft}$. Optionally, a bc-chain that has posted such a proof could be latched into Stalled Mode until manual intervention can occur. (Obviously we need to make sure that this cannot be abused for denial-of-service.)
      * This is now described in [Potential changes to Crosslink](./potential-changes.md#recommended-recording-more-info-about-the-bftchain-in-bcblocks).

**Okay, but is it a good idea to make that change to the fork-choice rule anyway?**

Probably not. I don’t know how to repair the safety and liveness arguments.

The change was that the bc‑best‑chain for a node $i$ would be required to extend $\snapshot(B)$ where $B$ is the last final bft‑block in node $i$’s view.

From the point of view of any modular analysis that treats $\Pi_{\mathsf{bft}}$ as potentially subverted, we cannot say anything useful about $\snapshot(B)$. It seems as though any repair would have to assume much more about the BFT protocol than is desirable.

In general, changes to fork‑choice rules are tricky; it was a fork-choice rule problem that allowed the liveness attack against Casper FFG described in [[NTT2020](https://eprint.iacr.org/2020/1091.pdf), Appendix E].

**What if validators who see that a long rollback occurred, refuse to vote for it?**

Yep that is allowed. The rule is “An honest validator will only vote for a proposal $P$ if ...” (not if‑and‑only‑if). If an honest validator sees a “good” reason not to vote for a proposal, including reasons based on out‑of‑band information, they should not. The [Complementarity argument](./the-arguments-for-bounded-availability-and-finality-overrides.md#complementarity) made in *The Argument for Bounded Availability and Finality Overrides* actually depends on this. Obviously, it may affect BFT liveness (and that’s okay).

The only reason why we don’t make this part of the voting condition is that it’s a stateful rule. A new validator could come along and wouldn’t have the state needed to enforce it. Perhaps that could be fixed.
