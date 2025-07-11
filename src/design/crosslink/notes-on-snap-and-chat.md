# Notes on Snap‑and‑Chat

The discussion in [The Argument for Bounded Availability and Finality Overrides](./the-arguments-for-bounded-availability-and-finality-overrides.md) is at an abstract level, applying to any Ebb‑and‑Flow-like protocol.

This document considers specifics of the Snap‑and‑Chat construction proposed in [[NTT2020]](https://eprint.iacr.org/2020/1091.pdf) ([arXiv version](https://arxiv.org/pdf/2009.04987.pdf)).

```admonish info "Terminology"
We are trying to be precise in this document about use of the terms “Ebb‑and‑Flow”, which is the security model and goal introduced in [[NTT2020]](https://eprint.iacr.org/2020/1091.pdf), vs “Snap‑and‑Chat”, which is the construction proposed in the same paper to achieve that goal. There are other ways to design an Ebb‑and‑Flow protocol that don’t run into the difficulties described in this section (or that run into different difficulties).
```

### Effect on consensus

A general problem with the Snap‑and‑Chat construction is that it does not follow, from enforcement of the original consensus rules on blocks produced in $\Pi_{\lc}$, that the properties they are intended to enforce hold for the $\LOG_{\fin,i}^t$ or $\LOG_{\da,i}^t$ ledgers. Less obviously, the converse also does not follow: enforcing unmodified consensus rules on $\Pi_{\lc}$ blocks is **both** too lax and too strict.

Recall from the paper how $\LOG_{\fin,i}^t$ and $\LOG_{\da,i}^t$ are constructed (starting at the end of page 8 of [[NTT2020]](https://eprint.iacr.org/2020/1091.pdf)):

> 3) *Ledger extraction:* Finally, how honest nodes compute $\LOG_{\fin,i}^t$ and $\LOG_{\da,i}^t$ from $\Ch_i^t$ and $\ch_i^t$ is illustrated in Figure 6. Recall that $\Ch_i^t$ is an ordering of snapshots, i.e., a chain of chains of LC blocks. First, $\Ch_i^t$ is flattened, i.e. the chains of blocks are concatenated as ordered to arrive at a single sequence of LC blocks. Then, all but the first occurrence of each block are removed (sanitized) to arrive at the finalized ledger $\LOG_{\fin,i}^t$ of LC blocks. To form the available <span style="white-space: nowrap">ledger $\LOG_{\da,i}^t$,</span> <span style="white-space: nowrap">$\ch_i^t$, which is</span> a sequence of LC blocks, is appended to $\LOG_{\fin,i}^t$ and the result again sanitized.

The use of “sanitized” here to apply to a sequence of $\Pi_{\lc}$ blocks is imprecise, as is the reference to appending $\ch_i^t$ (a sequence of blocks) to $\LOG_{\fin,i}^t$ (a sequence of transactions). Sanitization is properly defined on the top-right of page 7 of [[NTT2020]](https://eprint.iacr.org/2020/1091.pdf) as taking only the first *valid* occurrence of a transaction in a sequence of *transactions*.

The paper shows signs of it having been assumed at some point in the writing process that sanitization will only remove *duplicate* transactions, but that is not the case: for example it may remove a transaction because some of its inputs have been double-spent, or because it spends an output of a prior transaction that was removed (see [Effect on transaction ordering](#effect-on-transaction-ordering) below for further discussion).

Thus, $\LOG_{\fin,i}^t$ and $\LOG_{\da,i}^t$ are sequences of transactions, *not* sequences of blocks — and they may contain only a subset of the transactions from any given $\Pi_{\lc}$ block. Therefore, [consensus rules defined at the block level](https://zips.z.cash/protocol/protocol.pdf#blockheader) are not applicable.

```admonish warning "Zcash-specific"

Most of these rules are Proof‑of‑Work‑related checks that can be safely ignored at this level. Some are related to the `hashBlockCommitments` field intended for use by the FlyClient protocol. It is not at all clear how to make FlyClient (or other uses of this commitment) work with the Snap‑and‑Chat construction. In particular, the `hashEarliest{Sapling,Orchard}Root`, `hashLatest{Sapling,Orchard}Root`, and `n{Sapling,Orchard}TxCount` fields don’t make sense in this context since they could only reflect the values in $\ch_i^t$, which have no relation in general to those for any subrange of transactions in $\LOG_{\da,i}^t$. This problem occurs as a result of sanitization and so will be avoided by Crosslink 2, which does not need sanitization.
```

Since $\LOG_{\da,i}^t$ does not have blocks, it is not well-defined whether it has “coinbase‑only blocks” when in Stalled Mode. That by itself is not so much of a problem because it would be sufficient for it to have only coinbase transactions in that mode.

### Effect on issuance

The issuance schedule of Zcash was designed under the assumption that blocks only come from a single chain, and that the difficulty adjustment algorithm keeps the rate of block mining roughly constant over time.

For Snap‑and‑Chat, if there is a rollback longer than $\sigma$ blocks in $\Pi_{\lc}$, additional coinbase transactions from the rolled-back chain will be included in $\LOG_{\fin}$.

We can argue that this will happen rarely enough not to cause any significant problem for the overall issuance schedule. However, it does mean that issuance is less predictable, because the block subsidies will be computed according to their depth in the $\Pi_{\lc}$ chain on which they were mined. So it would no longer be the case that coinbase transactions issue a deterministic, non-increasing sequence of block subsidies. (Again, this problem will be avoided by Crosslink 2.)

### Effect on transaction ordering

The order of transactions in any particular $\ch_i^t$ is *not* in general preserved in either $\LOG_{\fin}$ or $\LOG_{\da}$. This *is* considered in the paper (middle of the left column on page 10) but it is very easy to miss it:

> Thus, snapshots taken by different nodes or at different times can conflict. However, $\Pi_{\bft}$ is still safe and thus orders these snapshots linearly. Any transactions invalidated by conflicts are sanitized during ledger extraction.

That is, a transaction from one snapshot might double-spend an output already spent in a different transaction of a different snaphot earlier in the flattening order. If it is omitted, then later transactions could depend on the outputs of the omitted one. The paper is saying that each transaction is only included if (in Bitcoin and Zcash terminology) it satisfies contextual checks for double-spending and existence of inputs at the point in the ledger where it would be added.

Since nullifiers for shielded spends are public, it is possible to do this even for shielded transactions. Each node $i$ will construct commitment trees in the order given by $\LOG_{\da,i}^t.$

```admonish info
This means that if $\LOG_{\fin,i}$ is extended by a block that is not the next block in $\LOG_{\da,i}$ after the finalization point (and that has different note commitments), then *all* shielded transactions from that point onward in the previous $\LOG_{\da,i}$ will be invalidated. It could be possible to do better at the expense of a more complicated note commitment tree structure. This situation is expected to be rare, because it can only occur if there is a rollback of more than $\sigma$ blocks in the $\Pi_{\lc}$ consensus chain or a failure of BFT safety. However, it is clear from this that the design of Snap‑and‑Chat is making implicit assumptions derived from transparent Bitcoin-like blockchains.
```

### Subtlety in the definition of sanitization

There are two possible ways to interpret how $\LOG_{\{\fin,\da\}}$ are constructed in Snap‑and‑Chat:

1. Concatenate the transactions from each final BFT block snapshot of an LC chain, and sanitize the resulting transaction sequence by including each transaction iff it is contextually valid.
2. Concatenate the *blocks* from each final BFT block snapshot of an LC chain, remove duplicate *blocks*, and only then sanitize the resulting transaction sequence by including each transaction iff it is contextually valid.

These are equivalent in the setting considered by [[NTT2020]](https://eprint.iacr.org/2020/1091.pdf), but the argument for their equivalence is not obvious. We definitely want them to be equivalent: in practice there will be many duplicate blocks from chain prefixes in the input to sanitization, and so a literal implementation of the first variant would have to recheck all duplicate transactions for contextual validity. That would have at least $O(n^2)$ complexity (more likely $O(n^2 \log n)$) in the length $n$ of the block chain, because the length of each final snapshot grows with $n$.

Suppose that, in a particular $\Pi_{\lc}$, the only reasons for a transaction to be contextually invalid are double-spends and missing inputs. In that case the argument for equivalence is:
* If a transaction is omitted due to a double-spend, then any subsequent time it is checked, that input will still have been double-spent.
* If a transaction is omitted due to a missing input, this can only be because an earlier transaction in the input to sanitization was omitted. So the structure of omitted transactions forms a DAG in which parent links must be to *earlier* omitted transactions. The roots of the DAG are at double-spending transactions, which cannot be reinstated. A child cannot be reinstated until its parents have been reinstated. Therefore, no transactions are reinstated.

Note that any *other* reason for transactions to be contextually invalid might interfere with this argument. Therefore, strictly speaking Snap‑and‑Chat should require of $\Pi_{\lc}$ that there is no such other reason. This does not seem to be explicitly stated anywhere in [[NTT2020]](https://eprint.iacr.org/2020/1091.pdf).

```admonish warning "Zcash-specific"

In Zcash a transaction can also be contextually invalid because it has expired, or because it has a missing anchor. Expiry can be handled by extending the above argument as follows:
* If a transaction is omitted due to having expired, then any subsequent time it is checked, it will still be expired.

It is not obvious how to extend it to handle missing anchors, because it *is* technically possible for a duplicate transaction that was invalid because of a missing anchor to *become* valid in a subsequent block. That situation would require careful manipulation of the commitment trees, but there does not seem to be anything preventing it from being provoked intentionally. The argument that was used above for missing inputs does not work here, because there is no corresponding DAG formed by the transactions with missing anchors: the same commitment treestate can be produced by two unrelated transactions.
```

### Spending finalized outputs

Transactions in $\ch_i^t$ need to be able to spend outputs that are not necessarily from any previous transaction in $\ch_i^t$. This is because, from the point of view of a user of node $i$ at time $t$, the block chain includes all transactions in $\LOG_{\da,i}^t$. All of the transactions after the finalization point are guaranteed to also be in $\ch_i^t$, but the ones before the finalization point (i.e. in $\LOG_{\fin,i}^t$) are not, because they could be from some other $\ch_j^u$ for $u \leq t$ and $j \neq i$ (intuitively, from some long chain fork that was once considered confirmed by enough nodes).

```admonish info
Honest nodes only ever vote for confirmed snapshots, that is, prefixes of their best $\Pi_{\lc}$ chain truncated by the confirmation depth $\sigma$. Obviously the whole point of having the BFT protocol is that chain forks longer than $\sigma$ **can** occur in $\Pi_{\lc}$ — otherwise we'd just use $\Pi_{\lc}$ and have done. So it is not that we expect this case to be common, but if it happens then it will never fix itself: the consensus chain in $\Pi_{\lc}$ will continue on without ever including the transactions from $\LOG_{\fin}^t$ that were obtained from a snapshot of another fork.
```

A user must be able to spend outputs for which they hold the spending key from **any** finalized transaction, otherwise there would be no point to the finalization.

The authors of [[NTT2020]](https://eprint.iacr.org/2020/1091.pdf) probably just missed this: the paper only has evidence that they simulated their construction, rather than implementing it for Bitcoin or any other concrete block chain as $\Pi_{\lc}$. Let’s try to repair it.

Suppose that node $j$ is trying to determine whether $\ch_i^t$ is a consensus-valid chain, which is necessary for deterministic consensus in $\Pi_{\lc}$. It cannot decide whether to allow transactions in $\ch_i^t$ to spend outputs not in the history of $\ch_i^t$ on the basis of its *own* finalized view $\LOG_{\fin,j}^t,$ because $\LOG_{\fin,i}^t$ and $\LOG_{\fin,j}^t$ are not in general the same.

Of course, we hope that $\LOG_{\fin,i}^t$ and $\LOG_{\fin,j}^t$ are consistent, i.e. one is a prefix of the other. But even if they are consistent, they are not necessarily the same length. In particular, if $\LOG_{\fin,j}^t$ is *shorter* than $\LOG_{\fin,i}^t,$ then node $j$ does not have enough information to fill in the gap — and so it may incorrectly view a transaction in $\ch_i^t$ as spending an output that does not exist, when actually it does exist in $\LOG_{\fin,i}^t \setminus \LOG_{\fin,j}^t.$ Conversely if $\LOG_{\fin,j}^t$ were longer and node $j$ were to allow spending an output in $\LOG_{\fin,j}^t \setminus \LOG_{\fin,i}^t,$ that would be using information that is not necessarily available to other nodes, and so node $j$ could diverge from consensus.

Consensus validity of the block at the tip of $\ch_i^t$ can only be a deterministic function of the block itself and its ancestors in $\ch_i^t$. It is crucial to be able to *eventually* spend outputs from the finalized chain. We are forced to conclude that the chain $\ch_i^t$ **must include** the information needed to calculate $\LOG_{\fin,i}^s$ for some $s$ not too far behind $t$. That is, $\Pi_{\lc}$ must be modified to ensure that this is the case. This leads us to strengthen the required properties of an Ebb‑and‑Flow protocol to include another property, “finalization availability”.

## Finalization Availability

In the absence of security flaws and under the security assumptions required by the finality layer, the finalization point will not be seen by any honest node to roll back. However, that does not imply that all nodes will see the same finalized height — which is impossible given network delays and unreliable messaging.

Both in order to optimize the availability of applications that require finality, and in order to solve the technical issue of spending finalized outputs described in the previous section, we need to consider availability of the information needed to finalize the chain up to a particular point.

Note that in Bitcoin-like consensus protocols, we don’t generally consider it to be an availability flaw that a block header only *commits* to the previous block hash and to the Merkle tree of transactions in the block, rather than including them directly. These commitments allow nodes to check that they have the correct information, which can then be requested separately.

Suppose, then, that each block header in $\Pi_{\lc}$ commits to the **L**ast **F**inal BFT block known by the $\Pi_{\lc}$ block producer. For an LC block chain with block $H$ at its tip, we will refer to this commitment <span style="white-space: nowrap">as $\LF(H)$.</span> We refer to the parent block <span style="white-space: nowrap">of $H$</span> <span style="white-space: nowrap">as $H \trunc_{\bc}^1$</span> (this is a special case of a notation that will be defined in [The Crosslink 2 Construction](./construction.md)).

```admonish success "Consensus rule: Extension"
We require, as a consensus rule, that if $H$ is not the genesis block header, then this BFT block either descends from or is the same as the final BFT block committed to by the $\Pi_{\lc}$ block’s parent. <span style="white-space: nowrap">That is, $\LF(H \trunc_{\bc}^1) \preceq_{\bft} \LF(H)$.</span>
```

This Extension rule will be preserved into Crosslink 2.

The Extension rule does not prevent the BFT chain from rolling back, if the security assumptions of $\Pi_{\bft}$ were violated. However, it means that if <span style="white-space: nowrap">a node $i$</span> does not observe a rollback in $\Pi_{\lc}$ at confirmation <span style="white-space: nowrap">depth $\sigma$,</span> then it will also not observe any instability <span style="white-space: nowrap">in $\LOG_{\fin,i}$,</span> *even if* the security assumptions of $\Pi_{\bft}$ are violated. This property holds **by construction**, and in fact regardless <span style="white-space: nowrap">of $\Pi_{\bft}$.</span>

```admonish info
In the Snap‑and‑Chat construction, we also have BFT block proposals committing to $\Pi_{\lc}$ snapshots (top of right column of [[NTT2020](https://eprint.iacr.org/2020/1091.pdf), page 7]):
> In addition, $\ch^t_i$ is used as side information in $\Pi_{\bft}$ to boycott the finalization of invalid snapshots proposed by the adversary.

This does not cause any circularity, because each protocol only commits to *earlier* blocks of the other. In fact, BFT validators have to listen to transmission of $\Pi_{\lc}$ block headers anyway, so that *could* be also the protocol over which they get the information needed to make and broadcast their own signatures or proposals. (A possible reason not to broadcast individual signatures to all nodes is that with large numbers of validators, the proof that a sufficient proportion of validators/stake has signed can use an aggregate signature, which could be much smaller. Also, $\Pi_{\lc}$ nodes only need to know about *successful* BFT block proposals.)
```

Now suppose that, in a Snap‑and‑Chat protocol, the BFT consensus finalizes a $\Pi_{\lc}$ snapshot that does not extend the snapshot in the previous block (which can happen if either $\Pi_{\bft}$ is unsafe, or $\Pi_{\lc}$ suffers a rollback longer than $\sigma$ blocks). In that case we will initially not be able to spend outputs from the old snapshot in the new chain. But eventually for some node $i$ that sees the header $H$ at the tip of its best chain at <span style="white-space: nowrap">time $t$,</span> $\LF(H)$ will be such that from then on (i.e. at <span style="white-space: nowrap">time $u \geq t$),</span> $\LOG_{\fin,i}^u$ includes the output that we want to spend. This assumes *liveness* of $\Pi_{\lc}$ and *safety* <span style="white-space: nowrap">of $\Pi_{\bft}$.</span>

That is, including a reference to a recent final BFT block in $\Pi_{\lc}$ block headers both incentivizes nodes to propagate this information, *and* can be used to solve the “spending finalized outputs” problem.

Optionally, we could incentivize the block producer to include the latest information it has, for example by burning part of the block reward or by giving the producer some limited mining advantage that depends on how many $\Pi_{\lc}$ blocks back the finalization information is.

This raises the question of how we measure how far ahead a given block is relative to the finalization information it provides. As we said before, $\LOG_{\fin,i}^t$ is a sequence of transactions, not blocks. The transactions will in general be in a different order, and also some transactions from $\ch_i^t$ may have been omitted from $\LOG_{\fin,i}^t$ (and even $\LOG_{\da,i}^t$) because they were not contextually valid.

```admonish info
In [Crosslink 2](./construction.md), we will sidestep this problem by avoiding the need for sanitization — that is, $\LOG_{\fin,i}^t$ will correspond exactly to a chain of blocks that is a prefix <span style="white-space: nowrap">of $\ch_i^t$.</span> Actually we use the notation $\localfin_i^t$ to reflect the fact that it is a bc‑chain, not a sequence of bc‑transactions. This invariant is maintained statefully on each <span style="white-space: nowrap">node $i$:</span> any rollback past $\localfin_i^t$ will be ignored. If a new $\localfin_i^t$ would conflict with the old one, the node will refuse to use it. This allows each node to straightforwardly measure how many blocks $\ch_i^t$ is ahead of $\localfin_i^t$ as the difference in heights. Since this document is intended to explain the development of Crosslink from Snap‑and‑Chat, here we describe the more complicated approach that we originally came up with for Crosslink 1 — which also serves to motivate the simplification in Crosslink 2.
```

Assume that a block unambiguously specifies its ancestor chain. For a <span style="white-space: nowrap">block $H$, define:</span>$$
\tailhead(H) := \lastcommonancestor(\snapshotlf{H}, H) \\
\finalitydepth(H) := \height(H) - \height(\tailhead(H))
$$

Here $\LF(H)$ is the BFT block we are providing information for, and $\snapshotlf{H}$ is the corresponding $\Pi_{\lc}$ snapshot. For a node $i$ that sees $\LF(H)$ as the most recent final BFT block at <span style="white-space: nowrap">time $t$,</span> $\LOG_{\fin,i}^t$ will definitely contain transactions from blocks <span style="white-space: nowrap">up to $\tailhead(H)$,</span> but usually will not contain subsequent transactions <span style="white-space: nowrap">on $H$’s fork.</span>

```admonish info
Strictly speaking, it is possible that a previous BFT block took a snapshot $H'$ that is <span style="white-space: nowrap">between $\tailhead(H)$ and $H$.</span> This can only happen if there have been at least two rollbacks longer than <span style="white-space: nowrap">$\sigma$ blocks</span> (i.e. we went more than <span style="white-space: nowrap">$\sigma$ blocks</span> <span style="white-space: nowrap">down $H$’s fork</span> <span style="white-space: nowrap">from $\tailhead(H)$,</span> then reorged to more than <span style="white-space: nowrap">$\sigma$ blocks</span> <span style="white-space: nowrap">down $\snapshotlf{H}$’s fork,</span> then reorged again to $H$’s fork). In that case, the finalized ledger would already have the non-conflicting transactions from blocks <span style="white-space: nowrap">between $\tailhead(H)$ and $H'$</span> — and it could be argued that the correct definition of finality depth in such cases is the depth of $H'$ <span style="white-space: nowrap">relative to $H$,</span> not <span style="white-space: nowrap">of $\tailhead(H)$</span> <span style="white-space: nowrap">relative to $H$.</span>

However,
* The definition above is simpler and easier to compute.
* The effect of overestimating the finality depth in such corner cases would only cause us to enforce Stalled Mode slightly sooner, which seems fine (and even desirable) in any situation where there have been at least two rollbacks longer than <span style="white-space: nowrap">$\sigma$ blocks.</span>

By the way, the “tailhead” of a tailed animal is the area where the posterior of the tail joins the rump (also called the “dock” in some animals).
```

We could alternatively just rely on the fact that some proportion of block producers are honest and will include the latest information they have. However, it turns out that having a definition of finality depth will also be useful to enforce going into Stalled Mode.

Specifically, if we accept the above definition of finality depth, then the security property we want is

```admonish success "Definition"
**Bounded hazard-freeness** for a finality gap bound of $L$ blocks: There is never, for any <span style="white-space: nowrap">node $i$</span> at <span style="white-space: nowrap">time $t$,</span> observed to be a more-available ledger $\LOG_{\da,i}^t$ with a hazardous transaction that comes from <span style="white-space: nowrap">block $H$ of $\ch_i^t$</span> such that <span style="white-space: nowrap">$\finalitydepth(H) > L$.</span>
```

```admonish info
This assumes that transactions in the non-finalized suffix  $\LOG_{\da,i}^t \setminus \LOG_{\fin,i}^t$ come from blocks <span style="white-space: nowrap">in $\ch_i^t$.</span> In Snap‑and‑Chat they do by definition, but ideally we wouldn’t depend on that. The difficulty in finding a more general security definition is due to the ledgers in an Ebb‑and‑Flow protocol being specified as sequences of transactions, so that a depth in the ledger would have only a very indirect correspondence to time. We could instead base a definition on timestamps, but that could run into difficulties in ensuring timestamp accuracy.

Another possibility would be to count the number of coinbase transactions in $\LOG_{\da,i}^t \setminus \LOG_{\fin,i}^t$ before the hazardous transaction. This would still be somewhat ad hoc (it depends on the fact that coinbase transactions happen once per block and cannot conflict with any other distinct transaction).

In any case, if $\finalitydepth$ sometimes overestimates the depth, that cannot weaken this security definition.
```

Note that a node that is validating a chain $\ch_i^t$ must fetch all the chains referenced by BFT blocks reachable from it (back to an ancestor that it has seen before). In theory, there could be a partition that causes there to be multiple disjoint snapshots that get added to the BFT chain in quick succession. However, in practice we expect such long rollbacks to be rare if $\Pi_{\lc}$ is meeting its security goals.

Going into Stalled Mode if there is a long finalization stall helps to reduce the cost of validation when the stall resolves. That is, if there is a partition and nodes build on several long chains, then in unmodified Snap‑and‑Chat, it could be necessary to validate an arbitrary number of transactions on each chain when the stall resolves. Having only coinbase transactions after a certain point in each chain would significantly reduce the concrete validation costs in this situation.

Nodes should not simply trust that the BFT blocks are correct; they should check validator signatures (or aggregate signatures) and finalization rules. Similarly, $\Pi_{\lc}$ snapshots should not be trusted just because they are referenced by BFT blocks; they should be fully validated, including the proofs‑of‑work.

It is also possible for a snapshot reference to include the subsequent <span style="white-space: nowrap">$\sigma$ block headers,</span> which are guaranteed to be available for a confirmed snapshot. Having all nodes validate the proofs‑of‑work in these headers is likely to significantly increase the work that an attacker would need to perform to cause disruption under a partial failure of either <span style="white-space: nowrap">$\Pi_{\bft}$’s or $\Pi_{\lc}$’s</span> security properties.

```admonish info
Note that [[NTT2020]](https://eprint.iacr.org/2020/1091.pdf) (bottom of right column, page 9) makes a safety assumption about $\Pi_{\lc}$ in order to prove the consistency of $\LOG_{\fin}$ with the output <span style="white-space: nowrap">of $\Pi_{\lc}$:</span>

> As indicated by Algorithm 1, a snapshot of the output of $\Pi_{\lc}$ becomes final as part of a BFT block only if that snapshot is seen as confirmed by at least one honest node. However, since $\Pi_{\lc}$ is safe [i.e., does not roll back further than the confirmation depth <span style="white-space: nowrap">$\sigma$],</span> the fact that one honest node sees that snapshot as confirmed implies that every honest node sees the same snapshot as confirmed.

We claim that, while this may be a reasonable assumption to make for parts of the security analysis, in practice we should always require any adversary to do the relevant amount of Proof‑of‑Work to construct block headers that are plausibly confirmed. This is useful even though we cannot require, for every possible attack, that it had those headers at the time they should originally have appeared.
```

## Enforcing Finalization Availability and Stalled Mode

The following idea for enforcing finalization availability *and* a bound on the finality gap was originally conceived before we had switched to advocating the Stalled Mode approach. It’s simpler to explain first in that variant.

Suppose that for an <span style="white-space: nowrap">$L$-block availability bound,</span> we required each block header to include the information necessary for a node to finalize to <span style="white-space: nowrap">$L$ blocks back.</span> This would automatically enforce a chain stall after the availability bound without any further explicit check, because it would be impossible to produce a block after the bound.

Note that if full nodes have access to the BFT chain, knowing $\LF(H)$ is sufficient to tell whether the correct version of any given BFT block in <span style="white-space: nowrap">$\LF(H)$’s</span> ancestor chain has been obtained.

Suppose that the finality gap bound is <span style="white-space: nowrap">$L$ blocks.</span> Having already defined $\finalitydepth$, the necessary $\Pi_{\lc}$ consensus rule is attractively simple:

```admonish success "Consensus rule"
For every $\Pi_{\lc}$ block $H$, $\finalitydepth(H) \leq L$.
```

To adapt this approach to enforce Stalled Mode instead of stalling the chain, we can allow the alternative of producing a block that follows the Stalled Mode restrictions:

```admonish success "Consensus rule"
For every $\Pi_{\lc}$ block $H$, <font color="#5050f0">either</font> $\finalitydepth(H) \leq L$<font color="#5050f0">, or $H$ follows the Stalled Mode restrictions</font>.
```

Note that Stalled Mode will be exited automatically as soon as the finalization point catches up to within <span style="white-space: nowrap">$L$ blocks</span> (if it does without an intentional rollback). Typically, after recovery from whatever was causing the finalization stall, the validators will be able to obtain consensus on the same chain <span style="white-space: nowrap">as $\LOG_{\da}$,</span> and so there will be no rollback (or at least not a long one) <span style="white-space: nowrap">of $\LOG_{\da}$.</span>

```admonish info
An earlier iteration of this idea required the finalization information to be included in $\Pi_{\lc}$ block headers. This is not necessary when we assume that full nodes have access to the BFT chain and can obtain arbitrary BFT blocks. This also sidesteps any need to relax the rule in order to bound the size of $\Pi_{\lc}$ block headers. $\Pi_{\lc}$ block producers are still incentivized to make the relevant BFT blocks available, because without them the above consensus rule cannot be checked, and so their $\Pi_{\lc}$ blocks would not be accepted.

There is, however, a potential denial‑of‑service attack by claiming the existence of a BFT block that is very far ahead of the actual BFT chain tip. This attack is not very serious as long as nodes limit the number of BFT blocks they will attempt to obtain in parallel before having checked validator signatures.
```

### Comment on security assumptions

Consider Lemma 5:
> Moreover, for a BFT block to become final in the view of an honest <span style="white-space: nowrap">node $i$</span> <span style="white-space: nowrap">under $(\mathcal{A}^∗_2, \mathcal{Z}_2)$,</span> at least one vote from an honest node is required, and honest nodes only vote for a BFT block if they view the referenced LC block as confirmed.

The stated assumptions are:

> $(\mathcal{A}_2(\beta), \mathcal{Z}_2)$ formalizes the model of **P2**, a synchronous network under dynamic participation, with respect to a bound $\beta$ on the fraction of awake nodes that are adversarial:
> * At all times, $\mathcal{A}_2$ is required to deliver all messages sent between honest nodes in at most $\Delta$ slots.
> * At all times, $\mathcal{A}_2$ determines which honest nodes are awake/asleep and when, subject to the constraint that at all times at most fraction $\beta$ of awake nodes are adversarial and at least one honest node is awake.

$(\mathcal{A}^∗_2, \mathcal{Z}_2)$ is defined as $(\mathcal{A}_2(\frac{1}{2}, \mathcal{Z}_2))$.

Now consider this statement and figure:

> Even if $\Pi_{\bft}$ is unsafe (Figure 9c), finalization of a snapshot requires at least one honest vote, and thus only valid snapshots become finalized.
>
> ![Figure 9 of [NTT2020]](./NTT2020-Figure-9.png)

This argument is technically correct but has to be interpreted with care. It only applies when the number of malicious nodes $f$ is such that $n/3 < f < n/2$. Here it is assumed that the same nodes are participating in the BFT and LC protocols, so that the proportion of malicious nodes $f/n$ is the same in both. What we are trying to do with Crosslink is to ensure that a similar conclusion holds even if $\Pi_{\bft}$ is completely subverted, i.e. the adversary has 100% of validators (but only < 50% of $\Pi_{\lc}$ hash rate).
