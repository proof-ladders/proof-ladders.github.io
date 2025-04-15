---
  title: Protocols Proof Ladder
  pagetitle: Index
  mainpagetitle:
  navigation: false

  next_page:
  next_page_url:
  prev_page:
  prev_page_url:

  bibliography: biblio.bib
  csl: ieee.csl
  link-citations: true
 
---



The protocol repository is
[here](https://github.com/proof-ladders/protocol-ladder). The problem
set is presented in a [pdf
file](https://github.com/proof-ladders/protocol-ladder/blob/main/Notes/main.pdf),
we recommend to start the reading.


If you are familiar with formal methods, the [README of the protocol
repository](https://github.com/proof-ladders/protocol-ladder) gives
you the keys to navigate the set of proposed solutions. If you are
not, we give below an introductory step-by-step tutorial to the
analysis of one of the problems, with key insights into its modeling
using CryptoVerif [@cryptoverif], EasyCrypt [@easycrypt], ProVerif
[@proverif], Tamarin [@tamarin] and Squirrel [@squirrel]. We present
how one thinks about modeling a protocol in a formal way, by going
through the signed Diffie Helman key-exchange (problem 2). We assume
that people are familiar with finite groups, signatures and hash
functions.



# Modeling the protocol  (⏳ 🚧 WIP 🚧 ⏳)

To model a protocol, we have to model the computations made by a given
agent, how it receives/send values over the network, and then define
concrete execution scenarios where multiple agents can interact
together.


## Abstract functions and domains

In any model, we start by specifying at which level of abstraction we
are going to work for the primitives and computations made by our
protocol agents. This part can be seen as defining the interface of a
library that our protocol relies on. When faced with a real word
example, we already have several choices. Do I model my hash function
as a single unary abstract hash function, or as a hmac based on an
abstract hash function, or a hmac based on a fixed block iterated hash
function, and so on. For our problem, which is a high-level
specification, we already have the layer of abstraction, we need to
define abstract signatures, hash functions and a DH group, and not
specify more than that how they might actually be instantiated.


::::: note

<span style="color: #0969da;">🗅 Note</span>

In this first step, we only care about modeling correctness
conditions of those primitives, so that our protocol does execute,
security notions will be discussed later. 

:::::


Let's consider the case of signatures. We have to define the way to
sample keys. Already, many small variants appear depending on the
tools capabilities. While those differences might not look very deep,
they can lead to subtle differences in the final guarantees, we thus
take the time to brieffly go through them. EasyCrypt can define
abstract functions that can be either deterministic or probabilistic,
we only have to define domains for the public keys, private keys,
signatures and messages, and then say that a signature has the three
desired algorithms of the expected types.


```CrossToolSyntax
(* EasyCrypt *)
type pkey, skey, sig, msg.

module type SigScheme = {
  proc keygen(): pkey * skey               
  (* from no arguments, probabilistic procedure returns a pair of type pkey * skey *)
  
  proc sign(_: skey, _: msg): sig
  proc verify(_: pkey, _: msg, _: sig): bool
}.
```
Interestingly, some tools that typically cannot prove executability
properties (for sanity checks) do not need to declare the correctness
property of the signature and verify functions, as they might not be
needed to actually prove the security. In the EasyCrypt example, the
correctness is typically not given. 

The other tools can only define abstract deterministic functions
(which is actually usefull on the proving side), so we have to make
explicit the randomness as parts of the argument. Typically, the
keygen function needs a new seed, for which we also define a domain,
and the signature also need an addition source of randomness. 
Both in Squirrel and CryptoVerif, declaratations are rather similar
and we can use an equation to define the correctness of the
verification function.



```CrossToolSyntax
(* CryptoVerif *)

type keyseed [large,fixed].
(* [large,fixed] => all elements are, given a security parameter, of a
fixed length, and with negligible chance of collisions. *)

type pkey [bounded]. (* [bounded] => all elements have a maximal length. *)
type skey [bounded].

fun skgen(keyseed):skey.
fun pkgen(keyseed):skey.

(* bitstring is a default builtin type *)
fun SIGsign(bitstring, skey): bitstring.
fun SIGverify(bitstring, pkey, bitstring): bool.

equation forall m:bitstring, r:keyseed; 
	SIGverify(m, pkgen(r), SIGsign(m, skgen(r))) = true.
```

In some tools, we tend to consider that we don't have a seed used to
derive keypairs, but rather that we sample uniformly at random a
secret key, and have a way to derive a public key from a secret
key. The actual declaration looks like this.

```CrossToolSyntax
(* Squirrel *)

type skey [large].
type pkey.

(* message is a default builtin type *)
abstract pk : skey -> pkey.
abstract SIGsign : message * skey -> message.
abstract SIGverify : message * message * pkey -> bool.

axiom [any] SIGverify_correct (x,y:message,k : skey) : 
     SIGverify(x, SIGsign(x,k), pk(k)).
```


This model is also common for ProVerif/Tamarin, and more generally the
symbolic model.

```CrossToolSyntax
(* ProVerif *)
type skey.
type pkey.

fun pk(skey):pkey.

fun SIGsign(bitstring, skey): bitstring.

reduc forall m: bitstring, k: skey; 
	SIGverify(SIGsign(m,k),m, pk(k)) = true. 
(* SIGverify is directly defined through the equation is verifies. *)

```

Tamarin is a corner case where we do not define any specific domain or
type, everything is of the same message type, one defines functions
with their arity, and then the equations over them.

```CrossToolSyntax
(* Tamarin *)

functions: skgen/1, pkgen/1, SIGsign/2, SIGverify/3, True/0
equations: SIGverify(SIGsign(m, skgen(seed)),m, pkgen(seed)) = True
```

::::: tip

<span style="color: #1a7f37;">💡 Tip</span>

Most tools offer builtins supports or library, we don't have to
redefine everything from scratch all the time.

:::::


## Modeling an agent

We have modeled the library that agents will have access to. We now
need to model how one session of an agent may sequentially execute the
protocol, and notably receive or send messages on the network. The
network is assumed to be attacker controlled, we thus do not make a
distinction between arguments received over a network or given by an
attacker. 


### Oracle/procedure based

CryptoVerif EasyCrypt

### Pi-calculus style

ProVerif Squirrel

### MSR based

Tamarin


## Modeling the protocol



# Security definitions

## Symbolic security definitions

Tamarin/Proverif, trace based

## Computational security definitions

### Monolithic AKE style security

Easycrypt + notes

### Split trace and indistinguishability based style

Squirrel/CryptoVerif

# Proving 

## Automated

ProVerif/Tamarin/CryptoVerif

## Interactive Proofs

### Logic based reasoning

Easycrypt/Squirrel

### Restricted tactic applications

CryptoVerif/Tamarin

### Heuristic guidance

Tamarin/ProVerif



# WIP guidelines for style



::::: note

<span style="color: #0969da;">🗅 Note</span>

This is a note.

:::::



::::: tip

<span style="color: #1a7f37;">💡 Tip</span>

This is a tip.

:::::


::::: important

<span style="color: #8250df;">🖹 Important</span>

This is a warning.

:::::


::::: warning

<span style="color: #9a6700;">⚠ Warning</span>

This is a warning.

:::::


::::: caution

<span style="color: #cf222e;">⚠ Caution</span>

This is a warning.

:::::



# References
