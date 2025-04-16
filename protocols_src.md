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
we recommend starting the reading with the pdf, then coming back here.


If you are familiar with formal methods, the [README of the protocol
repository](https://github.com/proof-ladders/protocol-ladder) gives
you the keys to navigate the set of proposed solutions. If you are
not, we give below an introductory step-by-step tutorial to the
analysis of one of the problems, with key insights into its modeling
using CryptoVerif [@cryptoverif], EasyCrypt [@easycrypt], ProVerif
[@proverif], Tamarin [@tamarin] and Squirrel [@squirrel]. We present
how one thinks about modeling a protocol in a formal way, by going
through the signed Diffie Hellman key-exchange (problem 2). We assume
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
as a single unary abstract hash function, or as a HMAC based on an
abstract hash function, or a HMAC based on a fixed block iterated hash
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
take the time to briefly go through them. EasyCrypt can define
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
(which is actually useful on the proving side), so we have to make
explicit the randomness as parts of the argument. Typically, the
keygen function needs a new seed, for which we also define a domain,
and the signature also need an addition source of randomness. 
Both in Squirrel and CryptoVerif, declarations are rather similar
and we can use an equation to define the correctness of the
verification function.



```CrossToolSyntax
(* CryptoVerif *)

type keyseed [large,fixed].
(* [large,fixed] => all elements are, given a security parameter, of a
fixed length, and with negligible chance of collisions. *)

type pkey [bounded]. (* [bounded] => all elements have a maximal length. *)
type skey [bounded].

fun skgen(keyseed) : skey.
fun pkgen(keyseed) : skey.

(* bitstring is a default builtin type *)
fun SIGsign(bitstring, skey): bitstring.
fun SIGverify(bitstring, pkey, bitstring): bool.

equation forall m : bitstring, r : keyseed; 
	SIGverify(SIGsign(m, skgen(r)), m, pkgen(r)) = true.
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

axiom [any] SIGverify_correct (x,y : message, k : skey) : 
     SIGverify(SIGsign(x,k), x, pk(k)).
```


This model is also common for ProVerif/Tamarin, and more generally the
symbolic model.

```CrossToolSyntax
(* ProVerif *)
type skey.
type pkey.

fun pk(skey) : pkey.

fun SIGsign(bitstring, skey) : bitstring.

reduc forall m : bitstring, k : skey; 
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

Most tools offer builtin supports or library, we don't have to
redefine everything from scratch all the time.

:::::


## Modeling an agent

We have modeled the library that agents will have access to. We now
need to model how one session of an agent may sequentially execute the
protocol, and notably receive or send messages on the network. The
network is assumed to be attacker controlled, we thus do not make a
distinction between arguments received over a network or given by an
attacker. 

::::: important

<span style="color: #8250df;">🖹 Important</span>

In the remaining code snippets, we assume that all declarations have
taken place, we thus have functions to compute Hash() and DH
operations, as well as corresponding types. We do not detail it, and
use explicit names everywhere.

:::::


::::: caution

<span style="color: #cf222e;">⚠ Caution</span>

For this part, tools have disparate input languages with distinct
philosophy, we present the three main variants below. The two main
couple of points to look for are:

 * how are new random values sampled?
 * how do I send or receive values over the network?


:::::


### Oracle/procedure based

One can define an agent through a set of oracles given to the
attacker. Each oracle model one input/output action of an agent, where
the inputs of the oracle are the inputs received over the network, and
the return value of the oracle.

A multiple step agent is defined by "composing" sequentially some
oracles, where the follow-up oracle inherits the state of the previous
ones. For the Signed DH protocol, we need two oracles for the client
as it receives two inputs, and a single one for the server.


This syntax is close to what cryptographers use, and is typically used
in CryptoVerif and EasyCrypt.



```CrossToolSyntax
(* CryptoVerif *)

(* We declare an explicit function to generate DH keypairs. *)
letfun DHkeygen() =
       a <-R Z;     (* this samples in the exponents Z. *)
       (a, exp(g,a)).

(* Client process *)
(* We declare a macro parametrized by a Server public key 
and a hash function, we'll see how to instantiate it later on. 
*)

let Client(hf : hashfunction, s_pkC : pkey) =
  (* First oracle, that does not have any input. *)
  OC1() :=
    let (x_sk : Z, x_pk : G) = DHkeygen() in
    return(x_pk);
	
    (* Second oracle, in sequential composition. *)
    (* Directly expects two arguments, rather than a pair. *)
    OC3(y_pk : G, s : bitstring) :=
      if SIGverify(s, msg2(x_pk, y_pk), s_pkC) then    
		kC <- Hash(hf, exp(y_pk, x_sk));
	    0.
```

::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

EasyCrypt syntax examples

:::::


### Pi-calculus style

To model agents, a pi-calculus dialect makes us write in an imperative
programming style, with `let` bindings, conditional branchings, but
also add two commands for network interactions, `in(c,x)` and `out(c,t)`, which models
receiving a value over the network and binding it to variable `x` or
sending out value `t` on the network. The value `c` is meant to model
a particular channel. Channels can be useful to model secret
communications between agents, otherwise, having a single public
channel is often enough. The last pi-calculus command is `new x :
type`, which binds variable `x` to a new value in the type. This is
akin to the sampling of a fresh value. We can model the client side 
protocol as follows in ProVerif.


```CrossToolSyntax
(* ProVerif *)

(* We declare an explicit function to generate DH keypairs. *)
letfun DHkeygen() =
       new a : Z; (* this samples a new value in the exponents. *)
       (a, exp(g,a)).
	   
(* Client process *)
(* We declare a macro parametrized by a Server public key, we'll see
how to instantiate it later on. *)

let Client(s_pk : pkey) = 

    (* First message *)	  
    (* No input needed *)
    let (x_sk : Z, x_pk : G) = DHkeygen() in
    out(c, x_pk);

    (* Second message *)
	(* we directly do some pattern matching on the input. *)
    in(c, (y_pk : G,sig : bitstring));
    if SIGverify(sig, (x_pk,y_pk), s_pk) then
       let k_C = Hash( exp(y_pk,x_sk)) in       
       0.

```

Squirrel syntax has mainly two differences. First, because we can only
receive and send messages of type `message`, and thus have to add
explicit type conversion functions (akin to
serialization/deserialization functions). Second, in Squirrel, random
values are represented as "names", that can be indexed, e.g. by a
session identifier.  Instead of sampling `x_sk` in the i-th Session of
the Client, it will directly use the value `x_sk i`. This is
equivalent to assuming that all secret values were pre-computed at the
beginning of the universe (akin to eager sampling), and that we stored
in an array `x_sk` the list of the ephemeral of all clients.




```CrossToolSyntax
(* Squirrel *)

(* We declare the names for the clients. *)
(* ephemerals for Client  *)
name x_sk : index -> Z.
	   
(* Client process *)
(* We declare a macro parametrized by a session identifier, which is a
replication index, we'll see how to instantiate it later on. *)

process Client (i : index) =
  (* We receive some server public key *)
  (* We cannot pass this as argument to the Client macro, this is not
  a technical limitation, just need some more implementation. *)
  in(c, s_pk);

  (* We compute our ephemeral *)
  let x_sk = x_sk i in  (* we use the i-th value of the array x_sk. *)
  let x_pk = gen^x_sk in

  out(c, ofG(x_pk));

  in(c, mA);
  let y_pk = toG(fst(mA)) in
  let sig = snd(mA) in
  if SIGverify(< ofG(x_pk), ofG(y_pk)>, sig, s_pk) then
    let gCS = y_pk^x_sk  in
    let kC = Hash( ofG(gCS), kHash) in
    null.
```




### MSR based

::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

MSR core ides + Tamarin snippet

:::::


## Modeling the protocol

To finalize the definition of the protocol, it remains to model the
concrete scenario we are in:

 * with which server public key do  we initialize the client?
 * how many client/server sessions do we set up?
 * ...

# Attacker Model

In the presented tool, we always have an active attacker which
controls the network. However, its capabilities differ, the main split
being between the symbolic (Proverif/Tamarin) and the computational
(EasyCrypt,CryptoVerif/Squirrel) tools.


## Computational attacker

::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

Very quick description (we assume some crypto knowledge). 
Give
snippets of uf-cma user defined axioms for EasyCrypt/CryptoVerif. Mention dedicated
tactics for Squirrel + user-defined functions.

:::::



## Symbolic attacker

In the symbolic world, the cryptography is assumed to be ideal.

::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

Symbolic model core ideas.

:::::

::::: important

<span style="color: #8250df;">🖹 Important</span>

We keep here the presentation simple. Note that however, symbolic
models have recently been developped to capture in a fine-grained
fashion many primitives, typically capturing the low-order points of
X25519, the length-extension property of SHA2, and other subtle
properties of signatures, KEMs, AEADs,...

In addition, it also enables modeling cases where the attacker is in
fact stronger than in the usual computational model, for instance by
letting the attacker chose at run time the output values of a hash
function, as long as it does not make any collision.

Comparing the symbolic and the computational attacker is thus not
compltely straigthforward in some cases, and especially on big
protocols where computational proofs are out of reach.

:::::


# Security definitions

We now turn to actually modeling the security definitions. 


::::: caution

<span style="color: #cf222e;">⚠ Caution</span>

Even tools that model the attacker in the same way may capture the
security with subtle differences, in how secret keys can be
compromised, or with different ways of modelling authentication or
secrecy. Clearly understanding this when reading a model is one of the
main challenge.

:::::


## Symbolic security definitions


::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

Notion of events and attacker knwoledge, 
model compromise inside the protocol model,
snippets of ProVerif queries + Tamarin lemmas.

:::::


## Computational security definitions

### Monolithic AKE style security

::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

High level summary of AKE notes, link to doc, snippets of easycrypt?

:::::


### Split trace and indistinguishability based style


::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

Describe the mix approach, both with trace based dedicated
authentication queries, and some indistinguishability based secrecy
queries.

snippets of CryptoVerif / Squirrel queries.

:::::





# Proving 

::::: tip

<span style="color: #1a7f37;">💡 Tip</span>

If your only goal was to better understand what kind of guarantees are
actually provided by the different models or tools, you can stop here!

:::::

We now brieffly delve into how the tools are proved.

## Automated

::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

Describe the automated approach, ProVerif Tamarin

A little bit CryptoVerif

:::::



### Heuristic guidance


::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

Use of helper lemmas in Tamarin/ProVerif
oracles, additional params.

:::::



## Interactive Proofs

### Logic based reasoning

::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

Easycrypt/Squirrel

:::::


### Restricted tactic applications


::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

CryptoVerif/Tamarin interactive mode

:::::



# Additional ressources

That's it!

Hopefully, you should now be able to browse the repository and understand at
least at a high-level the models. If you want to delve deeper into one
of the tools, here are for each some additional ressources.



::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

Add links to doc/manual/tutorial for tools!

:::::

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


::::: todo

<span style="color: ##fffd34;">⚙ WIP/TODO </span>

This is a TODO.

:::::





# References
