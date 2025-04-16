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

axiom [any] SIGverify_correct (x,y : message, k : skey) : g
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
programming style, with `let` bindings, conditional branching, but
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
    in(c, (y_pk : G,sign : bitstring));
    if SIGverify(sign, (x_pk,y_pk), s_pk) then
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
  let sign = snd(mA) in
  if SIGverify(< ofG(x_pk), ofG(y_pk)>, sign, s_pk) then
    let gCS = y_pk^x_sk  in
    let kC = Hash( ofG(gCS), kHash) in
    null.
```




### Multi-Set Rewriting based syntax

We can model an agent by providing its transition rules between one
state and another. This is how Tamarin models protocols, using
so-called Multi-Set Rewriting (MSR) rules. If we denote by
`StateC(C,x_sk)` the fact that a client `C` is in the intermediate
state of the protocol, we need to define a rule which can consume some
input, samples a fresh `x_sk` and send out the corresponding public
key. Tamarin relies on a set of builtin facts to enable this, with :


 *  `In(x)` which models the fact that an input of value `x` is
    available on the network and can be consumed by a transition rule;	
 *  `Fr(n)` which models the fact that a fresh value `n` is available
    and can be consumed by a transition rule. 	
 * `Out(t)` which models the fact that an output is sent over the network;

With this in mind, the first rule to initialize a client is as follows.

```CrossToolSyntax
(* Tamarin *)

rule Client_Init:
  let x_pk = 'g'^x_sk in
  [ Fr(~x_sk)]   (* if a fresh value x_sk is available *)
     -->
  [ Out(<x_pk>), StateC(C, x_sk) ]  
  (* we send the correspinding public key  out and create an intermediate client state. *)
```

To define the next and final client step, we also define an additional
fact `!Pk(S, s_pk)` which can be read by a rule and models the fact
that `s_pk` is the honestly produced public key of Server `S` (the `!`
prefix means that here we define a *persistent* fact, which can be
used an input to transition rules but will not be consumed). In addition, we
also need to be able to add the restriction that a transition can only be
executed if some check succeeds. We add to this end an `Eq(x,y)` event,
that we can use to lable transitions functions, and for which we
define that such an event can only occur when `x=y`.


```CrossToolSyntax
(* Tamarin *)

rule Client_Accepts:
  let
    m = <y_pk, serverSign>
    x_pk = 'g'^x_sk
    dh_output = y_pk^x_sk
    K_C = h(dh_output)
  in
  [ StateC(C, x_sk), 
  (* We consume the intermediate state produced by
    the previous rule *)
    !Pk(S, s_pk),
	(* We read the value of an available public key. *)
    In(m)
	(* we receive the actual message *)
	]
  --[  Eq(verify(serverSign, <x_pk, y_pk>, s_pk), true)]->
  [ ]

restriction Eq:
(* We express the restriction in a first-order temporal logic. *)
  "All x y #i. 
         Eq(x, y) @ #i  
		 (* Whenever at step i in some protocol
		 execution a rule with the label Eq(x,y) is raised. *)
               ==> x = y" (* then we must have x=y *)

```


::::: note

<span style="color: #0969da;">🗅 Note</span>

In Tamarin, some variables can be prefixed with a special symbol to
give some additional details to the tool about their possible
values. A `$` prefix denotes a publicly known constant, will `~n`
denotes a fresh value obtained through a `Fr(~n)` fact. In the actual
protocol modeling, the client and server identity `C` and `S` are in fact
be `$C` and `$S`, and `x_sk` would be `~x_sk`.

:::::


## Modeling the protocol

To finalize the definition of the protocol, it remains to model the
concrete scenario we are in:

 * with which server public key do  we initialize the client?
 * how many client/server sessions do we set up?
 * ...

In addition to the previous definitions for the Client we also defined
similar things for Servers, we can in the pi-calculus based tools directly
setup our scenarios by relying on a parallel composition operator `|`
and a replication operator `!` to spawn multiple sessions.

```CrossToolSyntax
(* Squirrel *)
process protocol = (
   (!_i
     (* instantiate parallel replications indexed by i *)
      Client(i))
   | 
   (!_S !_k Server(S,k))
   )
```
<a id="proverif-protocol"></a>
```CrossToolSyntax
(* Proverif *)
process
	!
	(
	(* Initiatialize a new server identity, under the ! replication *)
	new s_sk: skey;
	let s_pk = pk(s_sk) in
	out(c, s_pk);

	(* spawn for this identity an unbounded number of sessions *)
	! Server(s_sk,s_pk)	
	(* spawn an unbounded number of clients, using keys received as inputs *)
	( ! in(c,s_pk:pkey); Client(s_pk))   
```


CryptoVerif can also use the `|` operator to specify that an attacker
gets access to some oracles in parallel, and has the `for each`
instruction to replicate oracles.

```CrossToolSyntax
(* CryptoVerif *)
process
  (* the initial oracle the attacker will have access to *)
  Ostart() := 
    hf <-R hashfunction;  (* initialize the hash function. *)
    return ();
	(* after an empty return of this start oracle, the attacker gets
   	   access to the follow-up oracles. *)

    (
     (foreach iC <= NC do
      (* spawn an unbounded number of clients talking to anybody *)
      OInitClient(s_pkC:pkey) :=
         return ();
         run Client(hf, s_pkC)
     )
     |
     (foreach iS <= NS do
     (* spawn an unbounded number of servers *)
      OInitServer() :=
          let (s_sk: skey, s_pk: pkey) = keygen() in
	  return(s_pk);	  
  	     (
    	 (* and after having it initialized, 
		 spawn an unbounded number of sessions for this server *)
   	      foreach iS2 <= NS2 do
    	      run Server(hf, s_sk, s_pk))
	  )  
    )
```

On the Tamarin side, the protocol is directly given by the set of
rules we define, and any transition rule can be triggered at any time,
assuming its premises are met. Typically, the previously defined
`Client_Init` rule can directly be triggered an unbounded number of
times. To complete the protocol model,
we would only need to add rules for the server, and to define rules to
set up the public key infrastructure. This PKI could look like this, thus
enabling the execution of our second Tamarin rule `Client_Accepts`.


<a id="tamarin-protocol"></a>
```CrossToolSyntax
(* Tamarin *)

// Generate Server's long-term (s_sk, s_pk)
rule Generate_serverLtk:
  let pkS = pk(~s_sk) 
  in
  [ Fr(~s_sk) ]
  (* By consuming an available fresh value sk *)
  -->
  [ !Ltk($S, ~s_sk), 
  (* we store in the Ltk fact the secret key, that a server
    rule would later read *)
    !Pk($S, s_pk), 
	(* and we define the corresponding Pk fact storing the public key *)
    Out(s_pk) 
	(* and we output on the network the public key. *)
	]

```

# Attacker Model

In the presented tool, we always have an active attacker which
controls the network. However, its capabilities differ, the main split
being between the symbolic (Proverif/Tamarin) and the computational
(EasyCrypt/CryptoVerif/Squirrel) tools.


## Computational attacker

For tools that work in the computational model, we define the attacker
model by stating which computational/decisional problems are hard. Each tool
gives different ways to specify the usual cryptographic
axioms, such as UF-CMA, the ROM, or CDH.

In EasyCrypt, UF-CMA can be expressed almost literally as one would
see it written in a crypto paper, modulo a few syntactic tidbits.

```CrossToolSyntax
(* EasyCrypt *)
module UFCMA (S : SigScheme) (A : CMA_Adv) = {
(* Given S a signature Scheme and A some adversary. *)


  (* an integer to identify each generated key pair *)
  var n: int
  
  (* maps from integers to the corresponding key *)
  var pk_map: (int, pkey) fmap
  var sk_map: (int, skey) fmap

  (* the set of honestly signed messages. *)
  var q: (int * msg) fset

  (* We define some oracles *)
  module Oracles = {
  
    (* This oracle generates a keypair, and stores it in the key map. *)    
    proc gen() = {	
      var pk, sk;

      n <- n + 1;
      (pk, sk) <@ S.keygen();
      pk_map.[n] <- pk;
      sk_map.[n] <- sk;
      return pk;
    }

    (* This oracle uses key number j to sign message m *)
    proc sign(j, m) = {
      var sign, sk;
      var r <- None;

      if (0 < j <= n) {
	  (* if the key has been sampled *)
	  
        sk <- oget sk_map.[j];
        sign <@ S.sign(sk, m);
        r <- Some sign;
		(* We sign it *)
		
   	    (* and append to q the fact that m was signed with key j *)
        q <- q `|` fset1 (j, m);
      }
      return r;
    }
  }

 
  (* Final experiment definition *)
  proc run() = {
    var j, m, sign, pk;
    var b <- false;
    
	(* initialize n to 0 *)
    n <- 0;
	(* intialize the honeslty signed message list to empty. *)
    q <- fset0;
	(* Ask attacker A with access to Oracles to return a key
    identifier, a message and a signature. *)
    (j, m, sign) <@ A(Oracles).forge();
    if (0 < j <= n /\ (j, m) \notin q) {
	  (* if the key indentifier is valid and the message was never
      signed for this key. *)
      pk <- oget pk_map.[j];
	  (* the attacker wins, i.e. we return 1, if the signature does
         verifies. *)
      b <@ S.verify(pk, m, sign);
    }
    return b;
  }
}.
```


In CryptoVerif, we can have user-defined cryptographic axioms, where
we can model generic equivalences between two set of oracles that the
attacker has access to.  However, user-defined equivalences are later
on automatically used to make reductionist game-hops by CryptoVerif,
they thus often need to be specified with some optional arguments and
in a very specific and ad-hoc way amenable to its automation. We thus
do not give here the actual UF-CMA CryptoVerif definition, which is
not very user-friendly. As a toy example, let us rather consider that
we want to express that sampling a key seed and returning the
corresponding secret key is perfectly indistinguishable to directly
sampling a secret key.


```CrossToolSyntax
(* CryptoVerif *)

(* We define an equivalence of name `keygen` relating to function
    `skgen` *)
equiv(keygen(skgen))
    r <-R keyseed;   (* sampling a keyseed *)
	   Okey() := return(skgen(r)) 
	   (* and returning the corresponding sk *)
    <=(0)=> (* can be distinguished with at most probability 0 *)
    k <-R skey;   (* from sampling a secret key directly *)
	     Okey() := return(k).

```



Squirrel has two options to declare such axioms. It has a library of
builtins, and one can just write `signature SIGsign,SIGverify,pk` to
directly declare a UFCMA signature SIGsign. Alternatively, one can
write a subset user-defined axioms, by expressing the equivalence of
two given sets of oracles that the attacker has access to, similar in
spirit to CryptoVerif. However, the two sets of oracles are actually
defined as a single set, but using a `diff(x,y)` operator in some
places to specify that the left-side oracle uses `x` here and the
right-side oracle uses `y`.

```CrossToolSyntax
(* Squirrel *)

game UFCMA = {
  (* Defines on random secret key. *)
  rnd sk : skey;
  (* Initializes the empty list of signed messages. *)
  var l = empty_set;

 (* Give to the attacker the public key. *)
  oracle pk = {
    return pk(sk)
  }

  (* Give to the attacker access to a signing oracle. *)
  oracle sign x = {
    l := add x l;
    return SIGsign(x,sk)
  }


  (* Define the challenge oracle. *)
  oracle challenge s m = {
    return
      if not (mem m l) then
	    (* If the message is not in the list *)
       diff(SIGVerify(m,key), 
	        (* then the left hand side oracle which executes the
      verification *)
	        false)
			(* is indistinguishable from an attacker returning false. *)
      else true
  }
}.
```



## Symbolic attacker

In the symbolic world, the cryptography is assumed to be ideal, and
only the equations that we explicitly give may yield equalities
between terms. Typically, with the previous variants of our signature
definitions, `SIGsign(m,k)` for each `m` and `k` is a unique message,
that only can only compute if they know both `m` and `k`, and that
will never be equal to any other message, and that does not leak any
information about `m` and `k`. 

The attacker capabilities are then completely defined by the set of
equations we explicitly define, and what it sees over the network. At
its core, this is what enables a high-level of automation in this
level, as we can reason about the attacker knowledge by saturating the
messages sent over the network through the equations, and decide if it
can or not know some value.


::::: caution

<span style="color: #cf222e;">⚠ Caution</span>

It can be easy to make implicit assumptions that can go unnoticed in
the symbolic model. For instance, as we defined it `SIGsign(m,k)` does
not leak anything about the signed messages. This is not always the
case for all signatures, and we must add an addition function and
equation to model this fact, of the form `getmess(SIGsign(m,k))=m`.

:::::

::::: important

<span style="color: #8250df;">🖹 Important</span>

We keep here the presentation simple. Note that however, symbolic
models have recently been developed to capture in a fine-grained
fashion many primitives, typically capturing the low-order points of
X25519, the length-extension property of SHA2, and other subtle
properties of signatures, KEMs, AEADs,...

In addition, it also enables modeling cases where the attacker is in
fact stronger than in the usual computational model, for instance by
letting the attacker chose at run time the output values of a hash
function, as long as it does not make any collision.

Comparing the symbolic and the computational attacker is thus not
completely straightforward in some cases, and especially on big
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

In symbolic tools, we reason about the possible executions of events,
and can express that all executions satisfy some property, or that
some executions cannot occur. To allow for reasoning over the
executions, we add to our protocol definitions events, that agents may
raise at runtime. The list of events that occur in a given execution
form the trace of this execution, and we specify properties over the
traces in some dedicated logic.

### Authentication

For key-exchanges, it is natural to define two events, a
`ServerAccept(s_pk,x_pk,y_pk,k_S)` and a
`ClientAccept(s_pk,x_pk,y_pk,k_C)`, each executed by the corresponding
agent when terminating the protocol with the given values..

In ProVerif, we would typically add on the client side the event by
updating the client process definitions.


```CrossToolSyntax

(* ProVerif *)
let Client(s_pk : pkey) = 

    (...)

    (* Second message *)
    in(c, (y_pk : G,sign : bitstring));
    if SIGverify(sign, (x_pk,y_pk), s_pk) then
       let k_C = Hash( exp(y_pk,x_sk)) in       
       event ClientAccept(s_pk,x_pk,y_pk,k_C).
	   
```

In Tamarin, events are the labels of the rules.

```CrossToolSyntax
(* Tamarin *)

rule Client_Accepts:
  let
    m = <y_pk, serverSign>
    x_pk = 'g'^x_sk
    dh_output = y_pk^x_sk
    K_C = h(dh_output)
  in
  [ StateC(C, x_sk), 
    !Pk(S, s_pk),
    In(m)
	]
  --[  Eq(verify(serverSign, <x_pk, y_pk>, s_pk), true),
	   ClientAccept(C,S,s_pk,x_pk,y_pk,k_C)
	]->
  [ ]
```

Tamarin uses to specify security property the same first-order
temporal logic we saw before for the restriction. We can specify
lemmas, which are property that should hold on all possible
traces. It enables to naturally model the authentication property.

```CrossToolSyntax
(* Tamarin *)

lemma auth:
 "All s_pk, x_pk, y_pk, k_C #i
	   ClientAccept(C,S,s_pk,x_pk,y_pk,k_C)@i 
	   (* if client accepted at time i in the trace. *)
	    ==> Ex #j. j < i  &&
		    (* there exists another timepoint j before i *)
            ServerAccept(C,S,s_pk,x_pk,y_pk,k_S)@j 			
		    (* where a server accepted with the same parameters. *)
	]->
  [ ]
```

Intuitively, on the Tamarin model as we introduced it step by step, this property would
hold, as clients only use honest public keys obtained from the fact
`!Pk`.

In ProVerif, the lemma specification language is less generic. We
express authentication properties through so-called correspondence
queries, where the quantifiers over variables are implicit.

```CrossToolSyntax
(* ProVerif *)

(* Client-side authentication *)
query s_pk : pkey, x_pk,y_pk : G, k : bitstring; 
	(* universally quantified variable *)
      (* if a client accept at any point in time *)
      event(ClientAccept(s_pk,x_pk,y_pk,k))
         ==> (* then somewhere in the past *)
         event(ServerAccept(s_pk,x_pk,y_pk,k))
		(* there is a matching session*)
	    ).
```

However, this property does not hold! Indeed, recall that in our
[ProVerif protocol definition](#proverif-protocol), we allow clients
to run for any public key `s_pk` provided by the attacker over the
network. However, we can add an event to remember which public keys
are honest.

```CrossToolSyntax
(* Proverif *)
process
(* We define a variant of the process definitions. *)
    !
    (
    new s_sk: skey;
    let s_pk = pk(s_sk) in
	event HonestServer(s_pk);	
	(* We add an event for each honestly generated public keys. *)
    out(c, s_pk);
```
We then use it in our queries, to clarify that we only expect this to
hold when a client accepted with an honestly generated key.

```CrossToolSyntax
(* ProVerif *)

(* Client-side authentication *)
query s_pk : pkey, x_pk,y_pk : G, k : bitstring; 
	(* universally quantified variable *)
      (* if a client accept at any point in time *)
      event(ClientAccept(s_pk,x_pk,y_pk,k))
	  &&  event(HonestServer(s_pk))
	      (* and the s_pk key is honest *)
         ==> (* then somewhere in the past *)
         event(ServerAccept(s_pk,x_pk,y_pk,k))
		(* there is a matching session*)
	    ).
```

::::: caution

<span style="color: #cf222e;">⚠ Caution</span>

Correctly defining the public key infrastructure is one of the key
points of modeling protocols that can lead to very strong differences
in the quality of the final model. If we left the Tamarin model in its
current state, it would be a model of key-exchanges where there only
exists honest servers, and clients never try to contact any dishonest
server. Conversely, without the `HonestServer` event, our ProVerif
model was meaningless, in the sense that it was impossible to prove
any security property over it.

Another difference is that in ProVerif, we do not have a notion of
client or server identities, and only identify servers through their
public keys. In Tamarin, we use unique public identifiers `C` and
`S`. For our protocol, this does not change anything, but in scenarios
where for instance agents can dynamically register public key, the 
ProVerif model would not be suitable and we would have to add agents identifiers.

:::::


### Forward Secrecy

To model forward secrecy, we need to add to our protocol model the
fact that some `s_sk` secret keys might be compromised and leaked to
the attacker. Both in Tamarin and ProVerif, this is done by modeling
this inside the syntax of our protocol, almost like if the server
actually had a compromise command that the attacker could query on the
network and then obtain the secret key.

In ProVerif, we would simply add in parallel to our other processes a
single line compromise process.

```CrossToolSyntax
(* ProVerif *)

(...)
	(* on a dummy input, we give the attacker the power to compromise the public key. *)	
	| (in(c, =0); event CompromiseServer(s_pk); out(c,s_sk))
(...)	
```

In Tamarin, we simply add a new compromise rule, which uses the `!LTK`
fact in the key generation of our [Tamarin protocol definition](tamarin-protocol).

```CrossToolSyntax
(* Tamarin *)

// The attacker learns the server's long-term key
rule Compromise_LTK:
  [ !Ltk(S, ~sk)]
  (* Read some secret key *)
  --[CompromiseLtk(S, pk(~sk))]->
  [ Out(~sk) ]
```

To express secrecy properties, both tool rely on the fact that the
attacker may raise its own event in the trace when it can compute a
value. In Tamarin, this is denoted with the `K(x)` event, and we can
express forward secrecy as follows.


```CrossToolSyntax
(* Tamarin *)

lemma auth:
 "All C S s_pk, x_pk, y_pk, k_C #i #k
	   ClientAccept(C,S,s_pk,x_pk,y_pk,k_C)@i 
	   (* if client accepted at time i in the trace. *)
	   && K(k_C)
	   (* and the attacker knows the derived key. *)
	    ==> 
		(Ex #j. j < i && CompromiseLtk(S, s_pk))	
		(* then the corresponding public key of the corresponding
           server was leaked in the past. *)
	]->
  [ ]
```

In ProVerif, this is denoted with an `attacker(x)` event.

```CrossToolSyntax
(* ProVerif *)

(* Client-side authentication *)
query s_pk : pkey, x_pk,y_pk : G, k : bitstring; 
	(* universally quantified variable *)
      event(ClientAccept(s_pk,x_pk,y_pk,k))
      (* if a client accept at any point in time *)	  
	  &&  event(HonestServer(s_pk))
	  (* with an honest server *)
	  && attacker(k)
	  (* and the attacker knows the key *)
	      (* and the s_pk key is honest *)
         ==> (* then somewhere in the past *)
         event(CompromiseServer(s_pk))
		(* the key was compromised *)
	    ).
```

### Sanity checks

The Tamarin lemmas and ProVerif queries can be used to check that our
protocols are indeed executable. 


```CrossToolSyntax
(* ProVerif *)

query s_pk : pkey, x_pk,y_pk : G, k : bitstring; 
      event(ClientAccept(s_pk,x_pk,y_pk,k)). 
	  (* can the event be executed ? *)
	  
(* Tamarin *) 	  
lemma exec_c:
  exists-trace (* does there exists a trace such that *)
 "Ex C S s_pk, x_pk, y_pk, k_C #i
     (* there exists parameters and a timepoint i *)
     ClientAccept(C,S,s_pk,x_pk,y_pk,k_C)@i.
	 (* where a client accepts. *)
```

::::: caution

<span style="color: #cf222e;">⚠ Caution</span>

In symbolic protocols models, sanity checks are crucial! Indeed, going
back to the forward secrecy or authentication properties, they check
that for all traces, if some client accepts, something is verified. If
no clients can ever accept, for instance because we made a typo and
swapped the two pair elements `<x_pk,y_pk>` on the server side, those
queries could be trivially true!

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
