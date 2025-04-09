---
  title: Crypto Proof Ladder
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

Welcome to the home page of the Crypto Proof Ladder, a gentle introduction to formal methods for cryptography.    Here, we bring together a set of examples for the formal analysis of cryptographic primitives and protocols. Our goal is to provide a set of cryptographic problems, presented in pdf notes in a way accessible to both cryptographers or formal methods people, as well as a set of solutions for those problems, using distinct tools from the computer-aided cryptography domain.

This might be of interest to you if:

 * you are a formal method curious cryptographer, you should be able to understand all the problems, and then use the multiple solutions to discover the multiple tools, what kind of guarantees we can obtain with them, see which tools is best suited for which kind of analysis, ...;
 * if you are cryptography curious formal verification researcher, you should be able to get a feel for the kind of guarantees cryptographers expects, and the variety of techniques that are currently used to get them;
 * if you are a tool developper, you can use this opportunity to showcase your tool, understand how it compares with others and learn from those, on a set of clearly defined examples.

We consider three separates set of problems focusing on

 * symmetric primitives;
 * asymmetric primitves;
 * protocols.
		
The project is a work-in-progress, we recommend that you start with the [protocols set](protocols.html) to discover its current state.
		
# Why it matters?

Doing security is hard. And doing provable security is even harder, with many examples of subtle errors hiding everywhere in the crypto proofs. Formal methods and computer-aided cryptography can help us increase the level of trust we can have in crucial security and privacy mechanisms. With formal methods, once you have a proof, you know that the proof is correct.

However, while we delegate trusting the proof to a tool, a core question remains: "what did we actually prove?" Formal methods can typically yield meaningless results in some cases, typically if the protocol model is in fact completely incorrect and does not match at all the real world. The guarantees we get can also be very diverse, and sometimes have subtles differences with the long standing habits of cryptographers.

For formal models to acutally bring trust to some crucial systems, we need has many experienced eyes as possible on them, to clearly understand and validate the protocol modeling, the threat model and the actual security statements. And we need to have a clear view of the limitation of each model, so that we can keep improving them. 

We hope this ressource can improve the overall communication and joint understanding between cryptographers, cryptography developers, and the formal method community.


# Who are we?

This work is an initiative pushed by the [HACS](https://www.hacs-workshop.org/) workshop, and stems from the collobaration between cryptographers, cryptography developers, formal methods folks.

