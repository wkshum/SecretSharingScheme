 Lean program for the paper 
 
 **A Lean Formalization of Perfect Secret Sharing and Secure Distributed Matrix Multiplication**
 by K. W. Shum and C. W. Sung

- Formalize the notion of a secret sharing scheme with a general access structure.
- Show that the Shamir secret sharing scheme is an instance of this general scheme.
- Extend linear secret sharing scheme to distributed matrix multiplication

The Lean program is divided into 5 parts

1. Access structure
   
2. Secret sharing scheme
   
3. Shamir scheme
   
4. Disjoint access structure
 
5. Distributed hierarchy

A Lean Verso documentation can be found in [https://github.com/wkshum/SecretSharingScheme](https://wkshum.github.io/SecretSharingScheme/)

The programs are compiled using Mathlib 4.29.0.

The main file is SecretSharingScheme.lean
