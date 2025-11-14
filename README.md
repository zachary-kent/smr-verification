# Supplementary material for BigAtomics

This contains the supplementary material for BigAtomics. It also contains the arifact for "Modular Verification of Safe Memory Reclamation in Concurrent Separation Logic" in `smr-verification`, and the proof of BigAtomics is embedded in this artifact. We respected the license provided by the original artifact. Within the `smr-verification` directory, the `CachedWaitFree` implementation is located in `theories/hazptr/code_cached_wf.v`, the specification of a BigAtomic object is located at `theories/hazptr/spec_big_atomic.v`, and the proof that `CachedWaitFree` satisfies this spec is located at `theories/hazptr/proof_cached_wf.v`. A closed proof that the implementation satisfies the spec can be found at the end of `theories/hazptr/closed_proofs.v`; everything not related to BigAtomics or CachedWaitFree in `closed_proofs.v` is prior work from the original artifact.

All of the other files are prior work from the original artifact, modulo some minor modifications. In particular, we modified `theories/hazptr/[code spec proof]_hazptr.v` to extend hazard pointers with support for protecting tagged values. We also created `theories/lang/lib/array.v`to contain helpers for arrays. Overall, the directory structure of the files we modified is as follows:

```
smr-verification/
├── README.md
└── theories/
    ├── hazptr/
    │   ├── code_cached_wf.v
    │   ├── spec_big_atomic.v
    │   ├── proof_cached_wf.v
    │   ├── closed_proofs.v
    │   ├── code_hazptr.v
    │   ├── spec_hazptr.v
    │   └── proof_hazptr.v 
    └── lang/
        └── lib/
            └── array.v
```

This artifact can be built by following the instructions in `smr-verification/README.md`. Note that, even while compiling in parallel, this will require a large amount of time: potentially upwards of 30 minutes on commodity laptops. This is due to the automation within the the proof of `theories/hazptr/proof_cached_wf.v`. Thus, your terminal may appear to hang, but it will eventually terminate. We suggest using RocqIDE or VSRocq to step through the file, as they support asynchronous batch compilation and the file will compile much faster.
