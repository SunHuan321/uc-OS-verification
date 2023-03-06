# uc-OS-verification

## What is this repository for?
This project contains a case study for verification of memory management and mailbox modules for uc/OS-II. It uses PiCore, one of the state-of-the-art rely-guarantee reasoning frameworks for concurrent reactive systems (CRSs) to model and verify the functional correctness and invariant preservation for uc/OS-II.

## How do I get set up?
The project is developed by Isabelle/HOL 2018, latest version may need some slight adjustments. You can load theorems by dragging them in the Isabelle/HOL GUI

### ucOS_mem_mailbox
* kernel_spec : specification for kernel services of uc/OS-II at code level
* invariant : definition of invariants that must be maintained throughout the execution of kernel services
* func_cor_other: proof for tick and scheduler services
* func_cor_OSMemGet, func_cor_OSMemPut: proof for memory management services
* func_cor_OSMboxPost, func_cor_OSMboxPend, func_cor_OSMboxAccept : proof for mailbox services
* OS_kernel_sys : proof for the functional correctness of whole system
* OS_kernle_inv : proof for the invariant preservation of whole system
