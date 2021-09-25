Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.

Definition tm_enumerable := enumerable (fun k => ~ (TM.HaltTM 1) k).