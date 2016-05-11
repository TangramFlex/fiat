Require Export
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.BinLib.FixInt.

Require Export
        Fiat.CertifiedExtraction.RemoveSkips
        Fiat.CertifiedExtraction.Extraction.BinEncoders.BinEncoders
        Fiat.CertifiedExtraction.Benchmarks.MicrobenchmarksSetup.

Unset Implicit Arguments.

Ltac _encode_prepare_cache :=
  may_alloc_head; (* Only create bindings for the cache once. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons (NTSome _) (ret (fst (Compose.compose _ _ _ _))) _ =>
              apply ProgOk_Add_snd_ret with (f := fun _ => Nil)
            end).

Ltac _encode_start_compiling :=
  match goal with
  | |- sigT _ => eexists;
               let H := fresh in
               intros H *; destruct H;
               apply RemoveSkips_ProgOk
  end.

Ltac compile_encoder_step :=
  (* try _encode_show_progress; *)
  match goal with
  | _ => _encode_start_compiling
  | _ => _encode_cleanup
  | _ => _encode_prepare_cache
  | _ => _encode_FixInt
  | _ => _encode_IList_compile
  | _ => _compile_CallWrite
  | _ => _compile_Read
  | _ => _compile_ReadConstantN
  | _ => _compile_CallAdd16
  | _ => _compile_CallListLength
  | _ => _compile_CallAllocString
  | _ => _compile_CallAllocEMap
  | _ => _compile_CallAllocDMap
  | _ => _compile_CallAllocOffset
  | _ => _compile_CallDeallocQuestion
  | _ => _compile_CallDeallocResource
  | _ => _compile_compose
  | _ => _compile_step
  end.

Ltac compile_encoder_t :=
  progress (repeat repeat compile_encoder_step).

Global Opaque Compose.compose.
Global Opaque Transformer.transform_id.
Global Opaque EncodeAndPad. (* FIXME move *)

Definition MicroEncoders_Env : Env ADTValue :=
  (GLabelMap.empty (FuncSpec _))
    ### ("ByteString", "New") ->> (Axiomatic BytesADTSpec.New)
    ### ("ByteString", "Push") ->> (Axiomatic BytesADTSpec.Push).
