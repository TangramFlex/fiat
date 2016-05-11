Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.ExtendedLemmas
        CertifiedExtraction.ExtendedPropertiesOfTelescopes
        CertifiedExtraction.Extraction.BinEncoders.Basics.

Lemma IList_post_transform_TelEq :
  forall {av} {A bin : Type}
    (cache : Cache.Cache) (transformer : Transformer.Transformer bin)
    (A_encode : A -> Cache.CacheEncode -> bin * Cache.CacheEncode)
    (xs : list A) (base : bin) (env : Cache.CacheEncode)
    k__stream (tenv: _ -> Telescope av) ext,
    let fold_on b :=
        List.fold_left (IList.IList_encode'_body cache transformer A_encode) xs (b, env) in
    (forall a1 a2 b, tenv (a1, b) = tenv (a2, b)) ->
    TelEq ext
          ([[ret (fold_on Transformer.transform_id) as folded]]
             ::[[ k__stream ->> Transformer.transform base (fst folded) as _]] :: tenv folded)
          ([[ret (fold_on base) as folded]]
             ::[[ k__stream ->> fst folded as _]] :: tenv folded).
Proof.
  cbv zeta; intros * H.
  setoid_rewrite Propagate_anonymous_ret.
  rewrite (IList.IList_encode'_body_characterization _ _ _ _ base).
  destruct (List.fold_left _ _ _); simpl; erewrite H; reflexivity.
Qed.

Lemma IList_encode'_body_simpl :
  forall (cache : Cache.Cache) {av HD bin : Type} (transformer : Transformer.Transformer bin)
    f acc (head: HD) (tail: _ -> Telescope av) ext,
    TelEq ext
          ([[ ret (IList.IList_encode'_body cache transformer f acc head) as v ]] :: tail v)
          ([[ ret (f head (snd acc)) as v ]] :: tail (Transformer.transform (fst acc) (fst v), (snd v))).
Proof.
  intros; unfold IList.IList_encode'_body; destruct acc.
  rewrite TelEq_let_ret2; reflexivity.
Qed.
