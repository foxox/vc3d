axiom $arch_ptr_size == 8;

axiom $arch_spec_ptr_start == $max.u8;

const unique ^$##thread_id: $ctype;

axiom $def_math_type(^$##thread_id);

type $##thread_id;

const unique ^$##club: $ctype;

axiom $def_math_type(^$##club);

type $##club;

const unique ^Pair: $ctype;

axiom $is_span_sequential(^Pair);

axiom $def_struct_type(^Pair, 8, false, false);

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2(#s1, #s2, #p, ^Pair) } $inv2(#s1, #s2, #p, ^Pair) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2_without_lemmas(#s1, #s2, #p, ^Pair) } $inv2_without_lemmas(#s1, #s2, #p, ^Pair) == $set_eq($owns(#s2, #p), $set_empty()));

axiom (forall p: $ptr, q: $ptr, s: $state :: { $in(q, $composite_extent(s, p, ^Pair)) } $in(q, $composite_extent(s, p, ^Pair)) == (q == p));

const unique Pair.pair: $field;

axiom $def_phys_field(^Pair, Pair.pair, $ptr_to(^Pair), false, 0);

const unique ^PairLists: $ctype;

axiom $is_span_sequential(^PairLists);

axiom $def_struct_type(^PairLists, 24, false, false);

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2(#s1, #s2, #p, ^PairLists) } $inv2(#s1, #s2, #p, ^PairLists) == ($rd_inv(#s2, PairLists.num1, #p) > 0 && $rd_inv(#s2, PairLists.num2, #p) > 0 && (forall Q#i$1^45.14#tc1#1091: int :: {:weight 10} { $keeps(#s2, #p, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091)) } { sk_hack($keeps(#s2, #p, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091))) } { $keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) } { sk_hack($keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair))) } { $keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) } { sk_hack($keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair))) } $in_range_u4(Q#i$1^45.14#tc1#1091) ==> Q#i$1^45.14#tc1#1091 < $rd_inv(#s2, PairLists.num1, #p) ==> $keeps(#s2, #p, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091)) && $keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) && $keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) && $rd_phys_ptr(#s2, Pair.pair, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair) == $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091)) && (exists Q#j$1^62.14#tc1#1092: int :: {:weight 10} { $idx($rd_phys_ptr(#s2, PairLists.pairarray2, #p, ^Pair), Q#j$1^62.14#tc1#1092) } $in_range_u4(Q#j$1^62.14#tc1#1092) && Q#j$1^62.14#tc1#1092 < $rd_inv(#s2, PairLists.num2, #p) && $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray2, #p, ^Pair), Q#j$1^62.14#tc1#1092), ^Pair) == $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), 0))));

axiom (forall #s1: $state, #s2: $state, #p: $ptr :: { $inv2_without_lemmas(#s1, #s2, #p, ^PairLists) } $inv2_without_lemmas(#s1, #s2, #p, ^PairLists) == ($rd_inv(#s2, PairLists.num1, #p) > 0 && $rd_inv(#s2, PairLists.num2, #p) > 0 && (forall Q#i$1^45.14#tc1#1091: int :: {:weight 10} { $keeps(#s2, #p, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091)) } { sk_hack($keeps(#s2, #p, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091))) } { $keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) } { sk_hack($keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair))) } { $keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) } { sk_hack($keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair))) } $in_range_u4(Q#i$1^45.14#tc1#1091) ==> Q#i$1^45.14#tc1#1091 < $rd_inv(#s2, PairLists.num1, #p) ==> $keeps(#s2, #p, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091)) && $keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) && $keeps(#s2, #p, $rd_phys_ptr(#s2, Pair.pair, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) && $rd_phys_ptr(#s2, Pair.pair, $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair) == $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), Q#i$1^45.14#tc1#1091)) && (exists Q#j$1^62.14#tc1#1092: int :: {:weight 10} { $idx($rd_phys_ptr(#s2, PairLists.pairarray2, #p, ^Pair), Q#j$1^62.14#tc1#1092) } $in_range_u4(Q#j$1^62.14#tc1#1092) && Q#j$1^62.14#tc1#1092 < $rd_inv(#s2, PairLists.num2, #p) && $rd_phys_ptr(#s2, Pair.pair, $idx($rd_phys_ptr(#s2, PairLists.pairarray2, #p, ^Pair), Q#j$1^62.14#tc1#1092), ^Pair) == $idx($rd_phys_ptr(#s2, PairLists.pairarray1, #p, ^Pair), 0))));

axiom (forall p: $ptr, q: $ptr, s: $state :: { $in(q, $composite_extent(s, p, ^PairLists)) } $in(q, $composite_extent(s, p, ^PairLists)) == (q == p));

const unique PairLists.num1: $field;

axiom $def_phys_field(^PairLists, PairLists.num1, ^^u4, false, 0);

const unique PairLists.num2: $field;

axiom $def_phys_field(^PairLists, PairLists.num2, ^^u4, false, 4);

const unique PairLists.pairarray1: $field;

axiom $def_phys_field(^PairLists, PairLists.pairarray1, $ptr_to(^Pair), false, 8);

const unique PairLists.pairarray2: $field;

axiom $def_phys_field(^PairLists, PairLists.pairarray2, $ptr_to(^Pair), false, 16);

procedure PairLists#adm(P#_this_: $ptr);
  modifies $s, $cev_pc;
  ensures $is_admissibility_check() ==> $rd_inv($s, PairLists.num1, $phys_ptr_cast(P#_this_, ^PairLists)) > 0;
  ensures $is_admissibility_check() ==> $rd_inv($s, PairLists.num2, $phys_ptr_cast(P#_this_, ^PairLists)) > 0;
  ensures $is_admissibility_check() ==> (forall Q#i$1^45.14#tc1#1091: int :: {:weight 10} { $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091)) } { sk_hack($keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091))) } { $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) } { sk_hack($keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair))) } { $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) } { sk_hack($keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair))) } $in_range_u4(Q#i$1^45.14#tc1#1091) ==> Q#i$1^45.14#tc1#1091 < $rd_inv($s, PairLists.num1, $phys_ptr_cast(P#_this_, ^PairLists)) ==> $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091)) && $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) && $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) && $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair) == $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091));
  ensures $is_admissibility_check() ==> (exists Q#j$1^62.14#tc1#1092: int :: {:weight 10} { $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#j$1^62.14#tc1#1092) } $in_range_u4(Q#j$1^62.14#tc1#1092) && Q#j$1^62.14#tc1#1092 < $rd_inv($s, PairLists.num2, $phys_ptr_cast(P#_this_, ^PairLists)) && $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#j$1^62.14#tc1#1092), ^Pair) == $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), 0));
  ensures $is_unwrap_check() ==> $rd_inv($s, PairLists.num1, $phys_ptr_cast(P#_this_, ^PairLists)) > 0;
  ensures $is_unwrap_check() ==> $rd_inv($s, PairLists.num2, $phys_ptr_cast(P#_this_, ^PairLists)) > 0;
  ensures $is_unwrap_check() ==> (forall Q#i$1^45.14#tc1#1091: int :: {:weight 10} { $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091)) } { sk_hack($keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091))) } { $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) } { sk_hack($keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair))) } { $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) } { sk_hack($keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair))) } $in_range_u4(Q#i$1^45.14#tc1#1091) ==> Q#i$1^45.14#tc1#1091 < $rd_inv($s, PairLists.num1, $phys_ptr_cast(P#_this_, ^PairLists)) ==> $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091)) && $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) && $keeps($s, $phys_ptr_cast(P#_this_, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) && $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair) == $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091));
  ensures $is_unwrap_check() ==> (exists Q#j$1^62.14#tc1#1092: int :: {:weight 10} { $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#j$1^62.14#tc1#1092) } $in_range_u4(Q#j$1^62.14#tc1#1092) && Q#j$1^62.14#tc1#1092 < $rd_inv($s, PairLists.num2, $phys_ptr_cast(P#_this_, ^PairLists)) && $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), Q#j$1^62.14#tc1#1092), ^Pair) == $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#_this_, ^PairLists), ^Pair), 0));
  free ensures $writes_nothing(old($s), $s);
  free ensures $call_transition(old($s), $s);



implementation PairLists#adm(P#_this_: $ptr)
{
  var #wrTime$1^14.25: int;
  var #stackframe: int;

  anon6:
    assume $function_entry($s);
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(14,25) : function entry"} $full_stop_ext(#tok$1^14.25, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$1^14.25 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$1^14.25, (lambda #p: $ptr :: false));
    // assume @decreases_level_is(0); 
    assume {:captureState "<no file>(0,0)"} true;
    assume 0 == $decreases_level;
    // assume @_vcc_admissibility_start(_this_); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $admissibility_start($phys_ptr_cast(P#_this_, ^PairLists), ^PairLists);
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(14,25)"} true;
    // if (@_vcc_is_unwrap_check) ...
    if ($is_unwrap_check())
    {
      anon1:
        // assume !(@_vcc_is_stuttering_check); 
        assume {:captureState "<no file>(0,0)"} true;
        assume !$is_stuttering_check();
        // assume @_vcc_unwrap_check_pre(@state, _this_); 
        assume {:captureState "<no file>(0,0)"} true;
        assume $unwrap_check_pre($s, $phys_ptr_cast(P#_this_, ^PairLists));
        // @_vcc_unwrap_check(_this_)
        assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(14,25)"} true;
        call $unwrap_check($phys_ptr_cast(P#_this_, ^PairLists));
        assume $good_state_ext(#tok$1^14.25, $s);
        // assert true
    }
    else
    {
      anon4:
        assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(14,25)"} true;
        // if (@_vcc_is_admissibility_check) ...
        if ($is_admissibility_check())
        {
          anon2:
            // assume @_vcc_admissibility_pre(@state, _this_); 
            assume {:captureState "<no file>(0,0)"} true;
            assume $admissibility_pre($s, $phys_ptr_cast(P#_this_, ^PairLists));
        }
        else
        {
          anon3:
            // assume @_vcc_stuttering_pre(@state, _this_); 
            assume {:captureState "<no file>(0,0)"} true;
            assume $stuttering_pre($s, $phys_ptr_cast(P#_this_, ^PairLists));
        }

      anon5:
        // @_vcc_havoc_others(_this_, @_vcc_typeof((struct PairLists*)@null))
        assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(14,25)"} true;
        call $havoc_others($phys_ptr_cast(P#_this_, ^PairLists), ^PairLists);
        assume $good_state_ext(#tok$1^14.25, $s);
        // assert true
        // assume ==>(@_vcc_is_stuttering_check, @_vcc_inv2(old(@prestate, @state), @state, _this_)); 
        assume {:captureState "<no file>(0,0)"} true;
        assume $is_stuttering_check() ==> $inv2(old($s), $s, $phys_ptr_cast(P#_this_, ^PairLists), ^PairLists);
    }

  #exit:
}



const unique ^$#_purecall_handler#1: $ctype;

axiom $def_fnptr_type(^$#_purecall_handler#1);

type $#_purecall_handler#1;

const unique ^$#_invalid_parameter_handler#2: $ctype;

axiom $def_fnptr_type(^$#_invalid_parameter_handler#2);

type $#_invalid_parameter_handler#2;

const unique ^$#PairList.h..31666#3: $ctype;

axiom $def_fnptr_type(^$#PairList.h..31666#3);

type $#PairList.h..31666#3;

const unique ^$#_PtFuncCompare#4: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#4);

type $#_PtFuncCompare#4;

const unique ^$#_PtFuncCompare#5: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#5);

type $#_PtFuncCompare#5;

const unique ^$#_PtFuncCompare#6: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#6);

type $#_PtFuncCompare#6;

const unique ^$#_PtFuncCompare#7: $ctype;

axiom $def_fnptr_type(^$#_PtFuncCompare#7);

type $#_PtFuncCompare#7;

const unique ^$#_onexit_t#8: $ctype;

axiom $def_fnptr_type(^$#_onexit_t#8);

type $#_onexit_t#8;

procedure PairListInit(P#dis: $ptr);
  modifies $s, $cev_pc;
  ensures $wrapped($s, $phys_ptr_cast(P#dis, ^PairLists), ^PairLists);
  free ensures $modifies(old($s), $s, (lambda #p: $ptr :: $set_in(#p, $extent(old($s), $phys_ptr_cast(P#dis, ^PairLists)))));
  free ensures $call_transition(old($s), $s);



implementation PairListInit(P#dis: $ptr)
{
  var prestate#19: $state;
  var owns#18: $ptrset;
  var staticWrapState#16: $state;
  var prestate#15: $state;
  var owns#14: $ptrset;
  var staticWrapState#12: $state;
  var prestate#11: $state;
  var owns#10: $ptrset;
  var staticWrapState#8: $state;
  var prestate#7: $state;
  var owns#6: $ptrset;
  var staticWrapState#4: $state;
  var prestate#3: $state;
  var res__vcc_alloc#2: $ptr;
  var res__vcc_alloc#1: $ptr;
  var #wrTime$1^71.1: int;
  var #stackframe: int;

  anon7:
    assume $function_entry($s);
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(71,1) : function entry"} $full_stop_ext(#tok$1^71.1, $s);
    assume $can_use_all_frame_axioms($s);
    assume #wrTime$1^71.1 == $current_timestamp($s);
    assume $def_writes($s, #wrTime$1^71.1, (lambda #p: $ptr :: $set_in(#p, $extent($s, $phys_ptr_cast(P#dis, ^PairLists)))));
    assume $extent_mutable($s, $phys_ptr_cast(P#dis, ^PairLists));
    // assume true
    // assume @decreases_level_is(2147483647); 
    assume {:captureState "<no file>(0,0)"} true;
    assume 2147483647 == $decreases_level;
    // assume true
    // assert @writes_check(@_vcc_span(dis)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(75,10)"} true;
    assert (forall #writes$1^75.10: $ptr :: { $dont_instantiate(#writes$1^75.10) } $set_in(#writes$1^75.10, $span($phys_ptr_cast(P#dis, ^PairLists))) ==> $top_writable($s, #wrTime$1^71.1, #writes$1^75.10));
    // stmt _vcc_set_owns(dis, @_vcc_set_empty); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(75,10)"} true;
    call $set_owns($phys_ptr_cast(P#dis, ^PairLists), $set_empty());
    assume $full_stop_ext(#tok$1^75.10, $s);
    // assert @prim_writes_check((dis->num1)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(77,2)"} true;
    assert $writable_prim($s, #wrTime$1^71.1, $dot($phys_ptr_cast(P#dis, ^PairLists), PairLists.num1));
    // *(dis->num1) := 2; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(77,2)"} true;
    call $write_int(PairLists.num1, $phys_ptr_cast(P#dis, ^PairLists), 2);
    assume $full_stop_ext(#tok$1^77.2, $s);
    // assert @prim_writes_check((dis->num2)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(78,2)"} true;
    assert $writable_prim($s, #wrTime$1^71.1, $dot($phys_ptr_cast(P#dis, ^PairLists), PairLists.num2));
    // *(dis->num2) := 2; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(78,2)"} true;
    call $write_int(PairLists.num2, $phys_ptr_cast(P#dis, ^PairLists), 2);
    assume $full_stop_ext(#tok$1^78.2, $s);
    // \object res__vcc_alloc#1; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(80,20)"} true;
    // assert @reads_check_normal((dis->num1)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(80,27)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // res__vcc_alloc#1 := _vcc_alloc(@_vcc_array(@_vcc_typeof((struct Pair*)@null), *((dis->num1)))); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(80,20)"} true;
    call res__vcc_alloc#1 := $alloc($array(^Pair, $rd_inv($s, PairLists.num1, $phys_ptr_cast(P#dis, ^PairLists))));
    assume $full_stop_ext(#tok$1^80.20, $s);
    // assert @prim_writes_check((dis->pairarray1)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(80,2)"} true;
    assert $writable_prim($s, #wrTime$1^71.1, $dot($phys_ptr_cast(P#dis, ^PairLists), PairLists.pairarray1));
    // *(dis->pairarray1) := (struct Pair*)res__vcc_alloc#1; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(80,2)"} true;
    call $write_int(PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), $ptr_to_int($phys_ptr_cast(res__vcc_alloc#1, ^Pair)));
    assume $full_stop_ext(#tok$1^80.2, $s);
    // \object res__vcc_alloc#2; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(81,20)"} true;
    // assert @reads_check_normal((dis->num2)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(81,27)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // res__vcc_alloc#2 := _vcc_alloc(@_vcc_array(@_vcc_typeof((struct Pair*)@null), *((dis->num2)))); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(81,20)"} true;
    call res__vcc_alloc#2 := $alloc($array(^Pair, $rd_inv($s, PairLists.num2, $phys_ptr_cast(P#dis, ^PairLists))));
    assume $full_stop_ext(#tok$1^81.20, $s);
    // assert @prim_writes_check((dis->pairarray2)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(81,2)"} true;
    assert $writable_prim($s, #wrTime$1^71.1, $dot($phys_ptr_cast(P#dis, ^PairLists), PairLists.pairarray2));
    // *(dis->pairarray2) := (struct Pair*)res__vcc_alloc#2; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(81,2)"} true;
    call $write_int(PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), $ptr_to_int($phys_ptr_cast(res__vcc_alloc#2, ^Pair)));
    assume $full_stop_ext(#tok$1^81.2, $s);
    // assume @_vcc_ptr_neq_null(*((dis->pairarray1))); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(83,11)"} true;
    assume $non_null($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair));
    // assume @_vcc_ptr_neq_null(*((dis->pairarray2))); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(84,11)"} true;
    assume $non_null($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair));
    // assert @prim_writes_check((*((dis->pairarray1))[0]->pair)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(90,2)"} true;
    assert $writable_prim($s, #wrTime$1^71.1, $dot($idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0), Pair.pair));
    // assert @reads_check_normal((dis->pairarray1)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(90,2)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // assert @reads_check_normal((dis->pairarray2)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(90,29)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // *(*((dis->pairarray1))[0]->pair) := *((dis->pairarray2))[0]; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(90,2)"} true;
    call $write_int(Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0), $ptr_to_int($idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0)));
    assume $full_stop_ext(#tok$1^90.2, $s);
    // assert @prim_writes_check((*((dis->pairarray2))[0]->pair)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(91,2)"} true;
    assert $writable_prim($s, #wrTime$1^71.1, $dot($idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0), Pair.pair));
    // assert @reads_check_normal((dis->pairarray2)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(91,2)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // assert @reads_check_normal((dis->pairarray1)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(91,29)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // *(*((dis->pairarray2))[0]->pair) := *((dis->pairarray1))[0]; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(91,2)"} true;
    call $write_int(Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0), $ptr_to_int($idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0)));
    assume $full_stop_ext(#tok$1^91.2, $s);
    // assert @prim_writes_check((*((dis->pairarray1))[1]->pair)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(93,2)"} true;
    assert $writable_prim($s, #wrTime$1^71.1, $dot($idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1), Pair.pair));
    // assert @reads_check_normal((dis->pairarray1)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(93,2)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // assert @reads_check_normal((dis->pairarray2)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(93,29)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // *(*((dis->pairarray1))[1]->pair) := *((dis->pairarray2))[1]; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(93,2)"} true;
    call $write_int(Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1), $ptr_to_int($idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1)));
    assume $full_stop_ext(#tok$1^93.2, $s);
    // assert @prim_writes_check((*((dis->pairarray2))[1]->pair)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(94,2)"} true;
    assert $writable_prim($s, #wrTime$1^71.1, $dot($idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1), Pair.pair));
    // assert @reads_check_normal((dis->pairarray2)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(94,2)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // assert @reads_check_normal((dis->pairarray1)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(94,29)"} true;
    assert $thread_local($s, $phys_ptr_cast(P#dis, ^PairLists));
    // *(*((dis->pairarray2))[1]->pair) := *((dis->pairarray1))[1]; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(94,2)"} true;
    call $write_int(Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1), $ptr_to_int($idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1)));
    assume $full_stop_ext(#tok$1^94.2, $s);
    // assert @writes_check(@_vcc_span(dis)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(102,10)"} true;
    assert (forall #writes$1^102.10: $ptr :: { $dont_instantiate(#writes$1^102.10) } $set_in(#writes$1^102.10, $span($phys_ptr_cast(P#dis, ^PairLists))) ==> $top_writable($s, #wrTime$1^71.1, #writes$1^102.10));
    // stmt _vcc_set_owns(dis, @_vcc_set_add_element(@_vcc_owns(@state, dis), *((dis->pairarray1))[0])); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(102,10)"} true;
    call $set_owns($phys_ptr_cast(P#dis, ^PairLists), $set_add_element($owns($s, $phys_ptr_cast(P#dis, ^PairLists)), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0)));
    assume $full_stop_ext(#tok$1^102.10, $s);
    // assert @writes_check(@_vcc_span(dis)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(103,10)"} true;
    assert (forall #writes$1^103.10: $ptr :: { $dont_instantiate(#writes$1^103.10) } $set_in(#writes$1^103.10, $span($phys_ptr_cast(P#dis, ^PairLists))) ==> $top_writable($s, #wrTime$1^71.1, #writes$1^103.10));
    // stmt _vcc_set_owns(dis, @_vcc_set_add_element(@_vcc_owns(@state, dis), *((dis->pairarray1))[1])); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(103,10)"} true;
    call $set_owns($phys_ptr_cast(P#dis, ^PairLists), $set_add_element($owns($s, $phys_ptr_cast(P#dis, ^PairLists)), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1)));
    assume $full_stop_ext(#tok$1^103.10, $s);
    // assert @writes_check(@_vcc_span(dis)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(105,10)"} true;
    assert (forall #writes$1^105.10: $ptr :: { $dont_instantiate(#writes$1^105.10) } $set_in(#writes$1^105.10, $span($phys_ptr_cast(P#dis, ^PairLists))) ==> $top_writable($s, #wrTime$1^71.1, #writes$1^105.10));
    // stmt _vcc_set_owns(dis, @_vcc_set_add_element(@_vcc_owns(@state, dis), *((dis->pairarray2))[0])); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(105,10)"} true;
    call $set_owns($phys_ptr_cast(P#dis, ^PairLists), $set_add_element($owns($s, $phys_ptr_cast(P#dis, ^PairLists)), $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0)));
    assume $full_stop_ext(#tok$1^105.10, $s);
    // assert @writes_check(@_vcc_span(dis)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(106,10)"} true;
    assert (forall #writes$1^106.10: $ptr :: { $dont_instantiate(#writes$1^106.10) } $set_in(#writes$1^106.10, $span($phys_ptr_cast(P#dis, ^PairLists))) ==> $top_writable($s, #wrTime$1^71.1, #writes$1^106.10));
    // stmt _vcc_set_owns(dis, @_vcc_set_add_element(@_vcc_owns(@state, dis), *((dis->pairarray2))[1])); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(106,10)"} true;
    call $set_owns($phys_ptr_cast(P#dis, ^PairLists), $set_add_element($owns($s, $phys_ptr_cast(P#dis, ^PairLists)), $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1)));
    assume $full_stop_ext(#tok$1^106.10, $s);
    // _math \state prestate#3; 
    assume {:captureState "<no file>(0,0)"} true;
    // prestate#3 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    prestate#3 := $current_state($s);
    // _math \state staticWrapState#4; 
    assume {:captureState "<no file>(0,0)"} true;
    // staticWrapState#4 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    staticWrapState#4 := $current_state($s);
    // _math \objset owns#6; 
    assume {:captureState "<no file>(0,0)"} true;
    // owns#6 := @_vcc_set_empty; 
    assume {:captureState "<no file>(0,0)"} true;
    owns#6 := $set_empty();
    // assert @writes_check(*((dis->pairarray1))[0]); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(116,10)"} true;
    assert $top_writable($s, #wrTime$1^71.1, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0));
    // assume @_vcc_pre_static_wrap(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $pre_static_wrap($s);
    // @_vcc_static_wrap(pure(*((dis->pairarray1))[0]), staticWrapState#4, owns#6)
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(116,4)"} true;
    call $static_wrap($idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0), staticWrapState#4, owns#6);
    assume $good_state_ext(#tok$1^116.4, $s);
    // assert @inv_check(@_vcc_set_eq(@_vcc_owns(@state, *((dis->pairarray1))[0]), @_vcc_set_empty)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(116,10)"} true;
    assert $set_eq($owns($s, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0)), $set_empty());
    // assume @_vcc_full_stop(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $full_stop($s);
    // _math \state prestate#7; 
    assume {:captureState "<no file>(0,0)"} true;
    // prestate#7 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    prestate#7 := $current_state($s);
    // _math \state staticWrapState#8; 
    assume {:captureState "<no file>(0,0)"} true;
    // staticWrapState#8 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    staticWrapState#8 := $current_state($s);
    // _math \objset owns#10; 
    assume {:captureState "<no file>(0,0)"} true;
    // owns#10 := @_vcc_set_empty; 
    assume {:captureState "<no file>(0,0)"} true;
    owns#10 := $set_empty();
    // assert @writes_check(*((dis->pairarray1))[1]); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(117,10)"} true;
    assert $top_writable($s, #wrTime$1^71.1, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1));
    // assume @_vcc_pre_static_wrap(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $pre_static_wrap($s);
    // @_vcc_static_wrap(pure(*((dis->pairarray1))[1]), staticWrapState#8, owns#10)
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(117,4)"} true;
    call $static_wrap($idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1), staticWrapState#8, owns#10);
    assume $good_state_ext(#tok$1^117.4, $s);
    // assert @inv_check(@_vcc_set_eq(@_vcc_owns(@state, *((dis->pairarray1))[1]), @_vcc_set_empty)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(117,10)"} true;
    assert $set_eq($owns($s, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1)), $set_empty());
    // assume @_vcc_full_stop(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $full_stop($s);
    // _math \state prestate#11; 
    assume {:captureState "<no file>(0,0)"} true;
    // prestate#11 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    prestate#11 := $current_state($s);
    // _math \state staticWrapState#12; 
    assume {:captureState "<no file>(0,0)"} true;
    // staticWrapState#12 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    staticWrapState#12 := $current_state($s);
    // _math \objset owns#14; 
    assume {:captureState "<no file>(0,0)"} true;
    // owns#14 := @_vcc_set_empty; 
    assume {:captureState "<no file>(0,0)"} true;
    owns#14 := $set_empty();
    // assert @writes_check(*((dis->pairarray2))[0]); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(118,10)"} true;
    assert $top_writable($s, #wrTime$1^71.1, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0));
    // assume @_vcc_pre_static_wrap(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $pre_static_wrap($s);
    // @_vcc_static_wrap(pure(*((dis->pairarray2))[0]), staticWrapState#12, owns#14)
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(118,4)"} true;
    call $static_wrap($idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0), staticWrapState#12, owns#14);
    assume $good_state_ext(#tok$1^118.4, $s);
    // assert @inv_check(@_vcc_set_eq(@_vcc_owns(@state, *((dis->pairarray2))[0]), @_vcc_set_empty)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(118,10)"} true;
    assert $set_eq($owns($s, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0)), $set_empty());
    // assume @_vcc_full_stop(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $full_stop($s);
    // _math \state prestate#15; 
    assume {:captureState "<no file>(0,0)"} true;
    // prestate#15 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    prestate#15 := $current_state($s);
    // _math \state staticWrapState#16; 
    assume {:captureState "<no file>(0,0)"} true;
    // staticWrapState#16 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    staticWrapState#16 := $current_state($s);
    // _math \objset owns#18; 
    assume {:captureState "<no file>(0,0)"} true;
    // owns#18 := @_vcc_set_empty; 
    assume {:captureState "<no file>(0,0)"} true;
    owns#18 := $set_empty();
    // assert @writes_check(*((dis->pairarray2))[1]); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(119,10)"} true;
    assert $top_writable($s, #wrTime$1^71.1, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1));
    // assume @_vcc_pre_static_wrap(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $pre_static_wrap($s);
    // @_vcc_static_wrap(pure(*((dis->pairarray2))[1]), staticWrapState#16, owns#18)
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(119,4)"} true;
    call $static_wrap($idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1), staticWrapState#16, owns#18);
    assume $good_state_ext(#tok$1^119.4, $s);
    // assert @inv_check(@_vcc_set_eq(@_vcc_owns(@state, *((dis->pairarray2))[1]), @_vcc_set_empty)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(119,10)"} true;
    assert $set_eq($owns($s, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 1)), $set_empty());
    // assume @_vcc_full_stop(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $full_stop($s);
    // _math \state prestate#19; 
    assume {:captureState "<no file>(0,0)"} true;
    // prestate#19 := @_vcc_current_state(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    prestate#19 := $current_state($s);
    // assume @_vcc_pre_wrap(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $pre_wrap($s);
    // assert @writes_check(dis); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(121,4)"} true;
    assert $top_writable($s, #wrTime$1^71.1, $phys_ptr_cast(P#dis, ^PairLists));
    // assert @writes_check(@_vcc_owns(@state, dis)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(121,4)"} true;
    assert (forall #writes$1^121.4: $ptr :: { $dont_instantiate(#writes$1^121.4) } $set_in(#writes$1^121.4, $owns($s, $phys_ptr_cast(P#dis, ^PairLists))) ==> $top_writable($s, #wrTime$1^71.1, #writes$1^121.4));
    // stmt @_vcc_wrap(dis, @_vcc_typeof(dis)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(121,4)"} true;
    call $wrap($phys_ptr_cast(P#dis, ^PairLists), ^PairLists);
    assume $good_state_ext(#tok$1^121.4, $s);
    // assert @inv_check(>(*((dis->num1)), 0)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(121,9)"} true;
    assert $rd_inv($s, PairLists.num1, $phys_ptr_cast(P#dis, ^PairLists)) > 0;
    // assert @inv_check(>(*((dis->num2)), 0)); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(121,9)"} true;
    assert $rd_inv($s, PairLists.num2, $phys_ptr_cast(P#dis, ^PairLists)) > 0;
    // assert @inv_check(forall(uint32_t i; @in_range_u4(i); ==>(<(i, *((dis->num1))), &&(&&(&&(@keeps(dis, *((dis->pairarray1))[i]), @keeps(dis, *((*((dis->pairarray1))[i]->pair)))), @keeps(dis, *((*((*((dis->pairarray1))[i]->pair))->pair)))), @_vcc_ptr_eq_pure(*((*((*((dis->pairarray1))[i]->pair))->pair)), *((dis->pairarray1))[i]))))); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(121,9)"} true;
    assert (forall Q#i$1^45.14#tc1#1091: int :: {:weight 10} { $keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091)) } { sk_hack($keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091))) } { $keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) } { sk_hack($keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair))) } { $keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) } { sk_hack($keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair))) } $in_range_u4(Q#i$1^45.14#tc1#1091) ==> Q#i$1^45.14#tc1#1091 < $rd_inv($s, PairLists.num1, $phys_ptr_cast(P#dis, ^PairLists)) ==> $keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091)) && $keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair)) && $keeps($s, $phys_ptr_cast(P#dis, ^PairLists), $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair)) && $rd_phys_ptr($s, Pair.pair, $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091), ^Pair), ^Pair) == $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#i$1^45.14#tc1#1091));
    // assert @inv_check(exists(uint32_t j; @in_range_u4(j); &&(<(j, *((dis->num2))), @_vcc_ptr_eq_pure(*((*((dis->pairarray2))[j]->pair)), *((dis->pairarray1))[0])))); 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(121,9)"} true;
    assert (exists Q#j$1^62.14#tc1#1092: int :: {:weight 10} { $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#j$1^62.14#tc1#1092) } $in_range_u4(Q#j$1^62.14#tc1#1092) && Q#j$1^62.14#tc1#1092 < $rd_inv($s, PairLists.num2, $phys_ptr_cast(P#dis, ^PairLists)) && $rd_phys_ptr($s, Pair.pair, $idx($rd_phys_ptr($s, PairLists.pairarray2, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), Q#j$1^62.14#tc1#1092), ^Pair) == $idx($rd_phys_ptr($s, PairLists.pairarray1, $phys_ptr_cast(P#dis, ^PairLists), ^Pair), 0));
    // assume @_vcc_full_stop(@state); 
    assume {:captureState "<no file>(0,0)"} true;
    assume $full_stop($s);
    // return; 
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(122,1)"} true;
    assume {:captureState "C:\Users\John\SparkleShare\cis800-005\vc3d - nocaching\vc3d\PairList.h(122,1) : function exit"} true;
    assert $position_marker();
    goto #exit;

  #exit:
}



const unique l#public: $label;

const unique #tok$1^121.4: $token;

const unique #tok$1^119.4: $token;

const unique #tok$1^118.4: $token;

const unique #tok$1^117.4: $token;

const unique #tok$1^116.4: $token;

const unique #tok$1^106.10: $token;

const unique #tok$1^105.10: $token;

const unique #tok$1^103.10: $token;

const unique #tok$1^102.10: $token;

const unique #tok$1^94.2: $token;

const unique #tok$1^93.2: $token;

const unique #tok$1^91.2: $token;

const unique #tok$1^90.2: $token;

const unique #tok$1^81.2: $token;

const unique #tok$1^81.20: $token;

const unique #tok$1^80.2: $token;

const unique #tok$1^80.20: $token;

const unique #tok$1^78.2: $token;

const unique #tok$1^77.2: $token;

const unique #tok$1^75.10: $token;

const unique #tok$1^71.1: $token;

const unique #tok$1^14.25: $token;

axiom $type_code_is(1, ^^u4);

const unique #file^C?3A?5CUsers?5CJohn?5CSparkleShare?5Ccis800?2D005?5Cvc3d?20?2D?20nocaching?5Cvc3d?5CPairList.h: $token;

axiom $file_name_is(1, #file^C?3A?5CUsers?5CJohn?5CSparkleShare?5Ccis800?2D005?5Cvc3d?20?2D?20nocaching?5Cvc3d?5CPairList.h);

const unique #distTp1: $ctype;

axiom #distTp1 == $ptr_to(^Pair);
