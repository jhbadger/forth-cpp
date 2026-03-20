\ -- Variable and Constant defined in Forth ------------------------

: variable create 0 , does> ; 
: constant create , does> @ ;
: ? @ . ;
: +!  dup @ rot + swap ! ;  
: array create does> swap cell * + ;

: print-array ( addr len -- )
  0 do
    dup i cells +  ( addr addr[i] )
    @ .            ( addr value )
  loop
  drop ;

\ - Boolean constants ----------------------------------------------
-1 constant true
0  constant false


\ -- Arithmetic helpers ----------------------------------------------
: 1+   1 + ;
: 1-   1 - ;
: 2+   2 + ;
: 2-   2 - ;
: 2*   2 * ;
: 2/   2 / ;
: negate   0 swap - ;
: abs   dup 0 < if negate then ;
: min   2dup < if drop else swap drop then ;
: max   2dup > if drop else swap drop then ;

\ -- Stack helpers ---------------------------------------------------
: 2dup   over over ;
: 2drop  drop drop ;
: 2swap  rot >r rot r> ;
: nip    swap drop ;
: tuck   swap over ;

\ -- Logic -----------------------------------------------------------
: and   * 0= 0= ;
: or    + 0= 0= ;
: not   0= ;
: <>    = not ;
: <=    > not ;
: >=    < not ;

\ -- Output helpers --------------------------------------------------
: space    32 emit ;
: spaces   0 do space loop ;
: .cr      . cr ;

\ -- Loop helpers ----------------------------------------------------
: between   ( n lo hi -- flag )  rot tuck > rot rot > not and ;

\ -- Base helpers ----------------------------------------------------
\ show top of stack in binary but leave the number unchanged
: .bin { n -- n } base @ 2 base ! n . base ! n ;

\ show top of stack in octal but leave the number unchanged
: .oct { n -- n } base @ 8 base ! n . base ! n ;

\ show top of stack in decimal but leave the number unchanged
: .dec { n -- n } base @ 10 base ! n . base ! n ;

\ show top of stack in hex but leave the number unchanged
: .hex { n -- n } base @ 16 base ! n . base ! n ;

\ show top of stack in various bases but leave the number unchanged
: .nums ( n -- n ) .bin .oct .dec .hex ;

\ misc words

\ outputs code for space
: bl ( -- c ) 32 ;

\ : fill 
