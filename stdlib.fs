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

s" print-array" 
s" ( addr len -- ) prints content of array starting from addr" help-set

\ - Boolean constants ----------------------------------------------
-1 constant true
0  constant false

\ -- Stack helpers ---------------------------------------------------
: 2dup   over over ;
: 2drop  drop drop ;
: 2swap  rot >r rot r> ;
: nip    swap drop ;
: tuck   swap over ;
: ?dup   dup if dup then ;

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

\ -- Logic -----------------------------------------------------------
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

\ alias for then
: endif postpone then ; immediate

\ -- Double-cell memory ---------------------------------------------

: 2!  ( lo hi addr -- )
  DUP >R ! R> 1+ ! ;

: 2@  ( addr -- lo hi )
  DUP @ SWAP 1+ @ ;

\ -- Double-cell return stack ---------------------------------------

: 2>r  ( lo hi -- )
  SWAP >R >R ;

: 2r>  ( -- lo hi )
  R> R> SWAP ;

\ -- Help entries for stdlib words ----------------------------------

s" variable"
s" ( -- )
Creates a new variable. Usage: variable x
x pushes its address. Use @ to fetch, ! to store.
Example: variable counter  100 counter !  counter @ ."
help-set

s" constant"
s" ( n -- )
Creates a named constant. Usage: 42 constant answer
Pushes its value when invoked.
Example: 3 constant three  three . => 3"
help-set

s" ?"
s" ( addr -- )
Fetches and prints the value at addr.
Shorthand for @ .
Example: variable x  42 x !  x ?"
help-set

s" +!"
s" ( n addr -- )
Adds n to the value stored at addr.
Example: variable counter  1 counter +!"
help-set

s" array"
s" ( -- )
Creates an array. Usage: n array name
Invoke with an index to get the address of that element.
Example: 10 array scores  42 0 scores !  0 scores @ ."
help-set

s" true"
s" ( -- -1 )
Boolean constant for true. Value is -1."
help-set

s" false"
s" ( -- 0 )
Boolean constant for false. Value is 0."
help-set

s" 1+"
s" ( n -- n+1 )
Adds 1 to the top of stack."
help-set

s" 1-"
s" ( n -- n-1 )
Subtracts 1 from the top of stack."
help-set

s" 2+"
s" ( n -- n+2 )
Adds 2 to the top of stack."
help-set

s" 2-"
s" ( n -- n-2 )
Subtracts 2 from the top of stack."
help-set

s" 2*"
s" ( n -- n*2 )
Multiplies the top of stack by 2."
help-set

s" 2/"
s" ( n -- n/2 )
Divides the top of stack by 2. Integer division."
help-set

s" negate"
s" ( n -- -n )
Negates the top of stack."
help-set

s" abs"
s" ( n -- |n| )
Returns the absolute value of n."
help-set

s" min"
s" ( a b -- n )
Returns the smaller of a and b."
help-set

s" max"
s" ( a b -- n )
Returns the larger of a and b."
help-set

s" 2dup"
s" ( a b -- a b a b )
Duplicates the top two stack items."
help-set

s" 2drop"
s" ( a b -- )
Discards the top two stack items."
help-set

s" 2swap"
s" ( a b c d -- c d a b )
Swaps the top two pairs of stack items."
help-set

s" nip"
s" ( a b -- b )
Discards the second item, keeping the top."
help-set

s" tuck"
s" ( a b -- b a b )
Copies the top item below the second item."
help-set

s" and"
s" ( a b -- flag )
Logical AND. Returns 1 if both a and b are non-zero."
help-set

s" or"
s" ( a b -- flag )
Logical OR. Returns 1 if either a or b is non-zero."
help-set

s" not"
s" ( flag -- flag )
Logical NOT. Returns 1 if flag is 0, 0 otherwise."
help-set

s" <>"
s" ( a b -- flag )
Returns 1 if a and b are not equal, 0 otherwise."
help-set

s" <="
s" ( a b -- flag )
Returns 1 if a is less than or equal to b, 0 otherwise."
help-set

s" >="
s" ( a b -- flag )
Returns 1 if a is greater than or equal to b, 0 otherwise."
help-set

s" space"
s" ( -- )
Prints a single space character."
help-set

s" spaces"
s" ( n -- )
Prints n space characters."
help-set

s" .cr"
s" ( n -- )
Prints the top of stack followed by a newline."
help-set

s" between"
s" ( n lo hi -- flag )
Returns 1 if lo < n < hi, 0 otherwise. Bounds are exclusive."
help-set

s" .bin"
s" ( n -- n )
Prints n in binary, then restores the original base. Leaves n on stack."
help-set

s" .oct"
s" ( n -- n )
Prints n in octal, then restores the original base. Leaves n on stack."
help-set

s" .dec"
s" ( n -- n )
Prints n in decimal, then restores the original base. Leaves n on stack."
help-set

s" .hex"
s" ( n -- n )
Prints n in hexadecimal, then restores the original base. Leaves n on stack."
help-set

s" .nums"
s" ( n -- n )
Prints n in binary, octal, decimal, and hex. Leaves n on stack."
help-set

s" bl"
s" ( -- 32 )
Pushes the ASCII code for space (32)."
help-set

s" ?dup"
s" ( n -- n n | 0 )
  Duplicates the top of stack only if it is non-zero.
  If n is 0, leaves 0 unchanged and does not duplicate.
  Useful for conditional loops where zero means done.
  Example: 0 ?dup . => 0
  Example: 3 ?dup . . => 3 3"
help-set

s" 2!"
s"  ( lo hi addr -- )
  Stores a double-cell value at addr and addr+1.
  lo is stored at addr, hi is stored at addr+1.
  Example: variable x  2 cells allot
           10 20 x 2!
           x 2@ . .  => 10 20"
help-set

s" 2@"
s"  ( addr -- lo hi )
  Fetches a double-cell value from addr and addr+1.
  Leaves lo then hi on the stack, hi on top.
  Example: variable x  2 cells allot
           10 20 x 2!
           x 2@ . .  => 20 10"
help-set

s" 2>r"
s"  ( lo hi -- )
  Moves a double-cell value from the data stack to the return stack.
  Order is preserved: 2r> will restore lo hi with hi on top.
  Must be balanced with 2r> before the word exits.
  Only valid inside a definition.
  Example: : test  1 2 2>r  3 4  2r> . . . . ;
           test => 2 1 4 3"
help-set

s" 2r>"
s"  ( -- lo hi )
  Moves a double-cell value from the return stack to the data stack.
  Restores the pair pushed by 2>r with hi on top.
  Only valid inside a definition.
  See also: 2>r"
help-set
