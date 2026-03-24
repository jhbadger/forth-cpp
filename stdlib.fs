\ -- Variable, Constant, Array -----------------------------------------

: variable create 0 , does> ;
: constant create , does> @ ;
: ?        @ . ;
: +!       dup @ rot + swap ! ;
\ array: allocates n cells, created word pushes base address
\ use: n array myarr  then  myarr = base addr,  n myarr arr@ = element addr
: array    create cells allot does> ;
: arr@     ( idx arr-addr -- elem-addr )  swap cells + ;

: print-array ( addr len -- )
  0 do
    dup i cells +
    @ .
  loop
  drop ;

s" print-array"
s" ( addr len -- ) prints content of array starting from addr" help-set

\ -- Boolean constants -------------------------------------------------
-1 constant true
0  constant false

\ -- Stack helpers -----------------------------------------------------
: 2dup   over over ;
: 2drop  drop drop ;
\ 2swap: standard ( a b c d -- c d a b )
: 2swap  { a b c d -- } c d a b ;
: nip    swap drop ;
: tuck   swap over ;
: ?dup   dup if dup then ;

\ -- Arithmetic helpers ------------------------------------------------
: 1+     1 + ;
: 1-     1 - ;
: 2+     2 + ;
: 2-     2 - ;
: 2*     2 * ;
: 2/     2 / ;
: negate 0 swap - ;
: abs    dup 0 < if negate then ;
: min    2dup < if drop else swap drop then ;
: max    2dup > if drop else swap drop then ;

\ -- Logic -------------------------------------------------------------
\ Note: and/or/xor/invert are bitwise primitives.
\ not, <>, <=, >= are defined in terms of comparisons.
: not  0= ;
: <>   = not ;
: <=   > not ;
: >=   < not ;

\ -- Output helpers ----------------------------------------------------
: space    32 emit ;
: spaces   dup 0 > if 0 do space loop else drop then ;
: .cr      . cr ;

\ -- Loop helpers ------------------------------------------------------
\ between: ( n lo hi -- flag )  true if lo <= n < hi
: between  { n lo hi -- flag }  n lo >= n hi < and ;

\ -- Base helpers ------------------------------------------------------
\ Each word prints n in the given base, restores original base, leaves n.
: .bin { n -- n } base @ >r 2  base ! n . r> base ! n ;
: .oct { n -- n } base @ >r 8  base ! n . r> base ! n ;
: .dec { n -- n } base @ >r 10 base ! n . r> base ! n ;
: .hex { n -- n } base @ >r 16 base ! n . r> base ! n ;
: .nums ( n -- n ) .bin .oct .dec .hex ;

\ -- Misc --------------------------------------------------------------
: bl     ( -- 32 ) 32 ;

\ alias for then
: endif postpone then ; immediate

\ -- Double-cell memory -----------------------------------------------
\ 2! ( lo hi addr -- )  stores lo at addr, hi at addr+cell
: 2!  ( lo hi addr -- )
  dup >r cell+ !  r> ! ;

\ 2@ ( addr -- lo hi )  fetches lo from addr, hi from addr+cell
: 2@  ( addr -- lo hi )
  dup @  swap cell+ @ ;

\ -- Double-cell return stack -----------------------------------------
: 2>r  ( lo hi -- )   swap >r >r ;
: 2r>  ( -- lo hi )   r> r> swap ;

\ -- Help entries ------------------------------------------------------

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
s" ( n -- )
Creates an array of n cells. The created word pushes the base address.
Use arr@ for indexed element addresses.
Example: 10 array scores
         42 0 scores arr@ !    ( store 42 at index 0 )
         0 scores arr@ @  .    ( fetch index 0 => 42 )
         scores 10 print-array ( print all 10 elements )"
help-set

s" arr@"
s" ( idx addr -- elem-addr )
Computes the address of element idx in an array at addr.
Example: 3 scores arr@ @  ( fetch element 3 )"
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
s" ( a b -- n )
Bitwise AND of a and b."
help-set

s" or"
s" ( a b -- n )
Bitwise OR of a and b."
help-set

s" xor"
s" ( a b -- n )
Bitwise XOR of a and b."
help-set

s" invert"
s" ( n -- ~n )
Bitwise NOT of n."
help-set

s" not"
s" ( flag -- flag )
Logical NOT. Returns -1 if flag is 0, 0 otherwise."
help-set

s" <>"
s" ( a b -- flag )
Returns -1 if a and b are not equal, 0 otherwise."
help-set

s" <="
s" ( a b -- flag )
Returns -1 if a is less than or equal to b, 0 otherwise."
help-set

s" >="
s" ( a b -- flag )
Returns -1 if a is greater than or equal to b, 0 otherwise."
help-set

s" space"
s" ( -- )
Prints a single space character."
help-set

s" spaces"
s" ( n -- )
Prints n space characters. Does nothing if n <= 0."
help-set

s" .cr"
s" ( n -- )
Prints the top of stack followed by a newline."
help-set

s" between"
s" ( n lo hi -- flag )
Returns -1 if lo <= n < hi, 0 otherwise."
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
Example: 0 ?dup . => 0
Example: 3 ?dup . . => 3 3"
help-set

s" 2!"
s" ( lo hi addr -- )
Stores lo at addr and hi at addr+cell.
Example: variable x  1 cells allot
         10 20 x 2!
         x 2@ . .  => 20 10"
help-set

s" 2@"
s" ( addr -- lo hi )
Fetches lo from addr and hi from addr+cell.
hi is on top of stack after fetch.
Example: variable x  1 cells allot
         10 20 x 2!
         x 2@ . .  => 20 10"
help-set

s" 2>r"
s" ( lo hi -- )
Moves a double-cell value from the data stack to the return stack.
Must be balanced with 2r> before the word exits.
Only valid inside a definition."
help-set

s" 2r>"
s" ( -- lo hi )
Moves a double-cell value from the return stack to the data stack.
Restores the pair pushed by 2>r with hi on top.
Only valid inside a definition."
help-set

s" r@"
s" ( -- n )
Copies the top of the return stack to the data stack without removing it."
help-set