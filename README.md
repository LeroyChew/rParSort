# rParSort
produces and proves reordered parity CNFs

README (draft)
usage: ./parity [<VARS>] [<SEED>] [<option> ...]

<VARS> and <SEED> are positive integers
<VARS> is 4 or greater, specifying the number of input variables to the reordered parity cnf. 
<SEED> specifies the random ordering on the second XOR constraint and the position of the negated literal.

`<option>` is of the following:

	-o <filename> 	output to files filename.cnf and filename.drat

