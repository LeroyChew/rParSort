# rParSort
produces and proves reordered parity CNFs

README

simply use 'make' to make

e.g. "$ make parity"



usage: ./parity [<VARS>] [<SEED>] [<option> ...]

<VARS> and <SEED> are positive integers
<VARS> is 4 or greater, specifying the number of input variables to the reordered parity cnf. 
<SEED> specifies the random ordering on the second XOR constraint and the position of the negated literal.

`<option>` is of the following:

	-o <filename> 	output to files filename.cnf and filename.drat
	-m <mode number> <value> switches the probability distribution depending on mode
		0: uniformly random
		1: uniformly but rerolls until the maximum permutation distance is <value>
		2: produces a clique minor of size <value>
		3: performs <value> number of random adjacent swaps to make the permutation


If input.txt is a file in the main folder the program will read the file to find a permutation, instead of producing a new random instance.
Provided, the file lists a permutation of size 4 or greater, otherwise it will proceed with the random distributions.

E.g. 4 2 3 5 1

