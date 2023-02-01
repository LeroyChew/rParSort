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

	-o <filename> 	output to files filename.cnf and filename.drat, filename.gr and filename_half.gr
	-m <mode number> <value> switches the probability distribution depending on mode
		0 (default): uniformly random
		1: Mallows([<VARS>],q), if k<1 reads float q instead of k and uses the  distribution for permutations, otherwise using integer parameter k, where q= (1/n)^(1/(k*k))
		2: produces a clique minor of size <value>
		3: performs <value> number of random adjacent swaps to make the permutation
		4: performs 10000000 potential random adjacent swaps but forbids the distance being >k
		5: uniformly but rerolls until the maximum permutation distance is <value>
	-p <proof_format>
		0: skip proofs, use this option if you just want to generate the formulas
		1 (default): DRAT- proof (DRAT proof without new variables)
		2: Extended resolution proof (Still checkable with DRAT-trim)
	-g <graph_output_mode>
		0: no graphs
		1: .gr format
		2: .edges format
		3 (default): .gr format with tangled path _half.gr 
		4: .edges with tangled path _half.edges 
		5: .gr + .edges 
		6: all

If input.txt is a file in the main folder the program will read the file to find a permutation, instead of producing a new random instance.
Provided, the file lists a permutation of size 4 or greater, otherwise it will proceed with the random distributions.

E.g. 4 2 3 5 1

example of usage
$ ./parity 50 90003 -p 0 -m 1 21 -o n50s90003m1k21

50 input variables. Seed 90003 is used. Proofs suppressed.
Mallows mode is selected, but since k>=1, q is calculated  as (1/50)^(1/(441)).
Outputs files n50s90003m1k21.cnf n50s90003m1k21.gr n50s90003m1k21_half.gr n50s90003m1k21_stats.txt and input.txt
input.txt is made blank

If we want to run it again with the prover on, but we've forgotten the random seed, we can copy the permutation listed in n50s90003m1k21_stats.txt into input.txt and use -p 1 for any other input.
