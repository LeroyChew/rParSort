#include "Prop.h"
#include <fstream>
#include <stack>
#include <math.h>
#include "Tree.h"
#include <cstring>

#include <ctime>        // std::time
#include <cstdlib>      // std::rand, std::srand

#define ERPROOFONLY	0
#define DISPLAY_LEVEL 1
#define SWAP_LEVEL 1
#define XOR_LEVEL 5
#define DRAT_LEVEL 3
#define TREE_PSWAPS_LEVEL 5
#define TREE_ISWAPS_LEVEL 5
#define END_EXCEPTION_LEVEL 2
#define SWAP_LEVEL	1

Tree main_tree(1);
Tree second_tree(1);
ofstream myfile;

int proof_size = 0;
int ata_size = 0;
int rata_size = 0;
int ate_size = 0;
int rate_size = 0;

int order_random(int i) { return std::rand() % i; }
int max_ext_var = 0;
std::vector<int> extvariables;



bool file_writing = 0;
bool file_reading = 0;
bool clique_mode = 0;
int distribution_mode = 0;
bool graph_writing = 0;
FILE *file_proof;
FILE *file_cnf;
FILE *file_graph;
Cnf f;
Edge_Graph g;


void xor_add(Cnf* p, int lit1, int lit2, int lit3) {
	p->add_clause(Clause(-lit1, lit2, lit3, 0));
	p->add_clause(Clause(lit1, -lit2, lit3, 0));
	p->add_clause(Clause(lit1, lit2, -lit3, 0));
	p->add_clause(Clause(-lit1, -lit2, -lit3, 0));

	if (DISPLAY_LEVEL >= XOR_LEVEL) {
		cout << "xor" << lit1 << " " << lit2 << " " << lit3 << "\n";
	}
}

int ext_var(int input) {
	int output;
	if (input > 0) {
		output = ::extvariables[input - 1];
	}
	else {
		output = -::extvariables[-input - 1];
	}
	return output;
}


Cnf parity_fwd(int n, Cnf P) {
	::main_tree.source->data = (1);

	int lit1 = 1;
	int lit2 = 2;
	int lit3 = n + 3;

	//this can be copied=================
	::main_tree.extend_source(n + 3, 2, 1);
	
	xor_add(&P, lit1, lit2, lit3);
	

	//====This is for forward order================================

	for (int i = 3; i < n + 1; i++) {
		lit1 = i;
		lit2 = n + i ;
		lit3 = n + i + 1;

						  //this can be copied=================
		::main_tree.extend_source(n + i + 1, i, 1);
		
		xor_add(&P, lit1, lit2, lit3);

		//====================================
	}
	lit1 = n + 1;
	lit2 = n + 2;
	lit3 = -(2 * n) - 1; //negate last Tseitin variable
	
	xor_add(&P, lit1, lit2, lit3);

	::main_tree.end_lit1 = lit1;
	::main_tree.end_lit2 = lit2;
	return P;
}

Cnf parity(int n, std::vector<int> input_vector, int neg_lit) {
	Cnf P;

	P = parity_fwd(n, P);

	//===============================
	int lit1 = input_vector[0];
	int lit2 = input_vector[1];
	if (neg_lit == 0) {
		lit1 = -lit1;
	}
	if (neg_lit == 1) {
		lit2 = -lit2;
	}
	int lit3 = 2 * n+2;
	
	xor_add(&P, lit1, lit2, lit3);

	for (int i = 3; i < n + 1; i++) {
		lit1 = input_vector[i-1];
		if (neg_lit == i-1) {
			lit1 = -lit1;
		}
		lit2 = 2*n-1 + i; //second set of Tseitin variables
		lit3 = 2 * n + i;//second set of Tseitin variables
		
		xor_add(&P, lit1, lit2, lit3);
	}

	lit1 = input_vector[n];
	lit2 = input_vector[n + 1];
	if (neg_lit == n) {
		lit1 = -lit1;
	}
	if (neg_lit == n+1) {
		lit2 = -lit2;
	}
	lit3 = -(3 * n) ; //negate last Tseitin variable
	

	xor_add(&P, lit1, lit2, lit3);

	return P;
}


void clause_print(Clause C){
for (int i = 0; i < 4; i++) {
	if (C.lit[i] == 0) {
		break;
	}

	fprintf(::file_proof, "%i", C.lit[i]);
	fprintf(::file_proof, " ");
}

fprintf(::file_proof, "0\n");
}

void ata(Clause C) {
	if (DISPLAY_LEVEL > DRAT_LEVEL) {
		std::cout << "ATA ";
		C.display();
	}
	::proof_size++;
	::ata_size++;

	if (::file_writing) {

		clause_print(C);
	}
	return;


}

void rata(Clause C, int l) {
	if (DISPLAY_LEVEL > DRAT_LEVEL) {
		std::cout << l << " RATA ";
		C.display();
	}
	::proof_size++;
	::rata_size++;
	
	if (::file_writing) {
		clause_print(C);
	}
	return;
}

void ate(Clause C) {
	if (DISPLAY_LEVEL > DRAT_LEVEL) {
		std::cout << "ATE ";
		
		C.display();
	}
	::proof_size++;
	::ate_size++;
	if (::file_writing) {
		fprintf(::file_proof, "d ");
		clause_print(C);
	}
	return;
}

void rate(Clause C, int l) {
	if (DISPLAY_LEVEL > DRAT_LEVEL) {
		std::cout << l << " RATE ";
		
		C.display();
	}
	::proof_size++;
	::rate_size++;

	if (::file_writing){

		fprintf(::file_proof, "d ");
		clause_print(C);
		

	}
	
	return;
}

void clause_shift(int lit1, int lit2, int lit3, int lit4, int elim) {

	if (ERPROOFONLY) {
		::max_ext_var++;
		::extvariables[abs(elim) - 1] = max_ext_var;

		lit1 = ext_var(lit1);
		lit2 = ext_var(lit2);
		lit3 = ext_var(lit3);
		lit4 = ext_var(lit4);
		elim = ext_var(elim);
	}

	Clause tern1(-lit1, lit2, lit3, lit4);
	Clause tern2(lit1, -lit2, lit3, lit4);
	Clause tern3(lit1, lit2, -lit3, lit4);
	Clause tern4(lit1, lit2, lit3, -lit4);
	Clause tern5(-lit1, -lit2, -lit3, lit4);
	Clause tern6(lit1, -lit2, -lit3, -lit4);
	Clause tern7(-lit1, lit2, -lit3, -lit4);
	Clause tern8(-lit1, -lit2, lit3, -lit4);

	if (DISPLAY_LEVEL > XOR_LEVEL) {
		cout << "adding terns" << endl;
	}
	ata(tern1);
	ata(tern2);
	ata(tern3);
	ata(tern4);
	ata(tern5);
	ata(tern6);
	ata(tern7);
	ata(tern8);
	if (ERPROOFONLY) {
		
		if (DISPLAY_LEVEL > XOR_LEVEL) {
			cout << "adding lower xors" << endl;
		}
		rata(Clause(-elim, lit3, lit4, 0), -elim);
		rata(Clause(elim, -lit3, lit4, 0), -elim);
		rata(Clause(elim, lit3, -lit4, 0), -elim);
		rata(Clause(-elim, -lit3, -lit4, 0), -elim);
		
		//Resolve on lit3
		ata(Clause(-lit1, -lit2, -elim, lit4));
		ata(Clause(-lit1, -lit2, -elim, -lit4));
		ata(Clause(-lit1, lit2, elim, lit4));
		ata(Clause(-lit1, lit2, elim, -lit4));
		ata(Clause(lit1, -lit2, elim, lit4));
		ata(Clause(lit1, -lit2, elim, -lit4));
		ata(Clause(lit1, lit2, -elim, lit4));
		ata(Clause(lit1, lit2, -elim, -lit4));
		//resolve on lit4


		if (DISPLAY_LEVEL > XOR_LEVEL) {
			cout << "adding upper xors" << endl;
		}
		ata(Clause(-elim, lit1, lit2, 0));
		ata(Clause(elim, -lit1, lit2, 0));
		ata(Clause(elim, lit1, -lit2, 0));
		ata(Clause(-elim, -lit1, -lit2, 0));
			}
	else {

		
		if (DISPLAY_LEVEL > XOR_LEVEL) {
			cout << "eliminating upper xors" << endl;
		}

		rate(Clause(elim, -lit2, lit3, 0), elim);
		rate(Clause(elim, lit2, -lit3, 0), elim);
		rate(Clause(elim, -lit1, lit4, 0), elim);
		rate(Clause(elim, lit1, -lit4, 0), elim);
		if (DISPLAY_LEVEL > XOR_LEVEL) {
			cout << "eliminating lower xors" << endl;
		}
		rate(Clause(-elim, lit2, lit3, 0), -elim);
		rate(Clause(-elim, -lit2, -lit3, 0), -elim);
		rate(Clause(-elim, lit1, lit4, 0), -elim);
		rate(Clause(-elim, -lit1, -lit4, 0), -elim);
		

		if (DISPLAY_LEVEL > XOR_LEVEL) {
			cout << "adding lower xors" << endl;
		}
		rata(Clause(-elim, lit3, lit4, 0), -elim);
		rata(Clause(-elim, -lit3, -lit4, 0), -elim);
		rata(Clause(-elim, lit1, lit2, 0), -elim);
		rata(Clause(-elim, -lit1, -lit2, 0), -elim);
		if (DISPLAY_LEVEL > XOR_LEVEL) {
			cout << "adding upper xors" << endl;
		}
		rata(Clause(elim, -lit3, lit4, 0), elim);
		rata(Clause(elim, lit3, -lit4, 0), elim);
		rata(Clause(elim, -lit1, lit2, 0), elim);
		rata(Clause(elim, lit1, -lit2, 0), elim);
		
		if (DISPLAY_LEVEL > XOR_LEVEL) {
			cout << "eliminating terns" << endl;
		}
		ate(tern1);
		ate(tern2);
		ate(tern3);
		ate(tern4);
		ate(tern5);
		ate(tern6);
		ate(tern7);
		ate(tern8);
		}
	return;
	}

bool swap_end(T_Node* swap1, bool dir) {
	bool dir1 = swap1->lr;
	T_Node* par1 = swap1->parent;
	T_Node* other_child;
	if (dir1 == 0) {
		other_child = par1->child2;
	}
	else {
		other_child = par1->child1;
	}
	int lit_swap1 = swap1->data;
	int lit_swap2;
	int lit_par1 = par1->data;
	int lit_par2;
	int lit_no_swap = other_child->data;
	if (dir == 1) {
		lit_swap2 = ::main_tree.end_lit2;
		lit_par2 = -::main_tree.end_lit1;
	}
	else {
		lit_swap2 = ::main_tree.end_lit1;
		lit_par2 = -::main_tree.end_lit2;
	}


	clause_shift(lit_par2, lit_swap1, lit_no_swap, lit_swap2, lit_par1);
	if (dir == 1) {
		::main_tree.end_lit2=lit_swap1;
	}
	else {
		::main_tree.end_lit1 = lit_swap1;
	}
	if (DISPLAY_LEVEL > END_EXCEPTION_LEVEL) {
		::main_tree.print();
	}
	if (dir1 == 0) {
		par1->child1 = par1->child3;
		par1->child1->lr = 0;
	}
	else {
		par1->child2 = par1->child3;
		par1->child2->lr = 1;
	}
	par1->child3 = swap1;

	return dir1;
}

void swap_down(T_Node* swap1, bool dir) {

	//::main_tree.print();
	//dir gives direction of otherchild's child that we keep
	T_Node* par1 = swap1->parent;
	T_Node* other_child; //swap 1's sibling
	bool dir1 = swap1->lr;
	if (dir1 == 0) {
		other_child = par1->child2;
	}
	else {
		other_child = par1->child1;
	}
	T_Node* swap2;
	int lit_no_swap;
	if (dir == 0) {
		swap2 = other_child->child2;
		other_child->child2 = swap1;
		other_child->child2->parent = other_child;
		other_child->child2->lr = 1;
		lit_no_swap = other_child->child1->data;
	}
	else {
		swap2 = other_child->child1;
		other_child->child1 = swap1;
		other_child->child1->parent = other_child;
		other_child->child1->lr = 0;
		lit_no_swap = other_child->child2->data;
	}
	if (dir1 == 0) {
		par1->child1 = swap2;
		par1->child1->parent = par1;
		par1->child1->lr = 0;
	}
	else {
		par1->child2 = swap2;
		par1->child2->parent = par1;
		par1->child2->lr = 1;
	}

	//Put Cnf stuff here
	clause_shift(par1->data, swap2->data, lit_no_swap, swap1->data, other_child->data);

	if (DISPLAY_LEVEL > TREE_ISWAPS_LEVEL) {
		::main_tree.print();
	}
	return;
}

bool swap_up(T_Node* swap1) {
	int lit_swap1 = swap1->data;
	T_Node* par1 = swap1->parent;

	if (par1 == NULL) {
		cout << "error no parent" << endl;
	}
	int lit_par1 = par1->data;
	bool dir1 = swap1->lr;
	T_Node* par2 = par1->parent;
	if (par2 == NULL) {
		return 0;
	}
	int lit_par2 = par2->data;
	bool dir2 = par1->lr;
	T_Node* swap2;
	int lit_swap2;
	//this is where swapping occurs
	if (dir2 == 0) {
		swap2 = par2->child2;
		par2->child2 = swap1;
		par2->child2->lr = 1;
	}
	else {
		swap2 = par2->child1;
		par2->child1 = swap1;
		par2->child1->lr = 0;
	}
	lit_swap2 = swap2->data;
	swap1->parent = par2;

        // don't assign a variable to the same value in both branches

	int lit_no_swap;
	if (dir1 == 0) {
		par1->child1 = swap2;
		lit_no_swap = par1->child2->data;
		par1->child1->lr = 0;
	}
	else {
		par1->child2 = swap2;
		lit_no_swap = par1->child1->data;
		par1->child2->lr = 1;
	}
	swap2->parent = par1;



	clause_shift(lit_par2, lit_swap1, lit_no_swap, lit_swap2, lit_par1);
	
	if (DISPLAY_LEVEL > TREE_ISWAPS_LEVEL) {
		::main_tree.print();
	}

	return dir1;
}

Tree rebalance(Tree g, bool r) {//a0 is Tseitin variable
	if (g.depth <= 2) {
		return g; // already log depth
	}
	float half_internals = ((g.depth - 2) / 2.0);
	if (!r) {
		// we will add ceil n / 2 Tseitin variables to g2frange
		for (int i = 0; i < ceil(half_internals); i++) {
			int lit1 = g.source->data;
			int lit2 = g.source->child1->child1->data;
			int lit3 = g.source->child1->child2->data;
			int lit4 = g.source->child2->data;
			int elim = g.source->child1->data;

			::clause_shift(lit1, lit2, lit3, lit4, elim);

			g.tree_shift_r();
		}

	}
	else {
		for (int i = 0; i < floor(half_internals); i++) {

			int lit1 = g.source->data;
			int lit2 = g.source->child2->child2->data;
			int lit3 = g.source->child2->child1->data;
			int lit4 = g.source->child1->data;
			int elim = g.source->child2->data;

			::clause_shift(lit1, lit2, lit3, lit4, elim);

			g.tree_shift_l();

		}
	}

	Tree g1(g.source->child1); //the left tree
	Tree g2(g.source->child2); //the right tree
	g1.depth = (int)floor(half_internals) +1;
	g2.depth = (int)ceil(half_internals) +1;
	g.depth = max(g1.depth, g2.depth) + 1;
	g1=rebalance(g1, 0);
	g2=rebalance(g2, 1);
	g.depth = max(g1.depth, g2.depth) + 1;
	//merge the two cnfs and return
	return g;
}

T_Node* sel_leaf(int i, int n, T_Node* t) {
	if (n == 1) {
		return t;
	}

	float m = n / 2.0;
	int j = i;
	if (j <= floor(m)) {
		return sel_leaf(j, (int)floor(m), t->child1);
	}
	else
	{
		return sel_leaf(j- (int)floor(m), n- (int)floor(m), t->child2);
	}

}

Cnftnodepair sel_push_down(int i, int n, T_Node* pivot, T_Node* swap_item, Cnf f) {
	Cnftnodepair joint;
	joint.form = f; //preparing formula
	if (n == 1) {
		joint.nodestar = pivot;
		return joint;
	}

	float m = n / 2.0;
	int j = i;
	if (j <= (int)floor(m)) {
		//swapdown(swapitem, f);
		return sel_push_down(j, (int)floor(m), pivot->child1, swap_item, f);
	}
	else
	{
		return sel_push_down(j - (int)floor(m), n - (int)floor(m), pivot->child2, swap_item, f);
	}

}

T_Node* subroutine_tries1(T_Node* selection, int range_up, float range_mid, int* range_down, bool* is_selection_a_leaf, stack<SwapSelCombo>* select_pos, bool end_except) {
	if (selection->child2 != NULL) {
		*is_selection_a_leaf = 0;
		select_pos->top().tries++;

		if (!end_except) {
			if (DISPLAY_LEVEL > SWAP_LEVEL) {
				cout << "moving right" << endl;
			}
			selection = selection->child2;
			*range_down = (int)ceil(range_mid);
			select_pos->push(SwapSelCombo(*range_down, range_up, 0, 0));
		}
	}
	return selection;
}
T_Node* subroutine_tries2(T_Node* selection, bool* end_except, bool* is_selection_a_leaf, stack<SwapSelCombo>* select_pos) {
		if (DISPLAY_LEVEL > SWAP_LEVEL) {
			cout << "moving up" << endl;
		}
		if (selection->parent != NULL) {
			selection = selection->parent;
		}
		else {
			*end_except = 1;
		}
		*is_selection_a_leaf = 0;
		select_pos->pop();
		return selection;

}
T_Node* subroutine_endlit_normal(int* range_up, int* range_down, float* range_mid, T_Node* selection, int* enddata, bool* enddir, int* endvalue, bool* is_selection_a_leaf, int n) {
	*range_up = n;
	*range_down = 1;
	//put literal in child 3 position
	//perform clauseshift
	//now next swapdown puts it in realtree and subtree in child3 position
	//however remember to swap out the poor subtree in child3 position on the way back up
	//end by
	selection = new T_Node(*enddata);
	::main_tree.source->child3 = selection;
	selection->parent = ::main_tree.source;
	*range_mid = (*range_up + *range_down) / 2.0; 
	if ((int)ceil(*range_mid) <= *endvalue) {
		swap_end(::main_tree.source->child1, *enddir);
		*range_down = (int)ceil(*range_mid);
	}
	else {
		swap_end(::main_tree.source->child2, *enddir);
		*range_up = (int)ceil(*range_mid) - 1;
	}
	*is_selection_a_leaf = 1;
	return selection;

}

T_Node* subroutine_sel_is_leaf(int swap_pos, int n, int* range_up, int* range_down, float* range_mid,  bool* in_pos,  bool* is_selection_a_leaf, bool* end_except, bool* enddir, T_Node* selection, std::vector<int, std::allocator<int> >* inp_vector, stack<SwapSelCombo>* select_pos) {
	if (*is_selection_a_leaf) {
		int value = selection->data;
		if (swap_pos == 0) {
			value = abs((*inp_vector)[value - 1]);
		}
		else {
			value = swap_pos;
		}
		int first_level_exception = 2;
		stack<bool> reverse_swaps;
		bool in_leaf_position = 1;
		T_Node* selection2 = selection;
		//getchar();

		if (DISPLAY_LEVEL > SWAP_LEVEL) {
			cout << "found leaf with data " << selection->data << "and value " << value << endl;
		}
		if (value != select_pos->top().lbound || value != select_pos->top().ubound) {
			if (!*end_except) {
				*range_up = select_pos->top().ubound;
				*range_down = select_pos->top().lbound;
				*in_pos = false;
				//now we have found a leaf to swap
				// here we can use value to find the swapping position
				stack<SwapSelCombo> select_pos_copy = *select_pos;

				if (selection->lr == 0) {
					first_level_exception = 0;
				}
				else {
					first_level_exception = 1;
				}

				if (DISPLAY_LEVEL > SWAP_LEVEL) {
					cout << selection->data << "not in range " << *range_down << "to" << *range_up << endl;
				}
				bool notinrange = 1;
				in_leaf_position = 1;
				selection2 = selection;
				while (notinrange) { //the loop for the first push up
					select_pos_copy.pop();// this means bounds will be for parent of selection

					if (select_pos_copy.top().lbound <= value && select_pos_copy.top().ubound >= value) {
						notinrange = 0;
						if (DISPLAY_LEVEL > SWAP_LEVEL) {
							cout << selection->data << "is in the right range " << select_pos_copy.top().lbound << "to" << select_pos_copy.top().ubound << endl;
						}
						//::reverse.print();
						if (value > n) {
							bool the_bool;
							// common lines in both branches
							if (value == n + 1) {
								T_Node* third_node = new T_Node(::main_tree.end_lit1);
								::main_tree.source->child3 = third_node;
								third_node->parent = ::main_tree.source;
								the_bool = swap_end(selection, 0);

							}
							else {
								T_Node* third_node = new T_Node(::main_tree.end_lit2);
								::main_tree.source->child3 = third_node;
								third_node->parent = ::main_tree.source;
								the_bool = swap_end(selection, 1);

							}
							if (!the_bool) {
								selection = selection->parent->child1;
							}
							else {
								selection = selection->parent->child2;
							}
						}

					}
					else {

						if (DISPLAY_LEVEL > SWAP_LEVEL) {
							cout << selection->data << "not in range " << select_pos_copy.top().lbound << "to" << select_pos_copy.top().ubound << endl;
						}
						if (selection->lr == 0) {
							first_level_exception = 0;
						}
						else {
							first_level_exception = 1;
						}
						if (selection->parent->parent != NULL) {
							//bool g = swap_up(selection);
							reverse_swaps.push(swap_up(selection));
						}


						in_leaf_position = 0;

						selection2 = selection->parent;

						//::reverse.print();

					}
				}
				*range_up = select_pos_copy.top().ubound;
				*range_down = select_pos_copy.top().lbound;

			}
			else
			{
				in_leaf_position = 0;
			}
			//now swapdown 
			int down_levels = 0;
			bool down_swap_dir = 0;
			bool stop_swap_down = 0;



			T_Node* sibling = selection;
			T_Node* selection_swap = selection;
			T_Node* selection_no_swap = selection;



			//::reverse.print();

			if (value <= n) {
				while (!stop_swap_down) {
					//calculate sibling
					*range_mid = (*range_up + *range_down) / 2.0;
					if (selection->lr == 0) {
						sibling = selection->parent->child2;
					}
					if (selection->lr == 1) {
						sibling = selection->parent->child1;
					}
					//check if terminating
					if (in_leaf_position) { //we might not want to swap here
						stop_swap_down = 1;
						//::reverse.print();
						if (sibling->child1 != NULL) { //sibling is not a leaf, then it has at most two descendents
							if (value != *range_down) {// if value is rangedown it is already in the right position
								if (value == *range_up) {
									if (sibling->child2->child1 == NULL) {
										selection_swap = sibling->child2;
										swap_down(selection, 0);
										down_levels++;
										if (DISPLAY_LEVEL > SWAP_LEVEL) {
											cout << value << " moving right to " << *range_up << endl;
										}
									}
									else in_leaf_position = 0;
								}
								else {
									selection_swap = sibling->child1;
									swap_down(selection, 1);
									down_levels++;

									if (DISPLAY_LEVEL > SWAP_LEVEL) {
										cout << value << " moving left to " << *range_up - 1 << endl;
									}
								}
							}
							else {
								if (selection->lr == 1) {
									if (*range_up - *range_down == 3) {
										//::reverse.print();
										selection->parent->child1 = selection;
										sibling->lr = 1;
										selection->parent->child2 = sibling;
										selection->lr = 0;
										down_levels++;
										if (DISPLAY_LEVEL > SWAP_LEVEL) {
											cout << selection->data << " CASE A2 swapping left with sibling " << sibling->data << endl;
										}
									}
									if (*range_up - *range_down == 2) {
										selection_swap = sibling->child1;
										swap_down(selection, 1);
										down_levels++;
										if (DISPLAY_LEVEL > SWAP_LEVEL) {
											cout << value << " CASE A3 moving left to " << range_up << endl;
										}
									}
									//not sure if this case can happen
								}
								if (*range_up - *range_down == 1) {
									selection_swap = sibling->child1;
									swap_down(selection, 1);
									down_levels++;
									if (DISPLAY_LEVEL > SWAP_LEVEL) {
										cout << value << " CASE A1 moving left to " << range_up << endl;
									}
								}
							}
						}
						else {
							if ((selection->lr == 1) && (value == *range_down)) {
								selection->parent->child1 = selection;
								sibling->lr = 1;
								selection->parent->child2 = sibling;
								selection->lr = 0;
								selection_swap = sibling;
								down_levels++;
								if (DISPLAY_LEVEL > SWAP_LEVEL) {
									cout << value << "CASE B swapping left with sibling " << sibling->data << endl;
								}
							}
							else {
								if ((selection->lr == 0) && (value == *range_up)) {
									selection->parent->child2 = selection;
									sibling->lr = 0;
									selection->parent->child1 = sibling;
									selection->lr = 1;
									selection_swap = sibling;
									down_levels++;
									if (DISPLAY_LEVEL > SWAP_LEVEL) {
										cout << selection->data << "CASE C swapping right with sibling " << sibling->data << endl;
									}
								}
							}

						}
					}
					else {
						selection2 = sibling;
						if (first_level_exception == 2) {
							if (ceil(*range_mid) <= value) {
								selection_swap = selection2->child1;
								selection_no_swap = selection2->child2;
								swap_down(selection, 1);

								*range_down = (int)ceil(*range_mid);
								if (DISPLAY_LEVEL > SWAP_LEVEL) {
									cout << selection->data << " moving right " << *range_down << "to" << *range_up << endl;
								}
							}
							else {
								selection_swap = selection2->child2;
								selection_no_swap = selection2->child1;
								swap_down(selection, 0);

								*range_up = (int)ceil(*range_mid) - 1;
								if (DISPLAY_LEVEL > SWAP_LEVEL) {
									cout << selection->data << " moving left " << *range_down << "to" << *range_up << endl;
								}
							}
						}
						else {
							if (first_level_exception == 1) {
								selection_swap = selection2->child1;
								selection_no_swap = selection2->child2;
								swap_down(selection, 1);
							}
							else {
								selection_swap = selection2->child2;
								selection_no_swap = selection2->child2;
								swap_down(selection, 0);

							}
							first_level_exception = 2;
							if (ceil(*range_mid) <= value) {
								*range_down = (int)ceil(*range_mid);
								if (DISPLAY_LEVEL > SWAP_LEVEL) {
									cout << selection->data << " moving right " << *range_down << "to" << *range_up << endl;
								}
							}
							else {
								*range_up = (int)ceil(*range_mid) - 1;
								if (DISPLAY_LEVEL > SWAP_LEVEL) {
									cout << selection->data << " moving left " << *range_down << "to" << *range_up << endl;
								}
							}
						}
						down_levels++;
						if (selection_swap->child1 == NULL || selection_no_swap->child1 == NULL) {
							in_leaf_position = 1;
						}
					}


				}


				down_levels--;
				while (down_levels > 0) {
					down_levels--;
					bool g = swap_up(selection_swap);
					if (DISPLAY_LEVEL > SWAP_LEVEL) {
						cout << " moving " << selection_swap->data << "upwards" << endl;
					}
				}
			}
			if (*end_except) {
				swap_end(selection_swap, *enddir);
			}
			else {
				bool down_swap_dir2;
				while (!reverse_swaps.empty()) {
					down_swap_dir2 = 0;
					if (reverse_swaps.top() == 0) {
						down_swap_dir2 = 1;
					}
					swap_down(selection_swap, down_swap_dir2);
					if (DISPLAY_LEVEL > SWAP_LEVEL) {
						cout << " moving " << selection_swap->data << "downwards" << endl;
					}
					reverse_swaps.pop();
				}
			}


			if (*end_except) {
				selection = selection_swap->parent;
			}
			else {
				selection = selection_swap;
			}
		}
		if (DISPLAY_LEVEL > TREE_PSWAPS_LEVEL) {
			::main_tree.print();
		}
		select_pos->top().tries = 2;

	}
	return selection;
}


T_Node* subroutine_not_endexcept(bool* is_selection_a_leaf, stack<SwapSelCombo>* select_pos, bool* end_except, T_Node* selection, int* range_up, int* range_down, float* range_mid) 
{
	if (selection->child1 != NULL) {
		*is_selection_a_leaf = 0;
		select_pos->top().tries++;

		if (!*end_except) {
			if (DISPLAY_LEVEL > SWAP_LEVEL) {
				cout << "moving left" << endl;
			}
			selection = selection->child1;
			*range_up = (int)ceil(*range_mid) - 1;
			select_pos->push(SwapSelCombo(*range_down, *range_up, 0, 0));
		}
	}
	return selection;
}

string read_line() {
	char * input = new char[256];
	std::cin>> input;
	getchar();
	return input;
}

void swapping(int n, Cnf f, std::vector<int> inp_vector) {
	bool in_pos = 0;
	while (in_pos == 0) {
		in_pos = 1; //this will become false if any leaf is in the wrong position
		T_Node* selection = ::main_tree.source;
		int range_down = 1; //the currently selected node has a range of positions
		int range_up = n;
		stack<SwapSelCombo> select_pos; //swapselcombo
		select_pos.push(SwapSelCombo(range_down, range_up+2, 0, 0));
		if (DISPLAY_LEVEL >= END_EXCEPTION_LEVEL) {
			cout << "pushing excp" << range_down << " " << range_up + 2 << endl;
		}
		select_pos.push(SwapSelCombo(range_down, range_up, 0, 0));
		bool is_selection_a_leaf = 0;
		bool end_except = 0;
		while (!select_pos.empty()) { //this traverses all nodes
			is_selection_a_leaf = 1;
			range_down = select_pos.top().lbound;
			range_up = select_pos.top().ubound;
			float range_mid = (range_down + range_up)/ 2.0;
			if (select_pos.top().tries == 0) {
					selection = subroutine_not_endexcept(&is_selection_a_leaf, &select_pos, &end_except, selection, &range_up, &range_down, &range_mid);
			}
			else {
				if (select_pos.top().tries == 1) {
					selection = subroutine_tries1(selection, range_up, range_mid, &range_down, &is_selection_a_leaf, &select_pos, end_except);
				}
				else {
					if (select_pos.top().tries > 1) {
						selection = subroutine_tries2(selection, &end_except, &is_selection_a_leaf, &select_pos);
					}
				}
			}
			bool enddir = 0;
			if(end_except && (!select_pos.empty())) { //deal with endlits
				int endvalue;

				if (select_pos.top().tries == 0) {
					endvalue = ::main_tree.end_lit1;
				}
				else {
					endvalue = ::main_tree.end_lit2;
					enddir = 1;
				}

				if (DISPLAY_LEVEL > END_EXCEPTION_LEVEL) {
					cout << "found endleaf with data " << endvalue;
				}
				int enddata = endvalue;

				endvalue = abs(inp_vector[endvalue - 1]);
				if (DISPLAY_LEVEL > END_EXCEPTION_LEVEL) {
					cout <<"and value " << endvalue << endl;
				}
				if (endvalue > n){
					if ((select_pos.top().tries == 0)&&(endvalue==n+2)) {
						::main_tree.end_lit1 = ::main_tree.end_lit2;
						::main_tree.end_lit2=enddata;
					}
					else {
						if ((select_pos.top().tries == 1) && (endvalue == n + 1)) {
							::main_tree.end_lit2= ::main_tree.end_lit1;
							::main_tree.end_lit1 = enddata;
						}
					}
				}
				else {
					selection=subroutine_endlit_normal(&range_up, &range_down, &range_mid, selection, &enddata, &enddir, &endvalue, &is_selection_a_leaf, n);
				}
			}
			selection= subroutine_sel_is_leaf(0, n, &range_up, &range_down, &range_mid, &in_pos, &is_selection_a_leaf, &end_except, &enddir, selection, &inp_vector, &select_pos);
		}
	}
	return;
}

void swapping_pair(int n, Cnf f, int a, int b) {
	bool in_pos = 0;
		in_pos = 1; //this will become false if any leaf is in the wrong position
		T_Node* selection = ::main_tree.source;
		int rangedown = 1; //the currently selected node has a range of positions
		int rangeup = n;
		stack<SwapSelCombo> selectpos; //swapselcombo
		selectpos.push(SwapSelCombo(rangedown, rangeup + 2, 0, 0));
		if (DISPLAY_LEVEL >= END_EXCEPTION_LEVEL) {
			cout << "pushing excp" << rangedown << " " << rangeup + 2 << endl;
		}
		selectpos.push(SwapSelCombo(rangedown, rangeup, 0, 0));
		bool isselectionaleaf = 0;
		bool endexcept = 0;
		while (!isselectionaleaf) { //this traverses all nodes
			isselectionaleaf = 1;

			//recalculate the ranges
			rangedown = selectpos.top().lbound;
			rangeup = selectpos.top().ubound;
			float rangemid = (rangedown + rangeup)/ 2.0;
			int tries = selectpos.top().tries;
			if (endexcept) {

			}
			if (a<ceil(rangemid)) {
					selection= subroutine_not_endexcept(&isselectionaleaf, &selectpos, &endexcept, selection, &rangeup, &rangedown, &rangemid);
			}
			else {
				if (a<=n) {
					selection = subroutine_tries1(selection, rangeup, rangemid, &rangedown, &isselectionaleaf, &selectpos, endexcept);
				}
				else {
					if (a>n) {
						selection = subroutine_tries2(selection, &endexcept, &isselectionaleaf, &selectpos);
					}
				}
			}
			bool enddir = 0;
			if (endexcept && (!selectpos.empty())) { //new code to deal with endlits
				int endvalue;

				if (a==n+1) {
					endvalue = ::main_tree.end_lit1;
				}
				else {
					endvalue = ::main_tree.end_lit2;
					enddir = 1;
				}

				if (DISPLAY_LEVEL > END_EXCEPTION_LEVEL) {
					cout << "found endleaf with data " << endvalue;
				}
				int enddata = endvalue;

				endvalue = b;
				if (DISPLAY_LEVEL > END_EXCEPTION_LEVEL) {
					cout << "and value " << endvalue << endl;
				}
				if (endvalue > n) {
					if ((a == n + 1) && (endvalue == n + 2)) {
						::main_tree.end_lit1 = ::main_tree.end_lit2;
						::main_tree.end_lit2 = enddata;
						return;

					}
					else {
						if ((a == n + 2) && (endvalue == n + 1)) {
							::main_tree.end_lit2 = ::main_tree.end_lit1;
							::main_tree.end_lit1 = enddata;
							return;
						}
					}
				}
				else {
					selection = subroutine_endlit_normal(&rangeup, &rangedown, &rangemid, selection, &enddata, &enddir, &endvalue, &isselectionaleaf, n);
				}

			}
			std::vector<int> dummy;
			selection = subroutine_sel_is_leaf(0, n, &rangeup, &rangedown, &rangemid, &in_pos, &isselectionaleaf, &endexcept, &enddir, selection, &dummy , &selectpos);
		}
	return;
}

Tree linear_tree(Tree g, bool r , int lb, int ub ) {
	if (ub-lb<2) {
		return g; // already log depth
	}

	float m = (lb + ub) / 2.0;
	int m_int = (int) ceil(m);
	Tree g1(g.source->child1); //the left tree
	Tree g2(g.source->child2); //the right tree

	g1 = linear_tree(g1, 0, lb, m_int-1);
	g2 = linear_tree(g2, 1, m_int, ub);

	int reps;
	if (!r) {
		// we will add ceil n / 2 Tseitin variables to g2
		reps= ub - m_int;
		for (int i = 0; i < reps; i++) {

			int lit1 = g.source->data;
			int lit2 = g.source->child2->child2->data;
			int lit3 = g.source->child2->child1->data;
			int lit4 = g.source->child1->data;
			int elim = g.source->child2->data;

			::clause_shift(lit1, lit2, lit3, lit4, elim);

			g.tree_shift_l();
		}


	}
	else {
		reps = m_int-lb-1;
		for (int i = 0; i < reps; i++) {

			int lit1 = g.source->data;
			int lit2 = g.source->child1->child1->data;
			int lit3 = g.source->child1->child2->data;
			int lit4 = g.source->child2->data;
			int elim = g.source->child1->data;

			::clause_shift(lit1, lit2, lit3, lit4, elim);

			g.tree_shift_r();


		}
	}

	return g;
}



void final_equiv(int n, std::vector<int> invector) {
	T_Node* select = ::main_tree.source;
	while (select->child1 != NULL) {
		select = select->child1;
	}
	int l2 = invector[0];
	int r2 = invector[1];
	int u2 = 2 * n-2;
	int l1 = select->data;
	int r1 = select->parent->child2->data;
	int u1 = select->parent->data;

	l1 = ext_var(l1);
	l2 = ext_var(l2);
	r1 = ext_var(r1);
	r2 = ext_var(r2);
	u1 = ext_var(u1);
	u2 = ext_var(u2);

	bool flip;
	if ((l1 == l2) ^ (r1 == r2)) {
		ata(Clause(-l1, u1, u2, 0));
		ata(Clause(-l1, u1, u2, 0));
		ata(Clause(l1, -u1, -u2, 0));
		ata(Clause(l1, -u1, -u2, 0));
		ata(Clause(u1, u2, 0, 0));
		ata(Clause(-u1, -u2, 0, 0));
		flip = 1;
	}
	else {
		flip = 0;
		ata(Clause(-l1, -u1, u2, 0));
		ata(Clause(-l1, u1, -u2, 0));
		ata(Clause(l1, -u1, u2, 0));
		ata(Clause(l1, u1, -u2, 0));
		ata(Clause(-u1, u2, 0, 0));
		ata(Clause(u1, -u2, 0, 0));
	}


	for (int i = 2; i < n-2; i++ ) {
		select = select->parent;
		int r1 = select->parent->child2->data;
		int l2 = 2 * n + i - 4;
		int l1 = select->data;
		int r2 = invector[i];
		int u1 = select->parent->data;
		int u2 = 2 * n + i-3;

		l1 = ::extvariables[l1 - 1];
		l2 = ::extvariables[l2 - 1];
		r1 = ::extvariables[r1 - 1];
		if (r2 > 0) {
			r2 = ::extvariables[r2 - 1];
		}
		else {
			r2 = -::extvariables[-r2 - 1];
		}
		u1 = ::extvariables[u1 - 1];
		u2 = ::extvariables[u2 - 1];

		if ((flip) ^ (r1 != r2)) {
			ata(Clause(-l1, u1, u2, 0));
			ata(Clause(l1, u1, u2, 0));
			ata(Clause(-l1, -u1, -u2, 0));
			ata(Clause(l1, -u1, -u2, 0));
			ata(Clause(u1, u2, 0, 0));
			ata(Clause(-u1, -u2, 0, 0));
			flip = 1;
		}
		else {
			ata(Clause(-l1, -u1, u2, 0));
			ata(Clause(l1, -u1, u2, 0));
			ata(Clause(-l1, u1, -u2, 0));
			ata(Clause(l1, u1, -u2, 0));
			ata(Clause(u1, -u2, 0, 0));
			ata(Clause(-u1, u2, 0, 0));
			flip = 0;
		}
		if (DISPLAY_LEVEL > SWAP_LEVEL) {
			cout << "induction level" << i << endl;
		}
	}

	ata(Clause(invector[n-1] , invector[n - 2], 0, 0));
	ata(Clause(invector[n-1]  , -invector[n - 2], 0, 0));
	ata(Clause(-invector[n-1], invector[n - 2], 0, 0));
	ata(Clause(-invector[n-1], -invector[n - 2], 0, 0));

	ata(Clause(-invector[n-1], 0 , 0, 0));
	ata(Clause(invector[n-1], 0, 0, 0));

	ata(Clause(0, 0, 0, 0));

}

std::vector<int> uniform_random(int n) {
	std::vector<int> the_vector;
	for (int i = 0; i < n; i++) {
		the_vector.push_back(i + 1);
	}
	for (int i = 0; i < the_vector.size(); i++) {
		int r = i + rand() % (the_vector.size() - i); // careful here!
		swap(the_vector[i], the_vector[r]);
		//cout << i << " " << r << " " << myvector[i] << endl;
	}
	return the_vector;
}

std::vector<int> distance_bounded_random(int n, int k) {
	std::vector<int> the_vector;
	for (int i = 0; i < n; i++) {
		the_vector.push_back(i + 1);
	}
	
	int d = n;
	std::vector<int> best_vector = the_vector;
	int best_distance = n;
	int j = 0;
	while (d>k && j< 10000000) {
		j++;
		for (int i = 0; i < the_vector.size(); i++) {
			int r = i + rand() % (the_vector.size() - i); // careful here!
			swap(the_vector[i], the_vector[r]);
			//cout << i << " " << r << " " << myvector[i] << endl;
		}
		int max_distance=0;
		for (int i = 0; i < n; i++) {
			if (abs(the_vector[i]-(i+1)) > max_distance) {
				max_distance = abs(the_vector[i] - (i + 1));
			}
		}
		if (max_distance < best_distance) {
			best_distance = max_distance;
			best_vector = the_vector;
		}
		d = max_distance;
	}
		cout << "best distance is: " << best_distance << endl;
	return best_vector;
}


std::vector<int> clique_minor(int n, int k) {
	std::vector<int> the_vector;
	for (int i = 0; i < n; i++) {
		the_vector.push_back(i+1);
	}
	
	while(n < (k * (k - 3) + 2)) {
		k--;
	}
	the_vector[k * (k - 3) + 1] = 2;
	the_vector[1] = k * (k - 3) + 2;
	//std::cout << "myvector 0: " << the_vector[0] << endl;
	//std::cout << "myvector " << n - 1 << ": " << the_vector[n - 1] << endl;
	int in;
	int out = 2;
	for (int i = 0; i<k - 2; i++) {
		if (i == 0) {
			for (int j = i; j<k - 3; j++) {
				in = i * (k - 3) + j + 1;
				out++;
				the_vector[in] = out;
				//std::cout << "i" << i << "j"<< j << "myvector " << in << ": " << out<< endl;
				in = (j + 2)*(k - 3) + i + 1;
				out++;
				the_vector[in] = out;
				//std::cout << "myvector " << in << ": " << out<< endl;
			}
		}
		else {
			for (int j = i - 1; j<k - 3; j++) {
				in = i * (k - 3) + j + 1;
				out++;
				the_vector[in] = out;
				//std::cout  << "i" << i << "j"<< j<< "myvector " << in << ": " << out<< endl;
				if (j<k - 4) {
					in = (j + 3)*(k - 3) + i + 1;
				}
				else {
					in = (j + 3)*(k - 3) + i;
				}
				out++;
				the_vector[in] = out;
				//std::cout << "myvector " << in << ": " << out<< endl;
			}

		}
	}
	return the_vector;
}

std::vector<int> random_swaps(int n, int k) {
	std::vector<int> the_vector;
	for (int i = 0; i < n; i++) {
		the_vector.push_back(i + 1);
	}
	for (int i = 0; i < k; i++) {
		int r = rand() % (the_vector.size() - 1); // careful here!
		swap(the_vector[r], the_vector[r+1]);
	}
	cout <<  k << " random adjacent swaps" << endl;
	return the_vector;
}

int main (int argc, char** argv) {
	int n = 100;
	int k = n;
	int seed = 12345;
	char* fname = NULL;
	//char** argv= "-o pr";
	if (argc > 1) {
		if (argv[1][0] == '-') { printf("c first parameter needs to be a positive number\n"); return 0; }
		n = atoi(argv[1]);
	}
	else { printf("c need to provide size\n"); return 0; }

	std::vector<int> myvector;
	std::vector<int> filevector;
	::file_reading = 0;
	ifstream checker;
	checker.open("input.txt", ios::app);
	int a;
	int i = 0;
	while ((checker >> a)&& (i<4)) {
		i++;
		if (i == 4) {
			::file_reading =1;
			cout << "detected input.txt" << endl;
		}
	}
	checker.close();

	if (::file_reading == 1) {
		std:fstream myfile("input.txt", std::ios_base::in);
		int a;
		int i = 0;
		while (myfile >> a) {
				filevector.push_back(a);
				i++;
		}
		
		std::vector<int> checkvector;
		//checking bijectivity
		for (int j = 0; j < i; j++) {
			checkvector.push_back(0);
		}
		for (int j = 0; j < i; j++) {
			checkvector[filevector[j]-1]++;
		}
		for (int j = 0; j < i; j++) {
			if (checkvector[j] != 1) {
				cout << "input.txt is not a permutation, reverting to seed" << endl;
				::file_reading = 0;
				break;
			}
		}
		if (::file_reading == 1) {
			n = i;
			myvector = filevector;
		}

	}
	
//	std::string fname = "output";
        //const char* fname="test800";

 

	if (n < 4) {
		cout << "ERROR: n is too small";
		//getchar();
		return 0;
	}
	
		cout << "Running using size " << n << endl;

      if ((argc > 2) && (argv[2][0] != '-')) seed = atoi (argv[2]);
	srand(seed);
	if (::file_reading == 0) {
		cout << "Running using seed " << seed << endl;
	}
	for (int i = 1; i < argc; i++) {
		if (argv[i][0] == '-') {
			if (argv[i][1] == 'o') {
				file_writing = 1;
                                if (argc == i + 1) { printf ("c file name missing after -o\n"); 
								return 0;
								//strcat(fname, to_cstr(std::move(ss).str()));
								}
								else {
									fname = argv[i + 1];
								}
			}
			if (argv[i][1] == 'm') {
				distribution_mode= atoi(argv[i+1]);
				k= atoi(argv[i + 2]);
			}
		}

	}

//	if (::file_writing) {
//		cout << "Enter a file name to write to file" << endl;
//		fname = read_line();
//	}
//	string cnf_name_s = (fname + ".cnf");
//	string proof_name_s = (fname + ".drat");
//	const char* cnf_name = cnf_name_s.c_str();
//	const char* proof_name = proof_name_s.c_str();
	char cnf_name[100];
	char proof_name[100];
	char graph_name[100];
	char stats_name[100];
	if (::file_writing) {
                strcpy(cnf_name, fname);
                strcat(cnf_name, ".cnf");
                strcpy(proof_name, fname);
                strcat(proof_name, ".drat");
				strcpy(graph_name, fname);
				strcat(graph_name, ".gr");
				strcpy(stats_name, fname);
				strcat(stats_name, "_stats.txt");

		if (remove(proof_name) != 0)
		{	printf("No file to replace creating new %s file\n", proof_name); }
		else
			puts("File successfully deleted");
		if (remove(cnf_name) != 0)
		{	printf("No file to replace creating new %s file\n", cnf_name); }
		else
			puts("File successfully deleted");
		if (remove(graph_name) != 0)
		{
			printf("No file to replace creating new %s file\n", graph_name);
		}
		else
			puts("File successfully deleted");
		if (remove(stats_name) != 0)
		{
			printf("No file to replace creating new %s file\n", stats_name);
		}
		else
			puts("File successfully deleted");
	}
	//std::srand(unsigned(std::time(0)));
	

	// set some values:
	if (file_reading == 0) {
		for (int i = 1; i < n + 1; ++i) myvector.push_back(i); // 1 2 3 4 5 6 7 8 9
	}
	//ER stuff in main
	for (int i = 1; i<=3 * n - 6; ++i) ::extvariables.push_back(i); // 1 2 3 4 5 6 7 8 9
	::max_ext_var = 3 * n - 6;
	//::er_proof_only = ERPROOFONLY;

	// using myrandom:
//	std::random_shuffle(myvector.begin(), myvector.end(), order_random);
//	std::shuffle(myvector.begin(), myvector.end(), order_random);
	

	if (::file_reading == 0) {
		// uniform distribution
		
		if (::distribution_mode == 0) {
			myvector = uniform_random(n);
		}
		if (::distribution_mode == 1) {
			myvector = distance_bounded_random(n, k);
		}
		if (::distribution_mode == 2) {
			myvector = clique_minor(n, k);
		}
		if (::distribution_mode == 3) {
			myvector = random_swaps(n, k);
		}

	}
	else {
		cout << "shuffling skipped" << endl;
		//getchar();
	}

	// print out content:
	/*
	std::cout << "myvector contains:";
	for (std::vector<int>::iterator it = myvector.begin(); it != myvector.end(); ++it)
		std::cout << ' ' << *it;

	std::cout << '\n';
	*/
	ofstream vec_dump;
	if (::file_writing) {
		cout << "creating " << stats_name << endl;
		vec_dump.open(stats_name, ios::app);
		//stats << " n " << "\t" << "s" << "\t" << "#vars" << "\t" << "#c " << "\t" << "#lines" << "\t" << "#add" << "\t" << "#del" << "\t" <<  "time elapsed "  << endl;
		//stats << n << "\t" << seed << "\t" << ::max_ext_var << "\t" << 8 * (n - 2) << "\t" << ::proof_size << "\t" << ::ata_size + ::rata_size << "\t" << ::ate_size + ::rate_size << "\t" << duration << endl;
		for (int i = 0; i < myvector.size(); i++) {
			vec_dump << myvector[i] << " ";
			//cout << i << " " << r << " " << myvector[i] << endl;
		}
		vec_dump.close();
	}

	double duration;
	std::clock_t start;

	start = std::clock();
	if (::file_writing) {
		cout << "creating " << cnf_name << endl;
	}
	//Clause C = Clause(-1, 2, 3, 4);
	int negativelit = order_random(n);
	Cnf P= parity(n-2, myvector, negativelit);
	//C.Display();
	::max_ext_var = 3 * n - 6;
	std::vector<int> revvector= myvector;

	for (int i = 1; i < n+1; i++) {
		revvector[myvector[i-1]-1] = i;
	}

	//Tseitin Graph creation
	Edge_Graph tseitin;
	Cnf cnf_tseitin;

	for (int i = 1; i < n - 2; i++) {
		tseitin.add(i, i + 1);
		cnf_tseitin.add_clause(Clause(i, i + 1, 0, 0));
	}
	for (int i = 1; i < n - 2; i++) {
		tseitin.add(n - 2 + i, n - 2 + i + 1);
		cnf_tseitin.add_clause(Clause(n - 2 + i, n - 2 + i + 1, 0, 0));
	}
	if ((myvector[0]>1) && (myvector[0]<n)) {
		tseitin.add(myvector[0] - 1, n - 1);
		cnf_tseitin.add_clause(Clause(myvector[0] - 1, n - 1, 0, 0));
	}
	if ((myvector[0] == 1)) {
		tseitin.add(1, n - 1);
		cnf_tseitin.add_clause(Clause(1, n - 1, 0, 0));
	}
	if ((myvector[0] == n)) {
		tseitin.add(n - 2, n - 1);
		cnf_tseitin.add_clause(Clause(n - 2, n - 1, 0, 0));
	}
	for (int i = 1; i < n - 1; i++) {
		if ((myvector[i]>1) && (myvector[i]<n)) {
			tseitin.add(myvector[i] - 1, n - 2 + i);
			cnf_tseitin.add_clause(Clause(myvector[i] - 1, n - 2 + i, 0, 0));
		}
		if ((myvector[i] == 1)) {
			tseitin.add(1, n - 2 + i);
			cnf_tseitin.add_clause(Clause(1, n - 2 + i, 0, 0));
		}
		if ((myvector[i] == n)) {
			tseitin.add(n - 2, n - 2 + i);
			cnf_tseitin.add_clause(Clause(n - 2, n - 2 + i, 0, 0));
		}


	}
	//tseitin.add(myvector[n-1],2*n-4);
	if ((myvector[n - 1]>1) && (myvector[n - 1]<n)) {
		tseitin.add(myvector[n - 1] - 1, 2 * n - 4);
		cnf_tseitin.add_clause(Clause(myvector[n - 1] - 1, 2 * n - 4, 0, 0));
	}
	if ((myvector[n - 1] == 1)) {
		tseitin.add(1, 2 * n - 4);
		cnf_tseitin.add_clause(Clause(1, 2 * n - 4, 0, 0));
	}
	if ((myvector[n - 1] == n)) {
		tseitin.add(n - 2, 2 * n - 4);
		cnf_tseitin.add_clause(Clause(n - 2, 2 * n - 4, 0, 0));
	}
	/*
	std::cout << "revvector contains:";
	for (std::vector<int>::iterator it = revvector.begin(); it != revvector.end(); ++it)
		std::cout << ' ' << *it;

	std::cout << '\n';
	*/
	if (::file_writing) {
		::file_cnf = fopen(cnf_name, "w");
		
		//cnffile << "p cnf " << 3 * n -6 << " " << P.cspace << "\n";

		::f = P;
		//::f.Display();
		::f.print(::file_cnf);

		fclose(::file_cnf);
		duration = (std::clock() - start) / (double)CLOCKS_PER_SEC;
		std::cout << "time for constructing CNF" << duration << endl;
		//::reverse.print();
	}
	if (::file_writing) {
		::file_graph = fopen(graph_name, "w");
		::g = tseitin;
		if (::file_writing) {
			cout << "creating " << graph_name << endl;
		}
		//::g.print(::file_graph);
		cnf_tseitin.print_gr(::file_graph);
		fclose(::file_graph);
	}
	bool skip_prvr = 0;

	//getchar();
	if (!skip_prvr){
		if (::file_writing) {
			cout << "creating " << proof_name << endl;
		}
		std::clock_t start2;
		if (::file_writing) {
			::file_proof = fopen(proof_name, "w");
		}
		start2 = std::clock();
		::main_tree = rebalance(::main_tree, 0);
		//::reverse.print();
		//getchar();

		swapping(n - 2, f, revvector);
		//::reverse.print();
		//getchar();
		linear_tree(::main_tree, 0, 1, n - 2);
		//getchar();
		myvector[negativelit] = -myvector[negativelit];
		final_equiv(n, myvector);

		//::myfile.close();
		if (::file_writing) {
			fclose(::file_proof);
		}
		duration = (std::clock() - start2) / (double)CLOCKS_PER_SEC;
		cout << "time elapsed " << duration << endl;
		cout << "number of ATA lines " << ::ata_size << endl;
		cout << "number of RATA lines " << ::rata_size << endl;
		cout << "number of ATE lines " << ::ate_size << endl;
		cout << "number of RATE lines " << ::rate_size << endl;
		cout << " n " << "\t" << "#vars " << "\t" << "#c " << "\t" << "#lines" << "\t" << "#add" << "\t" << "#del" << "\t" << endl;
		cout << n << "\t" << ::max_ext_var << "\t" << 8 * (n - 2) << "\t" << ::proof_size << "\t" << ::ata_size + ::rata_size << "\t" << ::ate_size + ::rate_size << endl;

		ofstream stats; 
		if (::file_writing) {
			stats.open(stats_name, ios::app);
			stats <<" \n\n n " << "\t" << "s" << "\t" << "#vars" << "\t" << "#c " << "\t" << "#lines" << "\t" << "#add" << "\t" << "#del" << "\t" <<  "time elapsed "  << endl;
			stats << n << "\t" << seed << "\t" << ::max_ext_var << "\t" << 8 * (n - 2) << "\t" << ::proof_size << "\t" << ::ata_size + ::rata_size << "\t" << ::ate_size + ::rate_size << "\t" << duration << endl;
			stats.close();
		}
		//getchar();
	}
}
