#pragma once

struct Int_Edge{ //purely integer edges used to form tseitin graphs
	int node1;
int node2;

Int_Edge(int x, int y) {
	node1 = x;
	node2 = y;
}

Int_Edge() {
	node1 = 0;
	node2 = 0;
}

void display() {
	std::cout << "(" << node1 << "," << node2 << ")";
}

void print(FILE *graph) {
	fprintf(graph, "(");
	fprintf(graph, "%i", node1);
	fprintf(graph, ",");
	fprintf(graph, "%i", node2);
	fprintf(graph, ")");
}
};

struct Edge_Graph_Node {
	Int_Edge data;
	Edge_Graph_Node *next;

	Edge_Graph_Node(int x, int y) {
		data = Int_Edge(x, y);
		next = nullptr;
	}

	Edge_Graph_Node() {
		data = Int_Edge();
		next = nullptr;
	}
};

struct Edge_Graph {
	Edge_Graph_Node *head;
	Edge_Graph_Node *tail;

	Edge_Graph() {
		head = nullptr;
		tail = nullptr;
	}

	void add(int x, int y) {
		Edge_Graph_Node *temp = new Edge_Graph_Node;
		temp->next = NULL;
		temp->data = Int_Edge(x, y);

		if (head == NULL) {
			head = temp;
			tail = temp;
			temp = NULL;
		}
		else {

			tail->next = temp;
			tail = temp;
		}
	}

	void display() {
		Edge_Graph_Node *temp = new Edge_Graph_Node;
		temp = head;
		std::cout << "[";
		while (temp != NULL) {
			temp->data.display();
			std::cout << ",";
			temp = temp->next;
		}
		std::cout << "]" << std::endl;

	}

	void print(FILE *graph) {
		Edge_Graph_Node *temp = new Edge_Graph_Node;
		temp = head;
		fprintf(graph, "[");
		while (temp != NULL) {
			temp->data.print(graph);
			fprintf(graph, ",");
			temp = temp->next;
		}
		fprintf(graph, "]");
	}

};
struct P_Node {
	int input;
	int output;
	P_Node *next;

	P_Node(int x, int y) {
		input = x;
		output = y;
		next = nullptr;
	}

	P_Node() {
		input = 0;
		output = 0;
		next = nullptr;
	};
};


struct T_Node {
	int data;
	bool lr;
	//int depth;
	T_Node *child1;
	T_Node *child2;
	T_Node *child3;
	T_Node *parent;
	T_Node(int i) {
		data = i;
		lr = 0;
		child1 = NULL;
		child2 = NULL;
		child3 = NULL;
		parent = NULL;
	};
	void print_rt(int dp) {

		std::cout << data; // print label after last label
		if (child1 != NULL) {
			std::cout << "_\t_";
			child1->print_rt(dp+1);
		}
		else { std::cout << "\t"; }
		if (child2 != NULL) {
			std::cout << std::endl;
			for (int i = 0; i < dp; i++) {
				std::cout << " \t";
			}
			if (dp > 0) {
				std::cout << " \\";
			}
			std::cout << std::endl;
			for (int i = 1; i < dp+1; i++) {
				std::cout << "\t";
			}
				std::cout << "   -\t";
			std::cout << "_";
			child2->print_rt(dp+1);
		}
	};
};

struct Cnftnodepair {
	T_Node* nodestar;
	Cnf form;
};


struct Tree {
	T_Node * source;
	int depth;
	int end_lit1;
	int end_lit2;
	Tree(int i) {
		T_Node *temp = new T_Node(i);
		source = temp;
		depth = 1;
		end_lit1 = 0;
		end_lit2 = 0;
	};

	T_Node* cm_ancestor(T_Node* a, T_Node* b) {
		stack<T_Node*> stk1;
		stack<T_Node*> stk2;
		T_Node* current;
		current = a;
		while (current != nullptr) {
			stk1.push(current);
		}
		current = b;
		while (current != nullptr) {
			stk2.push(current);
		}

		while (stk1.top() == stk2.top()) {
			current = stk1.top();
			stk1.pop();
			stk2.pop();
		}

		return current;

	}

	void print() {
		source->print_rt(0);
		cout<<endl;
	};

	Tree(T_Node* s) {
		source = s;
//		s->parent;
	};

	T_Node* int_find_node(int i, T_Node* base) { // find node with data i;
		if (base->data == i) {
			return base;
		}
		T_Node* q;
		if (base->child1 != NULL) {
			q = int_find_node(i, base->child1);
			if (q != NULL) {
				return q;
			}
		}
		if (base->child2 != NULL) {
			q = int_find_node(i, base->child1);
			if (q != NULL) {
				return q;
			}
		}
		return NULL;
	};

	T_Node* int_find_node(int i) {
		return int_find_node(i, source);
	}


	

	void tree_shift_r(T_Node* pivot) {
		T_Node* elim;
		//first eliminate our node
		elim = pivot->child1;
		//new child1 is grandchild of pivot from elim side
		pivot->child1 = elim->child1;
		elim->child1->parent = pivot;
		

		//elim moves child2 to child 1
		elim->child1 = elim->child2;
		elim->child1->lr = 0;

		//child2 becomes child2 of elim
		pivot->child2->parent = elim;
		elim->child2 = pivot->child2;
		elim->child2->lr = 1;
		
		//elim becimes new child2 of pivot
		pivot->child2 = elim;
		pivot->child2->lr= 1;
		//elim->parent=pivot; but this is already true
	}

	void tree_shift_l(T_Node* pivot) {
		T_Node* elim;
		//first eliminate our node
		elim = pivot->child2;
		//new child2 is grandchild of pivot from elim side
		pivot->child2 = elim->child2;
		pivot->child2->lr = 1;
		elim->child2->parent = pivot;

		//elim moves child1 to child 2
		elim->child2 = elim->child1;
		elim->child2->lr = 1;

		//child1 becomes child1 of elim
		pivot->child1->parent = elim;
		elim->child1 = pivot->child1;
		elim->child1->lr = 0;

		//elim becimes new child1 of pivot
		pivot->child1 = elim;
		pivot->child1->lr = 0;
		//elim->parent=pivot; but this is already true
	}

	void tree_shift_r() {
		tree_shift_r(source);
	}

	void tree_shift_l() {
		tree_shift_l(source);

	}


	void extend_source(int i, int j, bool dir) {
		T_Node *temp1 = new T_Node(i);
		T_Node *temp2 = new T_Node(j);
		
		temp2->child1 = NULL;
		temp2->child2 = NULL; //temp 2 is an added leaf
		temp2->parent = temp1; //temp1 is the new source

		source->parent = temp1;

		if (dir == 1) {
			source->lr = 0;
			temp1->child1 = source;
			temp1->child1->lr = 0;
			temp1->child2 = temp2;
			temp1->child2->lr = 1;
			
		}
		else{
			source->lr = 1;
			temp1->child2 = source;
			temp1->child2->lr = 1;
			temp1->child1 = temp2;
			temp1->child1->lr = 0;
		}
		temp1->parent = NULL;
		source = temp1;
		depth++;
	}
};

struct Cnf_Tree {
	Cnf the_cnf;
	Tree the_tree;
};
