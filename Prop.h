#pragma once
#include <iostream>
#include <fstream>
#include <array>
#include <vector>       // std::vector
//#include <string.h>
using namespace std;

struct Clause {
	int lit[4];	// maximum width 4 is all we need
				// use 0 to denote empty slots in clauses

	Clause(int a, int b, int c, int d) {
		lit[0] = a;
		lit[1] = b;
		lit[2] = c;
		lit[3] = d;
	}

	Clause() {
		lit[0] = 0;
		lit[1] = 0;
		lit[2] = 0;
		lit[3] = 0;
	};

	void display() {
		for (int i = 0; i < 4; i++) {
			cout << lit[i] << " ";
		}
		cout << endl;
	};

	void print(FILE *cnf) {
		for (int i = 0; i < 4; i++) {

			if (lit[i] == 0) {
				break;
			}
			fprintf(cnf, "%i", lit[i]);
			fprintf(cnf, " ");
		}
		fprintf(cnf, "0\n");
	};

	bool empty() {
		for (int i = 0; i < 4; i++) {
			if (lit[i] != 0) { return false; }
		}
		return true;
	}
};

struct C_Node {
	Clause data;
	C_Node *next;
};

class Cnf
{
private:
	//array pointer for first clause
	C_Node * head, *tail;
public:
	int clause_space;
public:
	Cnf()
	{
		clause_space = 0;
		head = NULL;
		tail = NULL;
	}
public:

	bool is_empty() { //checks if empty CNF
		return clause_space == 0;
	}
	Clause choose_clause(int pos) {

		{
			C_Node *current;
			current = head;
			for (int i = 0; i<pos; i++)
			{
				current = current->next;
			}
			return current->data;
		}
	}
	void add_clause(Clause C) {
		//clauses[cspace] = C;
		C_Node *temp = new C_Node;
		temp->next = NULL;
		temp->data = C;
		
		if (head == NULL) {
			head = temp;
			tail = temp;
			temp = NULL;
		}
		else {
			
			tail->next = temp;
			tail = temp;
		}
		clause_space++;
	}

	bool emp_clause() {
		int c = clause_space;
		for (int i = 0; i < c; i++)
		{
			Clause C = choose_clause(i);
			if (C.empty())
			{
				return 1;
			}

		}
		return 0;
	}

	void display() {
		C_Node *temp = new C_Node;
		temp = head;
		while (temp != NULL) {
			temp->data.display();
			temp = temp->next;
		}


	}

	void print(FILE *cnf) {
		C_Node *temp = new C_Node;
		temp = head;
		while (temp != NULL) {
			temp->data.print(cnf);
			temp = temp->next;
		}

	}

	void rmv_clause_simplf(int pos) {
		if (pos == 0) {
			head = head->next;
		}
		else {
			C_Node *current = new C_Node;
			C_Node *previous = new C_Node;
			current = head;
			for (int i = 0; i<pos; i++)
			{
				previous = current;
				current = current->next;
			}
			previous->next = current->next;
			delete &current;
			delete current;
			delete previous;
		}
		clause_space--;
	}
};

Cnf cnf_merge(Cnf a, Cnf b) {
	Clause C;
	while (b.is_empty() == 0) {
		C = b.choose_clause(0);
		a.add_clause(C);
		b.rmv_clause_simplf(0);
	}
	return a;
}

struct IntCnfPair {
	Cnf thecnf;
	int theint;
	IntCnfPair(int j, Cnf f) {
		thecnf = f;
		theint = j;
	};
	IntCnfPair() {
	};
};

struct BoolCnfPair {
	Cnf thecnf;
	bool theint;
	BoolCnfPair(int j, Cnf f) {
		thecnf = f;
		theint = j;
	};
	BoolCnfPair() {
	};
};

struct SwapSelCombo {
	int lbound;
	int ubound;
	bool lr;
	int tries;

	SwapSelCombo(int lb, int ub, bool the_bool, int the_tries) {
		lbound = lb;
		ubound = ub;
		lr = the_bool;
		tries = the_tries;
	};
};
