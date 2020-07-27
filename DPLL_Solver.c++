#include <algorithm>
#include <fstream>
#include <iostream>
#include <map>
#include <vector>
using namespace std;

/* 
 *  define data types for each boolean logic concepts
 */
#define Var int                 //variable
#define Lit int                 //literal
#define Clause vector<Lit>      //clause
#define Formula vector<Clause>  //formula
#define Asgmt vector<Lit>       //assignment map
#define SAT true
#define UNSAT false

class Solver {
   private:
    int numVar;
    int numClause;
    Formula formula;
    Asgmt satAsgmt;

    Var getVar(const Lit);
    Lit getLit(const Lit, const bool);
    void printAsgmt();
    void printFormula(const Formula);
    void applyAsgmt(Formula &, const Asgmt &);
    Formula BCP(Formula, Asgmt &);
    bool haveConflict(const Formula &);
    bool solve(Formula, Asgmt);
    Var chooseVar(Formula);

   public:
    Solver(fstream &fn);
    void solve();
};

Solver::Solver(fstream &fn) {
    fn >> this->numVar >> this->numClause;
    Lit literal;
    Clause clause;
    while (fn >> literal && this->formula.size() < this->numClause) {
        if (literal) {
            if (literal > numVar || literal < -numVar) {
                cerr << "Error: wrong clause!" << endl;
                exit(1);
            }
            clause.push_back(literal);
        } else {
            this->formula.push_back(clause);
            clause.clear();
        }
    }
}

void Solver::printAsgmt() {
    for (Var var = 1; var <= numVar; var++) {
        if (find(this->satAsgmt.begin(), this->satAsgmt.end(), -var) != this->satAsgmt.end())
            cout << -var << " ";
        else
            cout << var << " ";
    }
    cout << endl;
}

void Solver::printFormula(const Formula _formula) {
    for (auto &c : _formula) {
        for (auto &l : c) {
            cout << l << '\t';
        }
        cout << endl;
    }
}

/* 
 *  retrieve the var from a literal
 */
Var Solver::getVar(const Lit lit) {
    return (Var)(abs(lit));
}

/* 
 *  return a literal with specified
 *  var and its true value
 */
Lit Solver::getLit(const Lit var, const bool value) {
    return (Var)(value ? var : -var);
}

void Solver::applyAsgmt(Formula &_formula, const Asgmt &assignMap) {
    for (auto const &assign : assignMap) {
        for (auto it = _formula.begin(); it != _formula.end();) {
            //find true literal
            auto posLit = find(it->begin(), it->end(), assign);
            //find false literal
            auto negLit = find(it->begin(), it->end(), -assign);
            //erase the clause which has a true literal
            if (posLit != it->end()) {
                // cout << "delete clause" << endl;
                it = _formula.erase(it);
            } 
            //erase the false literal in the clause
            else if (negLit != it->end()) {
                // cout << "delete literal" << endl;
                it->erase(negLit);
            } else {
                ++it;
            }
        }
    }
    return;
}

Formula Solver::BCP(Formula _formula, Asgmt &assignMap) {
    //apply current assignments to variables
    applyAsgmt(_formula, assignMap);

    //unit resolution
    //find a unit clause and assign true
    //then update the assignment map
    for (auto it = _formula.begin(); it != _formula.end();) {
        if (it->size() == 1) {
            assignMap.push_back(it->front());
            applyAsgmt(_formula, assignMap);
            //search from the begining again
            it = _formula.begin();
        } else
            ++it;
    }
    return _formula;
}

bool Solver::haveConflict(const Formula &_formula) {
    Clause unitClause;
    for (auto const &clause : _formula) {
        // empty clause
        if (clause.size() == 0) {
            return true;
        }
        // detect a unit clause AND
        // its negation clause in formula
        else if (clause.size() == 1) {
            if (count(unitClause.begin(), unitClause.end(), -clause.front()))
                return true;
            else
                unitClause.push_back(clause.front());
        } 
        // detect a var and its negation
        // in a same clause
        else {
            for (auto const &lit : clause)
                if (find(clause.begin(), clause.end(), -lit) != clause.end())
                    return true;
        }
    }
    return false;
}

/* 
 *  choose the first var in the 
 *  first clause of current formula
 */
Var Solver::chooseVar(Formula _formula) {
    return getVar(_formula.front().front());
}

/* 
 *  main function of the solver
 *  which implements DPLL algorithm
 */
bool Solver::solve(Formula _formula, Asgmt assignMap) {
    //boolean constraint propagation on input formula
    Formula resolvent = BCP(_formula, assignMap);

    // cout<<"BCP resolvent:"<<endl;
    // printFormula(resolvent);

    //Formula is true if no more clauses left
    if (resolvent.size() == 0) {
        this->satAsgmt = assignMap;
        return SAT;
    }

    //Formula becomes false if a conflict 
    //is derived due to unit resolution
    if (haveConflict(resolvent)) {
        // cout<<"conlict detected!"<<endl;
        return UNSAT;
    }

    //choose a var to be assigned
    Var selectedVar = chooseVar(resolvent);

    //assign true or false to selected var
    Asgmt _assignMap(assignMap);
    assignMap.push_back(getLit(selectedVar, true));
    _assignMap.push_back(getLit(selectedVar, false));

    //recursively solving with assigned vars
    // cout << "assign: " << selectedVar << " to ture"<<endl;
    if (solve(resolvent, assignMap) == SAT) return SAT;
    else {
        // cout << "assign: " << selectedVar << " to false"<<endl;
        return solve(resolvent, _assignMap);
    }
}

/* 
 *   A wrapper for actual solver.
 */
void Solver::solve() {
    Asgmt assignMap;
    if (solve(this->formula, assignMap) == SAT) {
        cout << "SAT" << endl;
        printAsgmt();
    } else
        cout << "UNSAT" << endl;
    return;
}

int main(int argc, char const *argv[]) {
    //validate input file
    if (argc <= 1) {
        cerr << "Error: No input cnf file!" << endl;
        exit(1);
    }
    string filename = argv[1];
    fstream fn(filename, ios_base::in);
    if (!fn.is_open()) {
        cerr << "Error: Can not open file!" << endl;
        exit(1);
    }

    Solver solver = Solver(fn);

    solver.solve();

    fn.close();
    return 0;
}
