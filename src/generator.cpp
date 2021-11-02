/*
 * File:	generator.cpp
 *
 * Description:	This file contains the public and member function
 *		definitions for the code generator for Simple C.
 *
 *		Extra functionality:
 *		- putting all the global declarations at the end
 */

# include <vector>
# include <iostream>
# include "generator.h"
# include "Register.h"
# include "machine.h"
# include "Tree.h"
# include <cassert>
# include "Label.h"
# include <map>

using namespace std;

static int offset;
static string funcname;


/* This needs to be zero for the next phase. */

# define SIMPLE_PROLOGUE 0


/* This shouid be set if we want to use the callee-saved registers. */

# define CALLEE_SAVED 0


/* The registers and their related functions */

typedef vector<Register *>Registers;

static Register *rax = new Register("%rax", "%eax", "%al");
static Register *rbx = new Register("%rbx", "%ebx", "%bl");
static Register *rcx = new Register("%rcx", "%ecx", "%cl");
static Register *rdx = new Register("%rdx", "%edx", "%dl");
static Register *rsi = new Register("%rsi", "%esi", "%sil");
static Register *rdi = new Register("%rdi", "%edi", "%dil");
static Register *r8 = new Register("%r8", "%r8d", "%r8b");
static Register *r9 = new Register("%r9", "%r9d", "%r9b");
static Register *r10 = new Register("%r10", "%r10d", "%r10b");
static Register *r11 = new Register("%r11", "%r11d", "%r11b");
static Register *r12 = new Register("%r12", "%r12d", "%r12b");
static Register *r13 = new Register("%r13", "%r13d", "%r13b");
static Register *r14 = new Register("%r14", "%r14d", "%r14b");
static Register *r15 = new Register("%r15", "%r15d", "%r15b");

static Registers registers;
static Registers parameters = {rdi, rsi, rdx, rcx, r8, r9};
static Registers caller_saved = {rax, rdi, rsi, rdx, rcx, r8, r9, r10, r11};

# if CALLEE_SAVED
static Registers callee_saved = {rbx, r12, r13, r14, r15};
# else
static Registers callee_saved = {};
# endif

static void assign(Expression *expr, Register *reg);
static void load(Expression *expr, Register *reg);
static void compute(Expression *result, Expression *left, Expression *right, const string &opcode);
static void relational(Expression *result, Expression *left, Expression *right, const string &opcode);
static void DivRem(Expression *result, Expression *left, Expression *right, const string &opcode);

map<string, Label> str_to_label;

Register *getreg() 
{
	for (unsigned i = 0; i < registers.size(); i++)
		if (registers[i]->_node == nullptr)
			return registers[i];
	
	load(nullptr, registers[0]);
	return registers[0];
}

/*
 * Function:	suffix (private)
 *
 * Description:	Return the suffix for an opcode based on the given size.
 */

static string suffix(unsigned long size)
{
    return size == 1 ? "b\t" : (size == 4 ? "l\t" : "q\t");
}


/*
 * Function:	suffix (private)
 *
 * Description:	Return the suffix for an opcode based on the size of the
 *		given expression.
 */

static string suffix(Expression *expr)
{
    return suffix(expr->type().size());
}


/*
 * Function:	align (private)
 *
 * Description:	Return the number of bytes necessary to align the given
 *		offset on the stack.
 */

static int align(int offset)
{
    if (offset % STACK_ALIGNMENT == 0)
	return 0;

    return STACK_ALIGNMENT - (abs(offset) % STACK_ALIGNMENT);
}


/*
 * Function:	operator << (private)
 *
 * Description:	Write an expression as an operand to the specified stream.
 *		This function first checks to see if the expression is in a
 *		register, and if not then uses its offset.
 */

static ostream &operator <<(ostream &ostr, Expression *expr)
{
    if (expr->_register != nullptr)
	return ostr << expr->_register;

    expr->operand(ostr);
    return ostr;
}


/*
 * Function:	Expression::operand
 *
 * Description:	Write an expression as an operand to the specified stream.
 */

void Expression::operand(ostream &ostr) const
{
    ostr << _offset << "(%rbp)";
}


/*
 * Function:	Identifier::operand
 *
 * Description:	Write an identifier as an operand to the specified stream.
 */

void Identifier::operand(ostream &ostr) const
{
    if (_symbol->_offset == 0)
	ostr << global_prefix << _symbol->name() << global_suffix;
    else
	ostr << _symbol->_offset << "(%rbp)";
}


/*
 * Function:	Number::operand
 *
 * Description:	Write a number as an operand to the specified stream.
 */

void Number::operand(ostream &ostr) const
{
    ostr << "$" << _value;
}


/*
 * Function:	Call::generate
 *
 * Description:	Generate code for a function call expression.
 */

static void findBaseAndOffset(Expression *expr, Expression *&base, int &offset)
{
	int field;
	base = expr;
	offset = 0;
	
	while (base->isField(base, field))
		offset += field;
}

void Call::generate()
{
    unsigned long value, size, bytesPushed = 0;


    /* Generate any arguments with function calls first. */

    for (int i = _args.size() - 1; i >= 0; i --)
	if (_args[i]->_hasCall)
	    _args[i]->generate();


    /* Adjust the stack if necessary. */

    if (_args.size() > NUM_PARAM_REGS) {
	bytesPushed = align((_args.size() - NUM_PARAM_REGS) * SIZEOF_PARAM);

	if (bytesPushed > 0)
	    cout << "\tsubq\t$" << bytesPushed << ", %rsp" << endl;
    }


    /* Move the arguments into the correct registers or memory locations. */

    for (int i = _args.size() - 1; i >= 0; i --) {
	size = _args[i]->type().size();

	if (!_args[i]->_hasCall)
	    _args[i]->generate();

	if (i < NUM_PARAM_REGS)
	    load(_args[i], parameters[i]);

	else {
	    bytesPushed += SIZEOF_PARAM;

	    if (_args[i]->_register)
		cout << "\tpushq\t" << _args[i]->_register->name() << endl;
	    else if (_args[i]->isNumber(value) || size == SIZEOF_PARAM)
		cout << "\tpushq\t" << _args[i] << endl;
	    else {
		load(_args[i], rax);
		cout << "\tpushq\t%rax" << endl;
	    }
	}

	assign(_args[i], nullptr);
    }


    /* Spill any caller-saved registers still in use. */

    for (unsigned i = 0; i < caller_saved.size(); i ++)
	load(nullptr, caller_saved[i]);


    /* Call the function.  Technically, we only need to assign the number
       of floating point arguments to %eax if the function being called
       takes a variable number of arguments.  But, it never hurts. */

    if (_id->type().parameters() == nullptr)
	cout << "\tmovl\t$0, %eax" << endl;

    cout << "\tcall\t" << global_prefix << _id->name() << endl;


    /* Reclaim the space of any arguments pushed on the stack. */

    if (bytesPushed > 0)
	cout << "\taddq\t$" << bytesPushed << ", %rsp" << endl;

    assign(this, rax);
}


/*
 * Function:	Block::generate
 *
 * Description:	Generate code for this block, which simply means we
 *		generate code for each statement within the block.
 */

void Block::generate()
{
    for (unsigned i = 0; i < _stmts.size(); i ++)
	_stmts[i]->generate();
}


/*
 * Function:	Simple::generate
 *
 * Description:	Generate code for a simple (expression) statement, which
 *		means simply generating code for the expression.
 */

void Simple::generate()
{
    _expr->generate();
    assign(_expr, nullptr);
}


/*
 * Function:	Function::generate
 *
 * Description:	Generate code for this function, which entails allocating
 *		space for local variables, then emitting our prologue, the
 *		body of the function, and the epilogue.
 *
 *		The stack must be aligned at the point at which a function
 *		begins execution.  Since the call instruction pushes the
 *		return address on the stack and each function is expected
 *		to push its base pointer, we adjust our offset by that
 *		amount and then perform the alignment.
 *
 *		On a 32-bit Intel platform, 8 bytes are pushed (4 for the
 *		return address and 4 for the base pointer).  Since Linux
 *		requires a 4-byte alignment, all we need to do is ensure
 *		the stack size is a multiple of 4, which will usually
 *		already be the case.  However, since OS X requires a
 *		16-byte alignment (thanks, Apple, for inventing your own
 *		standards), we will often see an extra amount of stack
 *		space allocated.
 *
 *		On a 64-bit Intel platform, 16 bytes are pushed (8 for the
 *		return address and 8 for the base pointer).  Both Linux and
 *		OS X require 16-byte alignment.
 */

void Function::generate()
{
# if 1
    unsigned size;
    int param_offset;
    Parameters *params = _id->type().parameters();
    const Symbols &symbols = _body->declarations()->symbols();


    /* Assign offsets to all symbols within the scope of the function. */

    param_offset = PARAM_OFFSET + SIZEOF_REG * callee_saved.size();
    offset = param_offset;
    allocate(offset);


    /* Generate the prologue. */

    funcname = _id->name();
    cout << global_prefix << funcname << ":" << endl;
    cout << "\tpushq\t%rbp" << endl;

    for (unsigned i = 0; i < callee_saved.size(); i ++)
	cout << "\tpushq\t" << callee_saved[i] << endl;

    cout << "\tmovq\t%rsp, %rbp" << endl;

    if (SIMPLE_PROLOGUE) {
	offset -= align(offset - param_offset);
	cout << "\tsubq\t$" << -offset << ", %rsp" << endl;
    } else {
	cout << "\tmovl\t$" << funcname << ".size, %eax" << endl;
	cout << "\tsubq\t%rax, %rsp" << endl;
    }


    /* Spill any parameters. */

    for (unsigned i = 0; i < NUM_PARAM_REGS; i ++)
	if (i < params->size()) {
	    size = symbols[i]->type().size();
	    cout << "\tmov" << suffix(size) << parameters[i]->name(size);
	    cout << ", " << symbols[i]->_offset << "(%rbp)" << endl;
	} else
	    break;


    /* Generate the body and epilogue. */

    registers = (_hasCall && callee_saved.size() ? callee_saved : caller_saved);
    _body->generate();

    cout << endl << global_prefix << funcname << ".exit:" << endl;
    cout << "\tmovq\t%rbp, %rsp" << endl;

    for (int i = callee_saved.size() - 1; i >= 0; i --)
	cout << "\tpopq\t" << callee_saved[i] << endl;

    cout << "\tpopq\t%rbp" << endl;
    cout << "\tret" << endl << endl;


    /* Finish aligning the stack. */

    if (!SIMPLE_PROLOGUE) {
	offset -= align(offset - param_offset);
	cout << "\t.set\t" << funcname << ".size, " << -offset << endl;
    }

    cout << "\t.globl\t" << global_prefix << funcname << endl << endl;

# else

    /* This is really all the students need to do. */

   	offset = 0;
    Parameters *params = _id->type().parameters();
    const Symbols &symbols = _body->declarations()->symbols();
    string parameters[] = {"%edi", "%esi", "%edx", "%ecx", "%r8d", "%r9d"};

    for (unsigned i = 0; i < symbols.size(); i ++)
	if (i < 6 || i >= params->size()) {
	    offset -= symbols[i]->type().size();
	    symbols[i]->_offset = offset;
	} else
	    symbols[i]->_offset = 16 + 8 * (i - 6);

    while (offset % 16 != 0)
	offset --;

    cout << global_prefix << _id->name() << ":" << endl;
    cout << "\tpushq\t%rbp" << endl;
    cout << "\tmovq\t%rsp, %rbp" << endl;
    cout << "\tsubq\t$" << -offset << ", %rsp" << endl;

    for (unsigned i = 0; i < 6; i ++)
	if (i < params->size()) {
	    cout << "\tmovl\t" << parameters[i] << ", ";
	    cout << symbols[i]->_offset << "(%rbp)" << endl;
	} else
	    break;

    _body->generate();

    cout << "\tmovq\t%rbp, %rsp" << endl;
    cout << "\tpopq\t%rbp" << endl;
    cout << "\tret" << endl << endl;
    cout << "\t.globl\t" << global_prefix << _id->name() << endl << endl;
# endif
}


/*
 * Function:	generateGlobals
 *
 * Description:	Generate code for any global variable declarations.
 */

void generateGlobals(Scope *scope)
{
    const Symbols &symbols = scope->symbols();

    for (unsigned i = 0; i < symbols.size(); i ++)
		if (!symbols[i]->type().isFunction()) {
	    	cout << "\t.comm\t" << global_prefix << symbols[i]->name() << ", ";
	    	cout << symbols[i]->type().size() << endl;
	}

	for (auto &i : str_to_label) {
		cout << i.second << ":\t.asciz\t" << i.first << endl;
	}
}

/*
 * Function:	Assignment::generate
 *
 * Description:	Generate code for an assignment statement.
 */
/*
void Assignment::generate()
{
	_right->generate();
	if (_right->_register == nullptr)
		load(_right, getreg());
	
	if(_left->isDereference(_left)) {
		_left->generate();
		
		if (_left->_register == nullptr)
			load(_left, getreg());
			
		cout << "\tmov" << suffix(_right) << _right << ", (" << _left->_register << ")" << endl;
	} else {
		cout << "\tmov" << suffix(_left) << _right << ", " << _left << endl;
		assign(_left, nullptr);
	}
	assign(_right, nullptr);
}
*/


// TODO: VERSION FOR STRUCTS 
void Assignment::generate()
{
	_right->generate();
	int offset;
	Expression *base;
	findBaseAndOffset(_left, base, offset);
	if (_right->_register == nullptr)
		load(_right, getreg());
	
	if(base->isDereference(_left)) { 
		_left->generate();
		cout << "# taint1" << endl;
		
		
		if (_left->_register == nullptr)
			load(_left, getreg());

		if (base->isField(base, offset))
		{
			cout << "#taint2" << endl;
			//findBaseAndOffset(_left, base, offset);
			if (base->_register == nullptr)
				load(base, getreg());

			cout << "\tmov" << suffix(_right) << _right << ", " << offset << "(" << base << ")" << endl;
			assign(base, nullptr);
		} else
			cout << "\tmov" << suffix(_right) << _right << ", (" << _left->_register << ")" << endl;
	} else { 
		Expression *base;
		_left->generate();
		if (_left->isField(base, offset))
		{		
			cout << "#bungo" << endl;	
			//findBaseAndOffset(_left, base, offset);
			//if (base->_register == nullptr)
				//load(base, getreg());
			cout << "\tmov" << suffix(_right) << _right << ", " << offset << "+" << base << endl;
		} else
			cout << "\tmov" << suffix(_left) << _right << ", " << _left << endl;
		assign(_left, nullptr);
	}
	assign(_right, nullptr);
}

/*
 * Function:	assign (private)
 *
 * Description:	Assign the given expression to the given register.  No
 *		assembly code is generated here as only the pointers are
 *		updated.
 */

static void assign(Expression *expr, Register *reg)
{

	if (expr != nullptr) {
		if (expr->_register != nullptr)
			expr->_register->_node = nullptr;

		expr->_register = reg;
	}

	if (reg != nullptr) {
		if (reg->_node != nullptr)
			reg->_node->_register = nullptr;

		reg->_node = expr;
	}

}


/*
 * Function:	load (private)
 *
 * Description:	Load the given expression into the given register.
 *
 */

static void load(Expression *expr, Register *reg)
{	
	if (reg->_node != expr) {
		if (reg->_node != nullptr) {
			unsigned size = reg->_node->type().size();
			offset -= size;
			reg->_node->_offset = offset;
			cout << "\tmov" << suffix(reg->_node);
			cout << reg->name(size) << ", ";
			cout << offset << "(%rbp)" << endl;
		}
		
    	if (expr != nullptr) {
			cout << "\tmov" << suffix(expr) << expr;
			cout << ", " << reg->name(expr->type().size()) << endl;
    	} 

		assign(expr, reg);
	}
}

void Add::generate()
{
	compute(this, _left, _right, "add");
}

void Subtract::generate()
{
	compute(this, _left, _right, "sub");
}

void Multiply::generate()
{
	compute(this, _left, _right, "imul");
}

static void compute(Expression *result, Expression *left, Expression *right, const string &opcode)
{

	left->generate();
	right->generate();

	if (left->_register == nullptr)
		load(left, getreg());

	cout << "\t" << opcode << suffix(left);
	cout << right << ", " << left << endl;

	assign(right, nullptr);
	assign(result, left->_register);
}

void LessThan::generate()
{
	relational(this, _left, _right, "l");
}

void GreaterThan::generate()
{
	relational(this, _left, _right, "g");
}

void LessOrEqual::generate()
{
	relational(this, _left, _right, "le");
}

void GreaterOrEqual::generate()
{
	relational(this, _left, _right, "ge");
}

void Equal::generate()
{
	relational(this, _left, _right, "e");
}

void NotEqual::generate()
{
	relational(this, _left, _right, "ne");
}

static void relational(Expression *result, Expression *left, Expression *right, const string &opcode)
{
	left->generate();
	right->generate();
	
	if (left->_register == nullptr)
		load(left, getreg());
	
	cout << "\t" << "cmp" << suffix(right) << right << ", " << left << endl;
	cout << "\tset" << opcode <<"\t" << left->_register->name(1) << endl;
	cout << "\tmovzbl\t" << left->_register->name(1) << ", " << left << endl;

	assign(right, nullptr);
	assign(result, left->_register);
}

void Divide::generate()
{
	DivRem(this, _left, _right, "/");
}

void Remainder::generate()
{
	DivRem(this, _left, _right, "%");
}


static void DivRem(Expression *result, Expression *left, Expression *right, const string &opcode)
{	
	left->generate();
	right->generate();

	load(left, rax);
	load(right, rcx);
	load(nullptr, rdx);

	(left->type().size() == 8) ? (cout << "\tcqto" << endl) : (cout << "\tcltd" << endl);

	cout << "\tidiv" << suffix(left) << right << endl;

	assign(right, nullptr);
	
	(opcode == "%") ? (assign(result,rdx)) : (assign(result,rax));
}

void Negate::generate()
{
	_expr->generate();
	
	if (_expr->_register == nullptr)
		load(_expr, getreg());

	cout << "\tneg" << suffix(_expr) << _expr->_register << endl;
	
	assign(this, _expr->_register);
}

void Not::generate()
{
	_expr->generate();

	if (_expr->_register == nullptr)
		load(_expr, getreg());

	cout << "\tcmp" << suffix(_expr) << "$0, " << _expr->_register << endl;
	cout << "\tsete\t" << _expr->_register->name(1) << endl;
	cout << "\tmovzb" << suffix(_expr) << _expr->_register->name(1) << ", " <<  _expr->_register << endl;
	assign(this, _expr->_register);
}

void Cast::generate()
{
	_expr->generate();
	unsigned long source = _expr->type().size();
	unsigned long target = _type.size();

	// long to int
	if (_expr->_register == nullptr)
		load(_expr, getreg());
	if (target <= source) {
		assign(this, _expr->_register);
	} else { // int to long

		assign(this, getreg());

		cout << "\tmovslq\t" << _expr << ", " << this << endl;
		assign(_expr, nullptr);
	}
}

void Expression::test(const Label &label, bool ifTrue)
{
	generate();

	if (_register == nullptr)
		load(this, getreg());

	cout << "\tcmp" << suffix(this) << "$0, " << this << endl;
	cout << (ifTrue ? "\tjne\t" : "\tje\t") << label << endl;

	assign(this, nullptr);
}

void While::generate()
{
	Label loop, exit;

	cout << loop << ":" << endl;
	
	_expr->test(exit, false);
	_stmt->generate();
	
	cout << "\tjmp\t" << loop << endl;
	cout << exit << ":" << endl;
}

void If::generate()
{
	Label skip, exit;
	cout << "# starting If::generate()" << endl;
	if (_elseStmt == nullptr) {
		_expr->test(skip, false);
		_thenStmt->generate();
		cout << skip << ":" << endl;
	} else {
		_expr->test(skip, false);
		_thenStmt->generate();
		cout << "\tjmp\t" << exit << endl;
		cout << skip << ":" << endl;
		_elseStmt->generate();
		cout << exit << ":" << endl;
	}
	cout << "# ending If::generate()" << endl;
}

void Return::generate()
{
	_expr->generate();
	load(_expr, rax);
	cout << "\tjmp\t" << global_prefix << funcname << ".exit" << endl; 
	cout << "# ending return::generate()" << endl;
	assign(_expr, nullptr);
}

void LogicalQ(Expression *result, Expression *left, Expression *right, const string &param)
{
	//left->generate();
	//right->generate();
	Label skip, exit;
	if (param == "||")
	{
		cout << "# starting ||" << endl;
		left->test(skip, true);
		right->test(skip, true);


		if (result->_register == nullptr)
			assign(result, getreg());

		cout << "\tmovl\t$0, " << result << endl;
		cout << "\tjmp\t" << exit << endl;
		cout << skip << ":" <<  endl;
		cout << "\tmovl\t$1, " << result << endl;
		cout << exit << ":" << endl;
		cout << "# ending ||" << endl;
	} else if (param == "&&") {
		cout << "# starting &&" << endl;
		left->test(skip, false);
		right->test(skip, false);

		if (result->_register == nullptr)
			assign(result, getreg());

		cout << "\tmovl\t$1, " << result << endl;
		cout << "\tjmp\t" << exit << endl;
		cout << skip << ":" <<  endl;
		cout << "\tmovl\t$0, " << result << endl;
		cout << exit << ":" << endl;
		cout << "# ending &&" << endl;
	}

}

void LogicalAnd::generate()
{
	LogicalQ(this, _left, _right, "&&");
}

void LogicalOr::generate()
{
	LogicalQ(this, _left, _right, "||");
}

bool Expression::isDereference(Expression *&p)
{
	return false;
}

bool Dereference::isDereference(Expression *&p)
{
	p = _expr;
	return true;
}

/*
void Address::generate()
{
	Expression *p;
	if (!_expr->isDereference(p)) {
		assign(this, getreg());
		cout << "\tleaq\t" << _expr << ", " << this << endl;
	} else {
		p->generate();
		load(p, getreg());
		assign(this, p->_register);
	}
} */

// TODO: VERSION FOR STRUCTS
void Address::generate()
{
	cout <<"#brap" << endl;
	Expression *p;
	if (!_expr->isDereference(p)) {
		_expr->generate();
		assign(this, getreg());
		cout << "\tleaq\t" << _expr << ", " << this << endl;
	} else {
		p->generate();
		load(p, getreg());
		int offset = 0;
		Expression *base;
		if(_expr->isField(p, offset))
		{
			findBaseAndOffset(p, base, offset);
			cout << "\taddq\t" << "$" << offset << ", " << p << endl;
		} 
		assign(this, p->_register);
	}
}

void Dereference::generate()
{
	_expr->generate();
	if (_expr->_register == nullptr)
		load(_expr, getreg());
	
	/*cout << "\tmov" << suffix(this) << "(" << _expr->_register->name(8) << "), ";
	cout << getreg()->name(this->_type.size()) << endl;
	assign(this, getreg()); */
	cout << "\tmov" << suffix(this) << "(" << _expr->_register << "), ";
	assign(this, _expr->_register);
	cout << this << endl;

	assign(_expr, nullptr);
}


void String::operand(ostream &ostr) const
{
	if (str_to_label.find(_value) == str_to_label.end()) 
	{
		Label *l = new Label;
		str_to_label[_value] = *l;
	} 

	ostr << str_to_label[_value]; 
}

bool Field::isField(Expression *&str, int &off) const
{
	_expr->type().size();
	str = _expr;
	off = _id->_offset;
	return true;
}

void Field::generate()
{
	int offset = 0;
	_expr->generate();
	cout << "# Field::generate()" << endl;
	Expression *base;
	if (!_expr->isDereference(base))
	{
		findBaseAndOffset(this, base, offset);
		//if (_expr->_register == nullptr)
		//	load(_expr, getreg());
		cout << "\tmov" << suffix(this) << offset << "+" << base << ", " << getreg()->name(_type.size()) << endl;
		assign(this, getreg());
	} else {
		cout << "# field deref" << endl;
		Expression *p;
		findBaseAndOffset(base, p, offset);
		if (p->_register == nullptr) 
			load(p, getreg());
		cout << "\tmov" << suffix(this) << offset << "(" << p << "), " << getreg()->name(_type.size()) << endl;
		assign(this, getreg());
		assign(p, nullptr);
	}
}


/*
void LessThan::test(const Label &label, bool onTrue)
{
	_left->generate();
	_right->generate();

	if (_left->_register == nullptr)
		load(_left, getreg());
	
	cout << "\tcmp" << suffix(_left);
	cout << _right << ", " << _left << endl;
	cout << (onTrue ? "\tjl\t" : "\tjge\t") << label << endl;

	assign(_left, nullptr);
	assign(_right, nullptr);
} */


