CXX		= g++ -std=c++11
CXXFLAGS	= -g -Wall
OBJS		=  Register.o Scope.o Symbol.o Tree.o Type.o \
		  allocator.o checker.o generator.o lexer.o parser.o \
		  writer.o Label.o
PROG		= scc

all:		$(PROG)

$(PROG):	$(OBJS)
		$(CXX) -o $(PROG) $(OBJS)

clean:;		$(RM) $(PROG) core *.o


# dependencies

Register.o:	Label.h Tree.h Scope.h Symbol.h Type.h Register.h 
Scope.o:	Scope.h Symbol.h Type.h
Symbol.o:	Symbol.h Type.h
Tree.o:		Tree.h Scope.h Symbol.h Type.h Register.h Label.h
Type.o:		Type.h
allocator.o:checker.h Scope.h Symbol.h Type.h Tree.h Register.h machine.h tokens.h
checker.o:	lexer.h checker.h Scope.h Symbol.h Type.h Tree.h Register.h tokens.h
generator.o:generator.h Scope.h Symbol.h Type.h Register.h machine.h Tree.h Label.h
lexer.o:	lexer.h tokens.h
parser.o:	lexer.h tokens.h checker.h Scope.h Symbol.h Type.h Tree.h Register.h generator.h
writer.o:	Tree.h Scope.h Symbol.h Type.h Register.h 
Label.o:	Label.h
