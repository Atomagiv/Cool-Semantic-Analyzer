

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;
extern char *curr_filename;
static class__class *curr_class;
static ClassTable *curr_classtable;
//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

ClassTable::ClassTable() : semant_errors(0) , error_stream(cerr)
{
  class_table = new std::map<Symbol, Class_>;
}

int ClassTable::install_classes(Classes classes)
{
  install_basic_classes();

  for(int i = classes->first(); classes->more(i); i = classes->next(i)) {
    Class_ class_ = classes->nth(i);
    if (install_class(class_->get_name(), class_)) {
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;

}

int ClassTable::get_environment()
{
  Class_ class_;

  for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
    class_ = it->second;
    if (class_->get_environment()) {
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;
}

int ClassTable::generate_tree()
{
  std::map<Symbol, Class_>::iterator pit;
  Class_ class_, parent;

  for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
    class_ = it->second;
    if (class_->get_parent() == No_class) {
      continue;
    }
    if ((pit = class_table->find(class_->get_parent())) == class_table->end()) {
      semant_error(class_);
      cerr << "No parent class " << class_->get_parent() << " found" << endl;
      return EXIT_FAILURE;
    }
    parent = pit->second;
    parent->add_child(class_);
  }
  return EXIT_SUCCESS;
}

int ClassTable::check_cycle()
{
  std::map<Symbol, Class_>::iterator it = class_table->find(Object);
  Class_ object_class, class_;

  assert(it != class_table->end());
  object_class = it->second;
  if (object_class->check_cycle()) {
    return EXIT_FAILURE;
  }

  /* Check for classes left outside Object-rooted inheritance tree i.e. C -> B and B -> C */
  for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
    class_ = it->second;
    if (class_->get_marked() == false) {
      semant_error(class_);
      cerr << "Class inheritance cycle has been detected for class " << class_->get_name() << endl;
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;
}

int ClassTable::install_class(Symbol name, Class_ class_)
{
  if (class_table->find(name) != class_table->end()) {
    semant_error(class_);
    cerr << "Class " << name << " already exists" << endl;
    return EXIT_FAILURE;
  }
  class_table->insert(std::pair<Symbol, Class_>(name, class_));
  return EXIT_SUCCESS;
}

Class_ ClassTable::lookup(Symbol name)
{
  return class_table->find(name)->second;
}

Class_ ClassTable::lookup_parent(Class_ class_)
{
  Symbol parent = class_->get_parent();
  return class_table->find(parent)->second;
}

Feature ClassTable::lookup_method(Symbol class_name, Symbol method_name)
{
  Class_ class_ = lookup(class_name);
  assert(class_ != NULL);
  return class_->get_method(method_name);
}

Symbol class__class::get_attr(Symbol var)
{
  Symbol *type_decl = object_table->lookup(var);
  if (type_decl == NULL) {
    if (get_parent() != No_class) {
      Class_ parent_class = curr_classtable->lookup_parent(this);
      return parent_class->get_attr(var);
    } else {
      return NULL;
    }
  }
  return *type_decl;
}

Feature class__class::get_method(Symbol method)
{
  std::map<Symbol, Feature>::iterator it = method_table->find(method);
  if (it == method_table->end()) {
    if (get_parent() != No_class) {
      Class_ parent_class = curr_classtable->lookup_parent(this);
      return parent_class->get_method(method);
    } else {
      return NULL;
    }
  }
  return it->second;
}

int class__class::check_cycle()
{
  Class_ class_;

  if (marked) {
    /* This node has already been marked, meaning there's a cycle */
    curr_classtable->semant_error(this);
    cerr << "Class inheritance cycle has been detected for class " << name << endl;
    return EXIT_FAILURE;
  }
  marked = true;

  for (std::list<Class_>::iterator it = children->begin(); it != children->end(); it++) {
    class_ = *it;
    if (class_->check_cycle()) {
      return EXIT_FAILURE;
    };
  }
  return EXIT_SUCCESS;
}

void class__class::add_child(Class_ class_)
{
  children->push_back(class_);
}

int class__class::get_environment()
{
  curr_class = this;
  for(int i = features->first(); features->more(i); i = features->next(i)) {
    if (features->nth(i)->get_environment()) {
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;
}

int attr_class::get_environment()
{
  SymbolTable<Symbol, Symbol> *object_table = curr_class->get_object_table();
  if (object_table->probe(name)) {
    curr_classtable->semant_error(curr_class);
    cerr << "Class " << curr_class << " has duplicate attribute " << name << endl;
    return EXIT_FAILURE;
  }
  object_table->addid(name, new Symbol(type_decl));
  return EXIT_SUCCESS;
}

int method_class::get_environment()
{
  std::map<Symbol, Feature> *method_table = curr_class->get_method_table();
  if (method_table->find(name) != method_table->end()) {
    curr_classtable->semant_error(curr_class);
    cerr << "Class " << curr_class << " has duplicate method " << name << endl;
    return EXIT_FAILURE;
  }
  method_table->insert(std::pair<Symbol, Feature>(name, this));
  return EXIT_SUCCESS;
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);

    install_class(Object, Object_class);
    install_class(IO, IO_class);
    install_class(Bool, Bool_class);
    install_class(Int, Int_class);
    install_class(Str, Str_class);
}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 



/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    curr_classtable = new ClassTable();

    if (curr_classtable->install_classes(classes) == EXIT_FAILURE ||
	curr_classtable->get_environment() == EXIT_FAILURE ||
	curr_classtable->generate_tree() == EXIT_FAILURE ||
	curr_classtable->check_cycle() == EXIT_FAILURE) {
      goto error;
    }

    /* some semantic analysis code may go here */
    exit(EXIT_SUCCESS);

error:
    if (curr_classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(EXIT_FAILURE);
    }
}
