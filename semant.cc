

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

#define ERROR(str)         curr_classtable->semant_error(curr_class);           \
                           cerr << str << endl;
#define SEMANT_ERROR(str)  curr_classtable->semant_error(curr_class);           \
                           cerr << str << endl;                                 \
			   type = Object;

extern int semant_debug;
extern char *curr_filename;
static Class__class *curr_class;
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
  Class_ parent;

  for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
    curr_class = it->second;
    if (curr_class->get_parent() == No_class) {
      continue;
    }
    if ((pit = class_table->find(curr_class->get_parent())) == class_table->end()) {
      ERROR("No parent class " << curr_class->get_parent() << " found");
      return EXIT_FAILURE;
    }
    parent = pit->second;
    parent->add_child(curr_class);
  }
  return EXIT_SUCCESS;
}

int ClassTable::compare_methods(Feature method1, Feature method2)
{
  if (method1->get_arg_len() != method2->get_arg_len() ||
      method1->get_return_type() != method2->get_return_type()) {
    return EXIT_FAILURE;
  }
  Formals formals = method1->get_formals();
  for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
    Formal formal1 = method1->get_formals()->nth(i);
    Formal formal2 = method2->get_formals()->nth(i);
    if (formal1->get_type_decl() != formal2->get_type_decl()) {
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;
}

int ClassTable::check_methods()
{
  std::map<Symbol, Feature> *method_table;
  Feature child_method, parent_method;

  for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
    curr_class = it->second;
    if (curr_class->get_parent() == No_class) {
      continue;
    }
    method_table = curr_class->get_method_table();
    for (std::map<Symbol, Feature>::iterator itt = method_table->begin(); itt != method_table->end(); itt++) {
      child_method = itt->second;
      parent_method = lookup_method(curr_class->get_parent(), child_method->get_name());
      if (parent_method == NULL) {
	continue;
      }
      if (compare_methods(child_method, parent_method)) {
	ERROR("Method " << child_method->get_name() << " redefined with different parameters and/or return type");
	return EXIT_FAILURE;
      }
    }
  }
  return EXIT_SUCCESS;
}

int method_class::check_attrs()
{
  return EXIT_SUCCESS;
}

int attr_class::check_attrs()
{
  if (curr_class->get_parent() != No_class) {
    if (curr_classtable->lookup_attr(curr_class->get_parent(), name)) {
      ERROR("Attribute " << name << "redefined in class " << curr_class->get_name());
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;
}

int class__class::check_attrs()
{
  curr_class = this;
  for (int i = features->first(); features->more(i); i = features->next(i)) {
    if (features->nth(i)->check_attrs()) {
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;
}

int ClassTable::check_attrs()
{
  SymbolTable<Symbol, Symbol> *object_table;
  Class_ class_;

  for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
    class_ = it->second;
    if (class_->check_attrs()) {
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;
}

int ClassTable::check_parents()
{
  for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
    curr_class = it->second;
    if (curr_class->get_parent() == Int || curr_class->get_parent() == Str || curr_class->get_parent() == Bool) {
      ERROR("Class " << curr_class->get_name() << " has illegal parent Class of Int, String or Bool");
      return EXIT_FAILURE;
    }
  }
  return EXIT_SUCCESS;
}

int ClassTable::check_main()
{
  std::map<Symbol, Class_>::iterator it = class_table->find(Main);
  if (it == class_table->end()) {
    semant_error();
    cerr << "Class Main is not defined." << endl;
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}

int ClassTable::check_cycle()
{
  std::map<Symbol, Class_>::iterator it = class_table->find(Object);
  Class_ object_class;

  assert(it != class_table->end());
  object_class = it->second;
  if (object_class->check_cycle()) {
    return EXIT_FAILURE;
  }

  /* Check for classes left outside Object-rooted inheritance tree i.e. C -> B and B -> C */
  for (std::map<Symbol, Class_>::iterator it = class_table->begin(); it != class_table->end(); it++) {
    curr_class = it->second;
    if (curr_class->get_marked() == false) {
      ERROR("Class inheritance cycle has been detected for class " << curr_class->get_name());
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
  if (name == SELF_TYPE) {
    semant_error(class_);
    cerr << "Class cannot have name SELF_TYPE" << endl;
    return EXIT_FAILURE;
  }
  class_table->insert(std::pair<Symbol, Class_>(name, class_));
  return EXIT_SUCCESS;
}

Class_ ClassTable::lookup_class(Symbol class_name)
{
  if (class_name == SELF_TYPE) {
    class_name = curr_class->get_name();
  }
  std::map<Symbol, Class_>::iterator it = class_table->find(class_name);
  if (it == class_table->end()) {
    ERROR("Type " << class_name << " does not exist");
    it = class_table->find(Object);
    assert(it != class_table->end());
  }
  return it->second;
}

Symbol ClassTable::lookup_attr(Symbol class_name, Symbol var_name)
{
  Class_ class_ = lookup_class(class_name);
  return class_->get_attr(var_name);
}

Feature ClassTable::lookup_method(Symbol class_name, Symbol method_name)
{
  if (class_name == No_type) {
    class_name = curr_class->get_name();
  }
  Class_ class_ = lookup_class(class_name);
  return class_->get_method(method_name);
}

bool ClassTable::leq(Symbol class1, Symbol class2)
{
  if (class1 == No_type || class2 == No_type) {
    return true;
  }

  if (class1 != SELF_TYPE && class2 == SELF_TYPE) {
    return false;
  }
  if (class1 == SELF_TYPE) {
    class1 = curr_class->get_name();
  }
  if (class2 == SELF_TYPE) {
    class2 = curr_class->get_name();
  }

  if (class1 == class2) {
    return true;
  }

  Class_ class1_ = lookup_class(class1);
  Class_ class2_ = lookup_class(class2);

  if (class1_->get_parent() != No_class) {
    return leq(class1_->get_parent(), class2);
  }
  return false;
}

Symbol ClassTable::lub(Symbol class1, Symbol class2)
{
  if (class1 == SELF_TYPE) {
    class1 = curr_class->get_name();
  }
  if (class2 == SELF_TYPE) {
    class2 = curr_class->get_name();
  }

  if (leq(class1, class2)) {
    return class2;
  } else if (leq(class2, class1)) {
    return class1;
  }

  Class_ class1_ = lookup_class(class1);
  if (class1_->get_parent() != No_class) {
    return lub(class1_->get_parent(), class2);
  }
  return Object;
}

void ClassTable::check_and_add_to_object_table(Symbol name, Symbol type_decl)
{
  lookup_class(type_decl);
  add_to_object_table(name, type_decl);
}

int ClassTable::add_to_object_table(Symbol name, Symbol type_decl)
{
  SymbolTable<Symbol, Symbol> *object_table = curr_class->get_object_table();

  if (object_table->probe(name)) {
    ERROR("Duplicate variable " << name << " exists in same scope");
    return EXIT_FAILURE;
  }
  if (name == self) {
    ERROR("Variable cannot have name self");
    return EXIT_FAILURE;
  }
  object_table->addid(name, new Symbol(type_decl));
  return EXIT_SUCCESS;
}

Symbol class__class::get_attr(Symbol var)
{
  Symbol *type_decl = object_table->lookup(var);
  if (type_decl == NULL) {
    if (get_parent() != No_class) {
      Class_ parent_class = curr_classtable->lookup_class(get_parent());
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
      Class_ parent_class = curr_classtable->lookup_class(get_parent());
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
  return curr_classtable->add_to_object_table(name, type_decl);
}

int method_class::get_environment()
{
  std::map<Symbol, Feature> *method_table = curr_class->get_method_table();
  if (method_table->find(name) != method_table->end()) {
    ERROR("Class " << curr_class << " has duplicate method " << name);
    return EXIT_FAILURE;
  }
  if (name == self) {
    ERROR("Method cannot have name self");
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


void class__class::semant()
{
  curr_class = this;
  for(int i = features->first(); features->more(i); i = features->next(i)) {
    features->nth(i)->semant();
  }
}

void method_class::semant()
{
  SymbolTable<Symbol, Symbol> *object_table = curr_class->get_object_table();
  object_table->enterscope();

  for(int i = formals->first(); formals->more(i); i = formals->next(i)) {
    formals->nth(i)->semant();
  }

  expr->semant();
  if (curr_classtable->leq(expr->get_type(), return_type) == false) {
    curr_classtable->semant_error(curr_class);
    cerr << "Method body has type " << expr->get_type() << " but function has type " << return_type << endl;
  }
  object_table->exitscope();
}

void formal_class::semant()
{
  if (type_decl == SELF_TYPE) {
    curr_classtable->semant_error(curr_class);
    cerr << "Formal cannot have type SELF_TYPE" << endl;
  }
  curr_classtable->check_and_add_to_object_table(name, type_decl);
}

void attr_class::semant()
{
  init->semant();
  if (curr_classtable->leq(init->get_type(), type_decl) == false) {
    curr_classtable->semant_error(curr_class);
    cerr << "Initialization has type " << init->get_type() << " but attribute has type " << type_decl << endl;
  }
}

void assign_class::semant()
{
  Symbol type_decl = curr_classtable->lookup_attr(curr_class->get_name(), name);
  expr->semant();
  if (!type_decl) {
    SEMANT_ERROR("Variable " << name << " does not exist in this scope");
  } else {
    if (curr_classtable->leq(expr->get_type(), type_decl)) {
      type = expr->get_type();
    } else {
      SEMANT_ERROR("Expression type " << expr->get_type() << " does not inherit from " << type_decl);
    }
  }
}

int method_class::get_arg_len()
{
  return formals->len();
}

Symbol method_class::get_arg_type(int i)
{
  assert(i < get_arg_len());
  return formals->nth(i)->get_type_decl();
}

Symbol dispatch_common(Expression expr, Symbol type_name, Symbol name, Expressions actual, Feature method)
{
  if (method == NULL) {
    ERROR("No method " << name << " in class " << type_name << " found");
    return Object;
  } else if (method->get_arg_len() != actual->len()) {
    ERROR("Method " << method->get_name() << " only has " << method->get_arg_len() << " arguments");
    return Object;
  }
  for(int i = actual->first(); actual->more(i); i = actual->next(i)) {
    actual->nth(i)->semant();
    if (method == NULL || i >= method->get_arg_len()) {
      /* Number of arguments is different, error should've been caught above */
      continue;
    }
    if (curr_classtable->leq(actual->nth(i)->get_type(), method->get_arg_type(i)) == false) {
      ERROR("Method " << method->get_name() << " argument " << i + 1<< " has type " << method->get_arg_type(i));
      return Object;
    }
  }
  Symbol type = method->get_return_type();
  if (type == SELF_TYPE) {
    type = expr->get_type();
  }
  curr_classtable->lookup_class(type);
  return type;
}

void static_dispatch_class::semant()
{
  expr->semant();
  if (curr_classtable->leq(expr->get_type(), type_name)) {
    Feature method = curr_classtable->lookup_method(type_name, name);
    type = dispatch_common(expr, type_name, name, actual, method);
  } else {
    SEMANT_ERROR("Expression of type " << expr->get_type() << " does not inherit from static dispatch type name " << type_name);
  }
}

void dispatch_class::semant()
{
  expr->semant();
  Feature method = curr_classtable->lookup_method(expr->get_type(), name);
  type = dispatch_common(expr, expr->get_type(), name, actual, method);
}

int typcase_class::check_dups()
{
  for(int i = cases->first(); cases->more(i); i = cases->next(i)) {
    for(int j = cases->next(i); cases->more(j); j = cases->next(j)) {
      if (cases->nth(i)->get_type_decl() == cases->nth(j)->get_type_decl()) {
	ERROR("Branches in case statement have same type " << cases->nth(i)->get_type_decl());
	return EXIT_FAILURE;
      }
    }
  }
  return EXIT_SUCCESS;
}

void typcase_class::semant()
{
  expr->semant();

  for(int i = cases->first(); cases->more(i); i = cases->next(i)) {
    cases->nth(i)->semant();
    if (i == cases->first()) {
      type = cases->nth(i)->get_expr()->get_type();
    } else {
      type = curr_classtable->lub(type, cases->nth(i)->get_expr()->get_type());
    }
  }
  if (check_dups()) {
    type = Object;
  }
}


void cond_class::semant()
{
  pred->semant();
  then_exp->semant();
  else_exp->semant();
  if (pred->get_type() == Bool) {
    type = curr_classtable->lub(then_exp->get_type(), else_exp->get_type());
  } else {
    SEMANT_ERROR("Predicate of conditional is not of type Bool");
  }
}

void loop_class::semant()
{
  pred->semant();
  body->semant();
  if (pred->get_type() != Bool) {
    SEMANT_ERROR("Predicate does not have type Bool");
  }
  type = Object;
}

void branch_class::semant()
{
  SymbolTable<Symbol, Symbol> *object_table = curr_class->get_object_table();
  object_table->enterscope();
  curr_classtable->check_and_add_to_object_table(name, type_decl);
  expr->semant();
  object_table->exitscope();
}

void block_class::semant()
{
  for(int i = body->first(); body->more(i); i = body->next(i)) {
    body->nth(i)->semant();
    type = body->nth(i)->get_type();
  }
}

void let_class::semant()
{
  SymbolTable<Symbol, Symbol> *object_table = curr_class->get_object_table();

  init->semant();
  object_table->enterscope();
  curr_classtable->check_and_add_to_object_table(identifier, type_decl);
  body->semant();
  if (curr_classtable->leq(init->get_type(), type_decl)) {
    type = body->get_type();
  } else {
    SEMANT_ERROR("Expression with type " << init->get_type() << " does not inherit from " << type_decl);
  }
  object_table->exitscope();
}

void plus_class::semant()
{
  e1->semant();
  e2->semant();
  if (e1->get_type() != Int || e2->get_type() != Int) {
    SEMANT_ERROR("One of the expressions for multiply does not evaluate to Integer");
  } else {
    type = Int;
  }
}

void sub_class::semant()
{
  e1->semant();
  e2->semant();
  if (e1->get_type() !=Int || e2->get_type() != Int) {
    SEMANT_ERROR("One of the expressions for multiply does not evaluate to Integer");
  } else {
    type = Int;
  }

}

void eq_class::semant()
{
    e1->semant();
    e2->semant();
    if ((e1->get_type() == Int || e1->get_type() == Bool || e1->get_type() == Str ||
	e2->get_type() ==Int || e2->get_type() == Bool || e2->get_type() == Str)
	&& e1->get_type() != e2->get_type()) {
      SEMANT_ERROR("Expressions of types " << e1->get_type() << " and " << e2->get_type() << " cannot be compared");
    } else {
      type = Bool;
    }
}

void mul_class::semant()
{
  e1->semant();
  e2->semant();
  if (e1->get_type() !=Int || e2->get_type() != Int) {
    SEMANT_ERROR("One of the expressions for multiply does not evaluate to Integer");
  } else {
    type = Int;
  }
}

void divide_class::semant()
{
  e1->semant();
  e2->semant();
  if (e1->get_type() !=Int || e2->get_type() != Int) {
    SEMANT_ERROR("One of the expressions for divide does not evaluate to Integer");
  } else {
    type = Int;
  }

}

void neg_class::semant()
{
  e1->semant();
  if (e1->get_type() == Int) {
    type = Int;
  } else {
    SEMANT_ERROR("Expression does not have Integer type");
  }
}

void lt_class::semant()
{
  e1->semant();
  e2->semant();
  if (e1->get_type() !=Int || e2->get_type() != Int) {
    SEMANT_ERROR("One of the expressions for lt does not evaluate to Integer");
  } else {
    type = Bool;
  }
}


void leq_class::semant()
{
  e1->semant();
  e2->semant();
  if (e1->get_type() != Int || e2->get_type() != Int) {
    SEMANT_ERROR("One of the expressions for leq does not evaluate to Integer");
  } else {
    type = Bool;
  }
}

void comp_class::semant()
{
  e1->semant();
  if (e1->get_type() == Bool) {
    type = Bool;
  } else {
    SEMANT_ERROR("Expression does not have type Bool");
  }
}

void int_const_class::semant()
{
  type = Int;
}

void bool_const_class::semant()
{
  type = Bool;
}

void string_const_class::semant()
{
  type = Str;
}

void new__class::semant()
{
  curr_classtable->lookup_class(type_name);
  type = type_name;
}

void isvoid_class::semant()
{
  e1->semant();
  type = Bool;
}

void no_expr_class::semant()
{
  type = No_type;
}

void object_class::semant()
{
  if (name == self) {
    type = SELF_TYPE;
  } else {
    Symbol type_decl = curr_classtable->lookup_attr(curr_class->get_name(), name);
    if (type_decl) {
      type = type_decl;
    } else {
      SEMANT_ERROR("Object " << name << " not declared in scope");
    }
  }
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
	curr_classtable->check_cycle() == EXIT_FAILURE ||
	curr_classtable->check_main() == EXIT_FAILURE ||
	curr_classtable->check_methods() == EXIT_FAILURE ||
	curr_classtable->check_attrs() == EXIT_FAILURE ||
	curr_classtable->check_parents() == EXIT_FAILURE) {
      goto error;
    }

    for(int i = classes->first(); classes->more(i); i = classes->next(i)) {
      classes->nth(i)->semant();
    }
 
error:
    if (curr_classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(EXIT_FAILURE);
    }
}
