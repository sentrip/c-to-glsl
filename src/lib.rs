#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]


use lang_c::ast::*;
use lang_c::visit::*;
use lang_c::span::{Span, Node};
use lang_c::driver::{Config, parse, parse_preprocessed}; 
use std::collections::HashMap;
use std::ops::Index;

//region public api

fn print_ast<'ast>(n: &'ast TranslationUnit) -> String {
    let mut w = String::new();
    let mut p = lang_c::print::Printer::new(&mut w);
    p.visit_translation_unit(&n);
    return w;
}


fn recompile<'ast>(file_name: &str, src: String, n: &'ast TranslationUnit) -> String {    
    Validator{}.visit_translation_unit(n);    
    
    let mut types = Types::new(false);
    TypeParser{types: &mut types}.visit_translation_unit(n);
    
    Parser{}.visit_translation_unit(n);
    
    src
}


pub fn c_to_glsl(source: &str) -> String {
    let mut config = Config::default();
    config.cpp_options.push("-Doffsetof=__builtin_offsetof".to_string());
    
    let result = parse(&config, source.to_owned());
    if let Ok(r) = result {
        println!("=============== AST ================\n\n{}", print_ast(&r.unit));
        
        let rc = recompile("memory", r.source, &r.unit);

        // println!("\n\n============= PROCESSED =============\n\n{}", rc);

        rc
    } else {
        println!("{:#?}", result);
        String::new()
    }
}


#[no_mangle]
pub extern "C" fn c_to_glsl_c() {

}

//endregion

//region types

type TypeH = usize;


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrimitiveKind {
    Bool,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    F32,
    U64,
    I64,
    F64,
}


#[derive(Debug, Clone, Copy)]
enum TypeKind {
    Primitive(PrimitiveKind),
    Struct
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Qualifier {
    Const,
    PtrMut,
    PtrConst
}


#[derive(Debug, Clone)]
struct Field {
    name: String,
    offset: usize,
    t: TypeH,
    quals: Qualifiers,
}


#[derive(Debug, Clone)]
struct Type {
    kind: TypeKind,
    name: String,
    size: usize,
    align: usize,
    fields: Vec<Field>,
}


#[derive(Debug, Clone)]
struct Qualifiers {
    qualifier_count: usize,
    array_count: usize,
    qualifiers: [Qualifier; 6],
    array_sizes: [usize; 4]
}


struct Types {
    ptr_size: usize,
    values: Vec<Type>,
}


struct TypeParser<'a> {
    types: &'a mut Types
}


struct Parser {

}


struct Validator {

}


impl Type {
    fn primitive(k: PrimitiveKind) -> Type {
        let s = k.size();
        Type{
            kind: TypeKind::Primitive(k),
            name: k.name().to_owned(),
            size: s,
            align: if s <= 4 { 4 } else { 8 },
            fields: vec![],
        }
    }

    fn struct_type(types: &Types, name: &String, fields: Vec<Field>) -> Type {
        let size  = fields.iter().map(|x: &Field| types[x.t].size).reduce(|prev, v| prev + v).unwrap_or(0);
        let align = std::cmp::max(size, fields.iter().map(|x: &Field| types[x.t].size).reduce(|prev, v| std::cmp::max(prev, v)).unwrap_or(0));
        Type{
            kind: TypeKind::Struct,
            name: name.clone(),
            size: size,
            align: align,
            fields: fields
        }
    }
}

impl Types {
    fn new(is_64_bit: bool) -> Types {
        Types{ptr_size: if is_64_bit { 8 } else { 4 }, values: vec![]}
    }

    fn add(&mut self, t: Type) {
        if let TypeKind::Struct = t.kind { println!("{:#?}", t); }
        self.values.push(t)
    }

    fn find(&self, name: &str) -> usize {
        for (i, v) in self.values.iter().enumerate() {
            if &v.name == name {
                return i;
            }
        }
        usize::MAX
    }
    
    fn find_primitive(&self, k: PrimitiveKind) -> usize {
        for (i, v) in self.values.iter().enumerate() {
            match &v.kind {
                TypeKind::Primitive(p) => if p == &k { return i; },
                _ => {}
            }
        }
        usize::MAX
    }
}

impl Index<usize> for Types {
    type Output = Type;
    
    fn index(&self, index: usize) -> &Self::Output {
        &self.values[index]
    }
}


macro_rules! cast {
    ($target: expr, $pat: path) => {
        {
            if let $pat(a) = $target { // #1
                a
            } else {
                panic!(
                    "mismatch variant when cast to {}", 
                    stringify!($pat)); // #2
            }
        }
    };
}

//endregion

//region main parser

impl<'a, 'ast> Visit<'ast> for TypeParser<'a> {
    fn visit_translation_unit(&mut self, translation_unit: &'ast TranslationUnit) {
        self.types.add(Type::primitive(PrimitiveKind::Bool));
        self.types.add(Type::primitive(PrimitiveKind::I8));
        self.types.add(Type::primitive(PrimitiveKind::U8));
        self.types.add(Type::primitive(PrimitiveKind::I16));
        self.types.add(Type::primitive(PrimitiveKind::U16));
        self.types.add(Type::primitive(PrimitiveKind::I32));
        self.types.add(Type::primitive(PrimitiveKind::U32));
        self.types.add(Type::primitive(PrimitiveKind::I64));
        self.types.add(Type::primitive(PrimitiveKind::U64));
        self.types.add(Type::primitive(PrimitiveKind::F32));
        self.types.add(Type::primitive(PrimitiveKind::F64));
        visit_translation_unit(self, translation_unit);
    }

    fn visit_external_declaration(&mut self, n: &'ast ExternalDeclaration, span: &'ast Span) {
        match n {
            ExternalDeclaration::Declaration(d) => {
                if lang_c_declaration_is_struct_definition(&d.node) {
                    let last_spec = d.node.specifiers.last().unwrap();
                    let type_spec = cast!(&last_spec.node, DeclarationSpecifier::TypeSpecifier);
                    let struct_type = cast!(&type_spec.node, TypeSpecifier::Struct);

                    let name = if let Some(init_decl) = &d.node.declarators.first() {
                        lang_c_declarator_name(&init_decl.node.declarator.node)
                    } else {    
                        &struct_type.node.identifier.as_ref().unwrap().node.name
                    };
                    
                    let fields = if let Some(declarations) = &struct_type.node.declarations {
                        Field::from_declarations(self.types, declarations)
                    } else {
                        Vec::new()
                    };
                    
                    self.types.add(Type::struct_type(self.types, name, fields));
                }
            }
            _ => {

            }
        }
    }
}


impl<'ast> Visit<'ast> for Parser {
    fn visit_external_declaration(&mut self, n: &'ast ExternalDeclaration, span: &'ast Span) {
        match n {
            ExternalDeclaration::Declaration(d) => {
                if lang_c_declaration_has_storage_class_specifier(&d.node, StorageClassSpecifier::Static) {
                    if lang_c_declaration_is_global_array(&d.node) {
                        println!("Global Array: {:?}", span);
                    }
                }
            }

            ExternalDeclaration::FunctionDefinition(f) => {
                let derived = f.node.declarator.node.derived.last().unwrap();
                let name = lang_c_declarator_name(&f.node.declarator.node);
                
                let mut uses_pointers = lang_c_declarator_is_pointer(&f.node.declarator.node);
                
                // parameters
                if let DerivedDeclarator::Function(func_def) = &derived.node {
                    for param in &func_def.node.parameters {
                        let decl = param.node.declarator.as_ref().unwrap();
                        if lang_c_declarator_is_pointer(&decl.node) {
                            uses_pointers = true;
                            break;
                        }
                    }
                }
                
                if uses_pointers {
                    println!("Function {} uses ptrs: {:?}", name, span);
                } else {
                    println!("Function {} is regular: {:?}", name, span);
                }
                
                self.visit_function_definition(&f.node, &f.span);
            }
            _ => {

            }
        }
    }
}


impl<'ast> Visit<'ast> for Validator {

    fn visit_external_declaration(&mut self, n: &'ast ExternalDeclaration, span: &'ast Span) {
        match n {
            ExternalDeclaration::Declaration(d) => {
                if lang_c_declaration_has_storage_class_specifier(&d.node, StorageClassSpecifier::Static) {
                    if !lang_c_declaration_is_global_array(&d.node) {
                        // Error - the only allowed way to use static globals is by defining global arrays
                        println!("ERROR - invalid global array: {:?}", span);
                    }
                }
            }
            _ => {

            }
        }
    }
}

//endregion

//region object parsing


impl Qualifiers {
    fn empty(&self) -> bool {
        self.qualifier_count == 0 && self.array_count == 0
    }

    fn is_const(&self) -> bool {
        self.qualifier_count > 0 && self.qualifiers[self.qualifier_count-1] != Qualifier::PtrMut
    }

    fn is_ptr(&self) -> bool {
        self.qualifier_count > 0 && self.qualifiers[self.qualifier_count-1] != Qualifier::Const
    }

    fn is_array(&self) -> bool {
        self.array_count > 0
    }

    fn access(&self) -> Qualifiers {
        let new_qc = if self.is_array() { self.qualifier_count } else { self.qualifier_count - 1 };
        let new_ac = if self.is_array() { self.array_count - 1 } else { self.array_count };
        Qualifiers{qualifier_count: new_qc, array_count: new_ac, qualifiers: self.qualifiers, array_sizes: self.array_sizes}
    }

    fn push_array_size(&mut self, size: usize) {
        self.array_sizes[self.array_count] = size;
        self.array_count += 1;
    }

    fn push_qualifier(&mut self, q: Qualifier) {
        self.qualifiers[self.qualifier_count] = q;
        self.qualifier_count += 1;
    }

    fn from_declarator(declarator: &Declarator, specs: &Vec<Node<SpecifierQualifier>>) -> Qualifiers {
        let mut quals = Qualifiers{qualifier_count: 0, array_count: 0, qualifiers: [Qualifier::Const; 6], array_sizes: [0; 4]};
        
        let mut is_const = false;
        for s in specs {
            match &s.node {
                SpecifierQualifier::TypeQualifier(q) => {
                    match &q.node {
                        TypeQualifier::Const => { is_const = true; break; },
                        _ => {}
                    }
                },
                _ => {}
            }
        }
        if is_const {
            quals.push_qualifier(Qualifier::Const);
        }

        for d in &declarator.derived {
            match &d.node {
                DerivedDeclarator::Array(arr) => {
                    quals.push_array_size(match &arr.node.size {
                        ArraySize::Unknown |
                        ArraySize::VariableUnknown |  
                        ArraySize::StaticExpression(_)      => usize::MAX,
                        ArraySize::VariableExpression(e)    => { 
                            if let Expression::Constant(c) = &e.node {
                                if let Constant::Integer(i) = &c.node {
                                    str::parse::<usize>(&i.number).unwrap()
                                } else {
                                    usize::MAX
                                }
                            } else {
                                usize::MAX
                            }
                        },
                    });
                }
                DerivedDeclarator::Pointer(p_qual) => { 
                    let mut is_const = false;
                    for q in p_qual {
                        if let TypeQualifier::Const = cast!(&q.node, PointerQualifier::TypeQualifier).node {
                            is_const = true;
                            break;
                        }
                    }
                    quals.push_qualifier(if is_const { Qualifier::PtrConst } else { Qualifier::PtrMut });
                }
                _ => {}
            }
        }

        // Const, ... , PtrMut -> PtrConst, ...
        if quals.qualifier_count >= 2 && quals.qualifiers[0] == Qualifier::Const && quals.qualifiers[quals.qualifier_count-1] == Qualifier::PtrMut {
            for i in 1..quals.qualifier_count {
                quals.qualifiers[i - 1] = quals.qualifiers[i];
            }
            quals.qualifiers[quals.qualifier_count-2] = Qualifier::PtrConst;
            quals.qualifiers[quals.qualifier_count-1] = Qualifier::Const;
            quals.qualifier_count -= 1;
        }

        quals
    }
}


impl Field {
    fn from_declarations(types: &Types, declarations: &Vec<Node<StructDeclaration>>) -> Vec<Field> {
        let mut offset = 0usize;
        let mut fields = Vec::new();
        for decl in declarations {
            if let StructDeclaration::Field(field) = &decl.node {
                let mut t = usize::MAX;
                
                if let Some(prim) = PrimitiveKind::from_specifier_qualifiers(&field.node.specifiers) {
                    t = types.find_primitive(prim);
                } else if let Some(name) = lang_c_type_name_from_specifier_qualifiers(&field.node.specifiers) {
                    t = types.find(&name);
                }

                if t == usize::MAX {
                    panic!("Undefined type");
                }

                for declarator in &field.node.declarators {
                    if let Some(d) = &declarator.node.declarator {
                        let quals = Qualifiers::from_declarator(&d.node, &field.node.specifiers);
                        fields.push(Field{name: lang_c_declarator_name(&d.node).clone(), offset: offset, t: t, quals: quals});
                        let is_ptr = lang_c_declarator_is_pointer(&d.node);
                        let size = std::cmp::max(types[t].size, types[t].align); 
                        offset += if is_ptr { types.ptr_size } else { size };
                    }
                }
            }
        }
        fields
    }
}

//endregion

//region primitive parsing

struct PrimitiveCalculator {
    is_bool: bool,
    is_float: bool,
    is_unsigned: bool,
    is_invalid: bool,
    size: usize,
}

impl PrimitiveCalculator {
    fn new() -> PrimitiveCalculator {
        PrimitiveCalculator{is_bool: false, is_float: false, is_unsigned: false, is_invalid: false, size: usize::MAX}
    }

    fn specifier(&mut self, t: &TypeSpecifier) {
        if self.is_invalid || self.is_bool { return; }
        match t {
            TypeSpecifier::Signed       => self.is_unsigned = false,
            TypeSpecifier::Unsigned     => self.is_unsigned = true,
            TypeSpecifier::Bool         => self.is_bool = true,
            TypeSpecifier::Char         => self.size = 1,
            TypeSpecifier::Short        => self.size = 2,
            TypeSpecifier::Int          => self.size = 4,
            TypeSpecifier::Float        => { self.size = 4; self.is_float = true; },
            TypeSpecifier::Double       => { self.size = 8; self.is_float = true; },
            TypeSpecifier::Long         => self.size = if self.size == usize::MAX { 4 } else { 8 },
            _                           => self.is_invalid = true,
        }
    }

    fn get_primitive(&self) -> Option<PrimitiveKind> {
        if self.is_invalid {
            return None;
        }
        Some(if self.is_bool {
            PrimitiveKind::Bool
        }
        else if self.is_float {
            if self.size == 4 { 
                PrimitiveKind::F32 
            } else { 
                PrimitiveKind::F64 
            }
        } 
        else {
            if self.is_unsigned {
                if self.size == 8 { 
                    PrimitiveKind::U64
                } else if self.size == 4 { 
                    PrimitiveKind::U32
                } else if self.size == 2 { 
                    PrimitiveKind::U16
                } else { 
                    PrimitiveKind::U8
                }
            } else {
                if self.size == 8 { 
                    PrimitiveKind::I64
                } else if self.size == 4 { 
                    PrimitiveKind::I32
                } else if self.size == 2 { 
                    PrimitiveKind::I16
                } else { 
                    PrimitiveKind::I8
                }
            }
        })
    }
}

impl PrimitiveKind {
    fn size(&self) -> usize {
        match self {
            PrimitiveKind::U8  |
            PrimitiveKind::I8  |
            PrimitiveKind::Bool => 1,
            PrimitiveKind::I16  |
            PrimitiveKind::U16  => 2,
            PrimitiveKind::I32  |
            PrimitiveKind::U32  |
            PrimitiveKind::F32  => 4,
            PrimitiveKind::I64  |
            PrimitiveKind::U64  |
            PrimitiveKind::F64  => 8,
        }
    }

    fn name(&self) -> &'static str {
        match self {
            PrimitiveKind::Bool => "bool",
            PrimitiveKind::I8   => "int8_t",
            PrimitiveKind::U8   => "uint8_t",
            PrimitiveKind::I16  => "int16_t",
            PrimitiveKind::U16  => "uint16_t",
            PrimitiveKind::I64  => "int64_t",
            PrimitiveKind::U64  => "uint64_t",
            PrimitiveKind::I32  => "int",
            PrimitiveKind::U32  => "uint",
            PrimitiveKind::F32  => "float",
            PrimitiveKind::F64  => "double",
        }
    }

    fn from_specifier_qualifiers(specs: &Vec<Node<SpecifierQualifier>>) -> Option<PrimitiveKind> {
        let mut calc = PrimitiveCalculator::new();
        for s in specs.iter().rev() {
            match &s.node {
                SpecifierQualifier::TypeSpecifier(s) => calc.specifier(&s.node),
                _ => {}
            }
        }
        calc.get_primitive()
    }

    fn from_declaration_specifiers(specs: &Vec<Node<DeclarationSpecifier>>) -> Option<PrimitiveKind> {
        let mut calc = PrimitiveCalculator::new();
        for s in specs.iter().rev() {
            match &s.node {
                DeclarationSpecifier::TypeSpecifier(s) => calc.specifier(&s.node),
                _ => {}
            }
        }
        calc.get_primitive()
    }
}

//endregion

//region helper functions

fn lang_c_declaration_has_storage_class_specifier(n: &Declaration, expected: StorageClassSpecifier) -> bool {
    for spec in &n.specifiers {
        match &spec.node {
            DeclarationSpecifier::StorageClass(storage) => {
                if storage.node == expected {
                    return true;
                }
            },
            _ => continue,
        }
    }
    false
}

fn lang_c_declaration_is_struct_definition(n: &Declaration) -> bool {
    if let Some(spec) = n.specifiers.last() {
        if let DeclarationSpecifier::TypeSpecifier(type_spec) = &spec.node {
            if let TypeSpecifier::Struct(st) = &type_spec.node {
                return st.node.kind.node == StructKind::Struct;
            }
        }
    }
    false
}


fn lang_c_declarator_is_pointer(n: &Declarator) -> bool {
    for derived in &n.derived {
        match &derived.node {
            DerivedDeclarator::Pointer(_) => return true,
            _ => continue,
        }
    }
    false
}

fn lang_c_declarator_name(n: &Declarator) -> &String {
    &cast!(&n.kind.node, DeclaratorKind::Identifier).node.name
}


fn lang_c_type_name_from_type_specifier(spec: &TypeSpecifier) -> Option<&String> {
    match spec {
        TypeSpecifier::TypedefName(n)   => Some(&n.node.name),
        TypeSpecifier::Struct(st)       => Some(&st.node.identifier.as_ref().unwrap().node.name),
        _                               => None
    }
}

fn lang_c_type_name_from_specifier_qualifiers(specs: &Vec<Node<SpecifierQualifier>>) -> Option<&String> {
    for s in specs {
        match &s.node {
            SpecifierQualifier::TypeSpecifier(t) => {
                if let Some(n) = lang_c_type_name_from_type_specifier(&t.node) { return Some(n); }
            },
            _ => {}
        }
    }
    None
}

fn lang_c_type_name_from_declaration_specifiers(specs: &Vec<Node<DeclarationSpecifier>>) -> Option<&String> {
    for s in specs {
        match &s.node {
            DeclarationSpecifier::TypeSpecifier(t) => { 
                if let Some(n) = lang_c_type_name_from_type_specifier(&t.node) { return Some(n); }
            },
            _ => {}
        }
    }
    None
}


fn lang_c_expression_is_binary_assign(n: &Expression) -> bool {
    match n {
        Expression::BinaryOperator(bo) => bo.node.operator.node == BinaryOperator::Assign,
        _ => false,
    }
}

fn lang_c_expression_is_global_array_key_value_pair_list(n: &Expression) -> bool {
    match n {
        Expression::Comma(b) => (*b).iter().all(|x| lang_c_expression_is_binary_assign(&x.node)),
        _ => lang_c_expression_is_binary_assign(n),
    }
}

// static TYPE *name = (key=value, ...);
fn lang_c_declaration_is_global_array(n: &Declaration) -> bool {    
    if n.declarators.len() != 1 {
        return false;
    }

    let init_decl = &n.declarators.first().unwrap().node;
    if !lang_c_declarator_is_pointer(&init_decl.declarator.node) {
        return false;
    }

    if let Some(i) = &init_decl.initializer {
        let init = &i.node;
        if let Initializer::Expression(e) = init {
            if !lang_c_expression_is_global_array_key_value_pair_list(&e.node) {
                return false;
            }
        } else {
            return false;
        }
        
        true
    } else {
        false
    }
}

//endregion

//region tests

#[cfg(test)]
mod tests {
    use crate::*;
    
    fn do_parse_types(source: &str) -> Types {
        let config = lang_c::driver::Config::default();
        let u = lang_c::driver::parse_preprocessed(&config, source.to_owned()).unwrap().unit;
        let mut t = Types::new(false);
        TypeParser{types: &mut t}.visit_translation_unit(&u);
        t
    }
    


    #[test]
    fn parse_struct_empty() {
        assert_eq!("X", do_parse_types("typedef struct {} X;").values.last().unwrap().name);
        assert_eq!("X", do_parse_types("typedef struct X {};").values.last().unwrap().name);
        assert_eq!("X", do_parse_types("struct X {};").values.last().unwrap().name);
    }

    #[test]
    fn parse_struct_regular_members() {
        let t = do_parse_types("typedef struct { int a; int b; } X; typedef struct { X a; X b; } Y;");
        let x = t.values.iter().rev().nth(1).unwrap();
        let y = t.values.iter().rev().nth(0).unwrap();
        let int_i = t.find("int");
        let xi = t.find(&x.name);

        assert_eq!("X", x.name);
        assert_eq!(8, x.size);
        assert_eq!(8, x.align);
        assert_eq!(2, x.fields.len());
        
        assert_eq!("a", x.fields[0].name);
        assert_eq!(0, x.fields[0].offset);
        assert_eq!(int_i, x.fields[0].t);
        
        assert_eq!("b", x.fields[1].name);
        assert_eq!(4, x.fields[1].offset);
        assert_eq!(int_i, x.fields[1].t);

        assert_eq!("Y", y.name);
        assert_eq!(16, y.size);
        assert_eq!(16, y.align);
        assert_eq!(2, y.fields.len());

        assert_eq!("a", y.fields[0].name);
        assert_eq!(0, y.fields[0].offset);
        assert_eq!(xi, y.fields[0].t);
        
        assert_eq!("b", y.fields[1].name);
        assert_eq!(8, y.fields[1].offset);
        assert_eq!(xi, y.fields[1].t);
    }

    // TODO:
    //  typedef struct { int a, b; } X;

    #[test]
    fn parse_struct_pointer_members() {
        
    }
}

//endregion
