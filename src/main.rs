extern crate lalrpop;
#[macro_use]
extern crate lalrpop_util;

use std::cmp::max;
use std::collections::HashMap;
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::ops::Deref;
use std::rc::Rc;

use lalrpop_util::{ErrorRecovery, ParseError};
use lalrpop_util::lexer::Token;

lalrpop_mod!(pub parser);

pub enum Top {
    Erase(Rc<Expr>),
    Check(Rc<Expr>),
    Declaration(String, Rc<Expr>),
    Definition(String, Rc<Expr>),
    DefinitionCheck(String, Rc<Expr>),
    Eval(Rc<Expr>),
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum Expr {
    Var(Variable),
    Universe(u64),
    IPi(Abstraction),
    Pi(Abstraction),
    ILambda(Abstraction),
    Lambda(Abstraction),
    IApp(Rc<Expr>, Rc<Expr>),
    App(Rc<Expr>, Rc<Expr>),
}

impl Expr {
    pub fn erase(&self) -> Rc<Expr> {
        match self {
            Expr::Var(v) => Rc::new(Expr::Var(v.clone())),
            Expr::Universe(u) => Rc::new(Expr::Universe(u.clone())),
            Expr::IPi((v, e1, e2)) => e2.erase(),
            Expr::Pi((v, e1, e2)) => Rc::new(Expr::Pi((v.clone(), e1.erase(), e2.erase()))),
            Expr::ILambda((v, e1, e2)) => e2.erase(),
            Expr::Lambda((v, e1, e2)) => Rc::new(Expr::Lambda((v.clone(), e1.erase(), e2.erase()))),
            Expr::IApp(e1, e2) => e1.erase(),
            Expr::App(e1, e2) => Rc::new(Expr::App(e1.erase(), e2.erase())),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Expr::Var(x) => x.fmt(f),
            Expr::Universe(k) => write!(f, "Type {}", k),
            Expr::IPi((x, t, e)) => {
                match e.deref() {
                    Expr::Var(v) => {
                        write!(f, ".{} -> {}", t, v)
                    }
                    _ => write!(f, ".forall ({} : {}) -> {}", x, t, e)
                }
            }
            Expr::Pi((x, t, e)) => {
                match e.deref() {
                    Expr::Var(v) => {
                        write!(f, "{} -> {}", t, v)
                    }
                    _ => write!(f, "forall ({} : {}) -> {}", x, t, e)
                }
            }
            Expr::ILambda((x, t, e)) => write!(f, ".\\{} : {} => {}", x, t, e),
            Expr::Lambda((x, t, e)) => write!(f, "\\{} : {} => {}", x, t, e),
            Expr::IApp(e1, e2) => write!(f, ".({} {})", e1, e2),
            Expr::App(e1, e2) => write!(f, "({} {})", e1, e2),
        }
    }
}

/// (x,t,e) x : t is bound in e
pub type Abstraction = (Variable, Rc<Expr>, Rc<Expr>);

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum Variable {
    String(String),
    Gensym(String, u64),
    Dummy,
}

impl Display for Variable {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Variable::String(x) => write!(f, "{}", x),
            Variable::Gensym(x, i) => write!(f, "{}{}", x, i),
            Variable::Dummy => write!(f, "_"),
        }
    }
}

#[derive(Debug)]
pub struct Context {
    /// maps variables to their types and optional definitions
    vars: HashMap<Variable, (Rc<Expr>, Option<Rc<Expr>>)>
}

impl Context {
    pub fn new() -> Self {
        Self { vars: HashMap::new() }
    }

    pub fn lookup_type(&self, x: &Variable) -> Option<Rc<Expr>> {
        match self.vars.get(x) {
            Some(v) => Some(v.0.clone()),
            None => None
        }
    }

    pub fn lookup_value(&self, x: &Variable) -> Option<Rc<Expr>> {
        match self.vars.get(x) {
            Some(v) => v.1.clone(),
            None => None
        }
    }

    pub fn extend(&self, x: Variable, typ: Rc<Expr>, def: Option<Rc<Expr>>) -> Self {
        let mut new_map = self.vars.clone();
        new_map.insert(x, (typ, def));
        Self {
            vars: new_map,
        }
    }
}

pub struct TypeChecker {
    gensym: u64
}

impl TypeChecker {
    pub fn new() -> Self {
        Self { gensym: 0 }
    }

    /// generates a fresh variable name with the same form
    pub fn refresh(&mut self, variable: Variable) -> Variable {
        self.gensym += 1;
        match variable {
            Variable::String(x) | Variable::Gensym(x, _) => {
                Variable::Gensym(x, self.gensym)
            }
            Variable::Dummy => {
                Variable::Gensym("_".into(), self.gensym)
            }
        }
    }

    /// performs the given substitutions for the variables in the expression
    pub fn substitute(&mut self, substitutions: &HashMap<Variable, Rc<Expr>>, e: Rc<Expr>) -> Rc<Expr> {
        match e.deref() {
            Expr::Var(x) => {
                match substitutions.get(&x) {
                    Some(e) => e.clone(),
                    None => e,
                }
            }
            Expr::IPi(a) => Rc::new(Expr::IPi(self.substitute_abstraction(&substitutions, a.clone()))),
            Expr::Pi(a) => Rc::new(Expr::Pi(self.substitute_abstraction(&substitutions, a.clone()))),
            Expr::ILambda(a) => Rc::new(Expr::ILambda(self.substitute_abstraction(&substitutions, a.clone()))),
            Expr::Lambda(a) => Rc::new(Expr::Lambda(self.substitute_abstraction(&substitutions, a.clone()))),
            Expr::IApp(e1, e2) => Rc::new(Expr::IApp(self.substitute(substitutions, e1.clone()), self.substitute(substitutions, e2.clone()))),
            Expr::App(e1, e2) => Rc::new(Expr::App(self.substitute(substitutions, e1.clone()), self.substitute(substitutions, e2.clone()))),
            _ => e
        }
    }

    fn substitute_abstraction(
        &mut self,
        substitutions: &HashMap<Variable, Rc<Expr>>,
        abstraction: Abstraction,
    ) -> Abstraction {
        let x = abstraction.0;
        let x1 = self.refresh(x.clone());
        let t = self.substitute(substitutions, abstraction.1);
        let mut new_substitutions = substitutions.clone();
        new_substitutions.insert(x, Rc::new(Expr::Var(x1.clone())));
        let e = self.substitute(&new_substitutions, abstraction.2);
        (x1, t, e)
    }

    pub fn infer_type(&mut self, ctx: &mut Context, e: Rc<Expr>) -> Rc<Expr> {
        match e.deref() {
            Expr::Var(x) => {
                match ctx.lookup_type(x) {
                    Some(t) => t,
                    None => {
                        println!("{:#?}", ctx);
                        panic!(format!("can't find variable: {:?}", x))
                    }
                }
            }
            Expr::Universe(k) => Rc::new(Expr::Universe(k + 1)),
            Expr::Pi((x, t1, t2)) | Expr::IPi((x, t1, t2)) => {
                let k1 = self.infer_universe(ctx, t1.clone());
                let mut ctx = ctx.extend(x.clone(), t1.clone(), None);
                let k2 = self.infer_universe(&mut ctx, t2.clone());
                Rc::new(Expr::Universe(max(k1, k2)))
            }
            Expr::ILambda((x, t, e)) => {
                let _ = self.infer_universe(ctx, t.clone());
                let mut ctx = ctx.extend(x.clone(), t.clone(), None);
                let te = self.infer_type(&mut ctx, e.clone());
                Rc::new(Expr::IPi((x.clone(), t.clone(), te)))
            }
            Expr::Lambda((x, t, e)) => {
                let _ = self.infer_universe(ctx, t.clone());
                let mut ctx = ctx.extend(x.clone(), t.clone(), None);
                let te = self.infer_type(&mut ctx, e.clone());
                Rc::new(Expr::Pi((x.clone(), t.clone(), te)))
            }
            Expr::App(e1, e2) | Expr::IApp(e1, e2) => {
                // println!("{} {}", e1, e2);
                let (x, s, t) = self.infer_pi(ctx, e1.clone());
                let te = self.infer_type(ctx, e2.clone());
                // println!("  {} : PI ({}: **{}**) -> {} ==? {} : **{}**", e1, x, s, t, e2, te);
                self.check_equal(ctx, s, te);
                let mut new = HashMap::new();
                new.insert(x, e2.clone());
                self.substitute(&new, t)
            }
        }
    }

    /// infer the universe level of the type in the context
    fn infer_universe(&mut self, ctx: &mut Context, typ: Rc<Expr>) -> u64 {
        let u = self.infer_type(ctx, typ);
        match self.normalize(ctx, u).deref() {
            Expr::Universe(k) => k.clone(),
            e => { panic!(format!("found expr {} when universe was expected", e)) }
        }
    }

    /// infer the type of the expression in the context, verifying that it is
    /// a Pi expression and returns the abstraction
    fn infer_pi(&mut self, ctx: &mut Context, e: Rc<Expr>) -> Abstraction {
        let t = self.infer_type(ctx, e.clone());
        match self.normalize(ctx, t).deref() {
            Expr::Pi(a) | Expr::IPi(a) => a.clone(),
            e1 => { panic!(format!("found expr {} ==> {} when pi was expected", e, e1)) }
        }
    }

    fn check_equal(&mut self, ctx: &mut Context, e1: Rc<Expr>, e2: Rc<Expr>) {
        if !self.equal(ctx, e1.clone(), e2.clone()) {
            panic!(format!("expressions {} and {} are not equal?", e1, e2))
        }
    }

    /// normalizes the expression in the context, removing all redexes and unfolding all definitions
    fn normalize(&mut self, ctx: &mut Context, e: Rc<Expr>) -> Rc<Expr> {
        match e.deref() {
            Expr::Var(x) => {
                match ctx.lookup_value(x) {
                    Some(e) => self.normalize(ctx, e),
                    None => {
                        match ctx.lookup_type(x) {
                            Some(_t) => e,
                            None => {
                                for (v, (t, e)) in ctx.vars.iter() {
                                    println!("{} : {} = {:#?}", v, t, e);
                                }
                                panic!(format!("can't find variable: {:?}", x))
                            }
                        }
                    }
                }
            }
            Expr::App(e1, e2) => {
                let e2 = self.normalize(ctx, e2.clone());
                let e1 = self.normalize(ctx, e1.clone());
                match e1.deref() {
                    Expr::Lambda((x, _, e1)) => {
                        let mut new = HashMap::new();
                        new.insert(x.clone(), e2.clone());
                        let e1 = self.substitute(&new, e1.clone());
                        self.normalize(ctx, e1)
                    }
                    _ => Rc::new(Expr::App(e1, e2))
                }
            }
            Expr::IPi(a) => Rc::new(Expr::IPi(self.normalize_abstraction(ctx, a))),
            Expr::Pi(a) => Rc::new(Expr::Pi(self.normalize_abstraction(ctx, a))),
            Expr::ILambda(a) => Rc::new(Expr::ILambda(self.normalize_abstraction(ctx, a))),
            Expr::Lambda(a) => Rc::new(Expr::Lambda(self.normalize_abstraction(ctx, a))),
            _ => e
        }
    }

    fn normalize_abstraction(&mut self, ctx: &mut Context, abstraction: &Abstraction) -> Abstraction {
        let (x, t, e) = abstraction;
        let t = self.normalize(ctx, t.clone());
        let mut ctx = ctx.extend(x.clone(), t.clone(), None);
        (x.clone(), t, self.normalize(&mut ctx, e.clone()))
    }

    fn equal(&mut self, ctx: &mut Context, e1: Rc<Expr>, e2: Rc<Expr>) -> bool {
        let e1 = self.normalize(ctx, e1);
        let e2 = self.normalize(ctx, e2);
        match (e1.deref(), e2.deref()) {
            (Expr::Var(x1), Expr::Var(x2)) => x1 == x2,
            (Expr::App(e11, e12), Expr::App(e21, e22)) =>
                self.equal(ctx, e11.clone(), e21.clone()) &&
                    self.equal(ctx, e12.clone(), e22.clone()),
            (Expr::IApp(e11, e12), Expr::IApp(e21, e22)) =>
                self.equal(ctx, e11.clone(), e21.clone()) &&
                    self.equal(ctx, e12.clone(), e22.clone()),
            (Expr::Universe(k1), Expr::Universe(k2)) => k1 == k2,
            (Expr::Pi(a1), Expr::Pi(a2)) => self.equal_abstraction(ctx, a1, a2),
            (Expr::Lambda(a1), Expr::Lambda(a2)) => self.equal_abstraction(ctx, a1, a2),
            (Expr::IPi(a1), Expr::IPi(a2)) => self.equal_abstraction(ctx, a1, a2),
            (Expr::ILambda(a1), Expr::ILambda(a2)) => self.equal_abstraction(ctx, a1, a2),
            _ => false
        }
    }

    fn equal_abstraction(&mut self, ctx: &mut Context, a1: &Abstraction, a2: &Abstraction) -> bool {
        let (x, t1, e1) = a1;
        let (y, t2, e2) = a2;
        let mut new = HashMap::new();
        new.insert(y.clone(), Rc::new(Expr::Var(x.clone())));

        let e2 = self.substitute(&new, e2.clone());
        self.equal(ctx, t1.clone(), t2.clone()) && (self.equal(ctx, e1.clone(), e2))
    }
}

fn main() {
    let mut ctx = Context::new();
    let mut checker = TypeChecker::new();

    let code = r"
Ty : Type 1
N : Type 0
B : Type 0
Z : N
S : forall _: N -> N
tZ = N
tS = forall _ : N -> N
C = forall s: tS -> (forall _: tZ -> N)
zero = \s : tS => \z : tZ => z
one = \s : tS => \z : tZ => (s z)
two = \s : tS => \z : tZ => (s (s z))
three = \s : tS => \z : tZ => (s (s (s z)))
four = \s : tS => \z : tZ => (s ((three s) z))
add = \m : C => \n : C => \s : tS => \z : tZ => ((m s) ((n s) z))

check (three S)
check (three (three S))
eval ((three (three S)) Z)
tthree = check three

check (S (S Z))

Vec : Π x : Type 0 -> (.Π l : C -> Type 0)
append : Π T : Type 0 -> (.Π n : C -> (.Π m : C -> (Π _ : .((Vec T) n) -> (Π _ : .((Vec T) m) -> .((Vec T) ((add m) n) )))))
tappend = check append
VecN2 : .((Vec B) one)
tVecN2 = check VecN2

erase Vec
erase append

BU = check \f : Type 0 => B

";
    let mut errors: Vec<ErrorRecovery<usize, Token, &str>> = Vec::new();
    let result: Result<Vec<Top>, ParseError<usize, Token, &str>> = parser::ProgramParser::new().parse(&mut errors, code);
    match result {
        Ok(tops) => {
            for top in tops {
                match top {
                    Top::Check(def) => {
                        let typ = checker.infer_type(&mut ctx, def.clone());
                        println!("{} : {}", def, typ);
                    }
                    Top::Erase(def) => {
                        let typ = checker.infer_type(&mut ctx, def.clone()).erase();
                        println!("erased {} : {}\n", def, typ);
                    }
                    Top::Declaration(name, typ) => {
                        println!("{} : {}", name, typ);
                        ctx = ctx.extend(Variable::String(name), typ, None);
                    }
                    Top::Definition(name, def) => {
                        let typ = checker.infer_type(&mut ctx, def.clone());
                        println!("{} = {}", name, def.clone());
                        println!("{}: {}\n", " ".repeat(name.len() + 1), typ.clone());
                        ctx = ctx.extend(Variable::String(name), typ, Some(def));
                    }
                    Top::DefinitionCheck(name, def) => {
                        let typ = checker.infer_type(&mut ctx, def.clone());
                        let typ_of_typ = checker.infer_type(&mut ctx, typ.clone());
                        println!("{} : {}", name, typ.clone());
                        println!("{}: {}\n", " ".repeat(name.len() + 1), typ_of_typ.clone());
                        ctx = ctx.extend(Variable::String(name), typ_of_typ, Some(typ));
                    }
                    Top::Eval(e) => {
                        let e1 = checker.normalize(&mut ctx, e.clone());
                        let t = checker.infer_type(&mut ctx, e1.clone());
                        println!("{}\n    = {}\n    : {}", e, e1, t);
                    }
                }
            }
        }
        Err(e) => eprintln!("{}", e.to_string())
    }
}
