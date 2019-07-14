trait Lazy_Term<'a, T>{
    fn get_term(&self) -> &Term<'a, T>;
}

enum Term<'a, T> {
    C(&'a Lazy_Term<'a, T>, &'a Lazy_Term<'a, T>),
    A(T),
}

struct Unev_Term<'a, T> {
    term: Option<>
}

impl<'a, T> Lazy_Term<'a, T> for Term<'a, T> {
    fn get_term(&self) -> &Term<'a, T>{
        return self;
    }
}

//struct choice<'a, T> {
//
//}


fn main() {
    println!("Hello, world!");
}
