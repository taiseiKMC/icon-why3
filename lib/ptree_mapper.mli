open Why3.Ptree

type mapper = {
  ident : ident -> ident;
  qualid : mapper -> qualid -> qualid;
  pty : mapper -> pty -> pty;
  pattern : mapper -> pattern -> pattern;
  term : mapper -> term -> term;
}

val default_mapper : mapper
val apply_term : term -> mapper -> term
