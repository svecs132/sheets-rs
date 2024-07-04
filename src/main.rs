//! a google sheets formula evaluator in rust

use core::fmt;
use std::{collections::HashMap, io::Write, rc::Rc, result};

use chrono::Local;

mod utils;

/// A type alias for the result of a function that can return an error message.
type Result<T> = result::Result<T, Box<str>>;

/// The different types of tokens in the formula language.
#[derive(Debug, Clone, Copy, PartialEq)]
enum TokenType {
  // Single-character tokens
  LParen,
  RParen,
  Comma,
  Plus,
  Minus,
  Star,
  Slash,

  // Literals
  Number,

  // Keywords
  Identifier,
}

impl fmt::Display for TokenType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{:?}", self)
  }
}

/// A token in the formula language.
#[derive(Debug, Clone)]
struct Token {
  t_type: TokenType,
  lexeme: Rc<str>,
  pos:    usize,
}

impl Token {
  fn new(t_type: TokenType, lexeme: &str, pos: usize) -> Token {
    Token {
      t_type,
      lexeme: lexeme.into(),
      pos,
    }
  }
}

impl fmt::Display for Token {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self.t_type {
      TokenType::Number => write!(f, "{}({})", self.t_type, self.lexeme)?,
      TokenType::Identifier => write!(f, "{}({})", self.t_type, self.lexeme)?,
      _ => write!(f, "{}", self.t_type)?,
    }
    // write!(f, "@{}", self.pos)?;
    Ok(())
  }
}

/// A lexer for `sheets-rs` formulas (based on Google Sheets but might vary
/// slightly)
struct Lexer {
  src: Vec<char>,
  pos: usize,
  out: Vec<Token>,
}

impl Lexer {
  //! All the methods for the Lexer struct leave the pos pointing to the next
  //! unread character in the source code. If the pos is at the end of the
  //! source code, the peek and next methods will return None.

  /// Creates a new lexer with the given source code.
  fn new(src: &str) -> Lexer {
    Lexer {
      src: src.chars().collect(),
      pos: 0,
      out: Vec::new(),
    }
  }

  /// Returns the current character in the source code without advancing the
  /// position or None if the position is at the end of the source code.
  #[allow(dead_code)]
  fn peek(&self) -> Option<char> {
    self.src.get(self.pos).copied()
  }

  /// Returns the current character in the source code and advances the
  /// position or None if the position is at the end of the source code.
  #[allow(dead_code)]
  fn next(&mut self) -> Option<char> {
    let c = self.peek();
    if c.is_some() {
      self.pos += 1;
    }
    c
  }

  /// Returns the current n characters in the source code without advancing the
  /// position or None if the position is less than n characters from the end of
  /// the source code.
  #[allow(dead_code)]
  fn peek_n(&self, n: usize) -> Option<&[char]> {
    self.src.get(self.pos..self.pos + n)
  }

  /// Returns the current n characters in the source code and advances the
  /// position by n or None if the position is less than n characters from the
  /// end of the source code.
  #[allow(dead_code)]
  fn next_n(&mut self, n: usize) -> Option<&[char]> {
    let s = self.src.get(self.pos..self.pos + n);
    if s.is_some() {
      self.pos += n;
    }
    s
  }

  /// Makes a token from the current character and adds it to the output.
  fn push_token(&mut self, t_type: TokenType, lexeme: &str, pos: usize) {
    self.out.push(Token::new(t_type, lexeme, pos));
  }

  /// Lexes a number from the source code and adds it to the output.
  fn lex_number(&mut self) {
    let p = self.pos;
    let mut num = String::new();
    while let Some(c) = self.peek() {
      if c.is_ascii_digit() {
        num.push(c);
        self.next();
      } else {
        break;
      }
    }
    self.push_token(TokenType::Number, &num, p);
  }

  /// Lexes an identifier from the source code and adds it to the output.
  fn lex_identifier(&mut self) {
    let p = self.pos;
    let mut id = String::new();
    while let Some(c) = self.peek() {
      if c.is_ascii_alphanumeric() || c == '_' {
        id.push(c);
        self.next();
      } else {
        break;
      }
    }
    self.push_token(TokenType::Identifier, &id, p);
  }

  /// Lexes the source code and returns a vector of tokens in a Result. If the
  /// source code is invalid, an error is returned. The position is reset to
  /// the beginning of the source code.
  fn lex(&mut self) -> Result<Rc<[Token]>> {
    self.out.clear();
    self.pos = 0;

    while self.pos < self.src.len() {
      if let Some(c) = self.peek() {
        match c {
          ' ' | '\t' | '\n' => {
            self.next();
          },
          '(' => {
            self.push_token(TokenType::LParen, "(", self.pos);
            self.next();
          },
          ')' => {
            self.push_token(TokenType::RParen, ")", self.pos);
            self.next();
          },
          ',' => {
            self.push_token(TokenType::Comma, ",", self.pos);
            self.next();
          },
          '+' => {
            self.push_token(TokenType::Plus, "+", self.pos);
            self.next();
          },
          '-' => {
            self.push_token(TokenType::Minus, "-", self.pos);
            self.next();
          },
          '*' => {
            self.push_token(TokenType::Star, "*", self.pos);
            self.next();
          },
          '/' => {
            self.push_token(TokenType::Slash, "/", self.pos);
            self.next();
          },
          '0'..='9' => self.lex_number(),
          'a'..='z' | 'A'..='Z' | '_' => self.lex_identifier(),
          _ => {
            return Err(format!("unexpected character: '{}' at position {}", c, self.pos).into())
          },
        }
      } else {
        break;
      }
    }

    Ok(self.out.clone().into())
  }
}

/// An expression in the formula language.
#[derive(Debug, Clone)]
#[allow(dead_code)]
enum Expr {
  Number(f64),
  Identifier(Rc<str>),
  Binary(Box<Expr>, TokenType, Box<Expr>),
  Call(Rc<str>, Vec<Expr>),
}

/// A parser for `sheets-rs` formulas.
struct Parser {
  src:     Rc<[Token]>,
  pos:     usize,
  src_pos: usize,
}

impl Parser {
  //! All the methods for the Parser struct leave the pos pointing to the next
  //! unread token in the tokens. If the pos is at the end of the tokens, the
  //! peek and next methods will return None.

  /// Creates a new parser with the given tokens.
  fn new(tokens: &Rc<[Token]>) -> Parser {
    Parser {
      src:     tokens.clone(),
      pos:     0,
      src_pos: 0,
    }
  }

  /// Returns the current token in the tokens without advancing the position or
  /// None if the position is at the end of the tokens.
  #[allow(dead_code)]
  fn peek(&self) -> Option<Token> {
    self.src.get(self.pos).cloned()
  }

  /// Returns the current token in the tokens and advances the position or None
  /// if the position is at the end of the tokens.
  #[allow(dead_code)]
  fn next(&mut self) -> Option<Token> {
    let t = self.src.get(self.pos);
    if let Some(t) = t {
      self.pos += 1;
      self.src_pos = t.pos;
    }
    t.cloned()
  }

  /// Returns the current n tokens in the tokens without advancing the position
  /// or None if the position is less than n tokens from the end of the tokens.
  /// The tokens are returned as a slice.
  #[allow(dead_code)]
  fn peek_n(&self, n: usize) -> Option<&[Token]> {
    self.src.get(self.pos..self.pos + n)
  }

  /// Returns the current n tokens in the tokens and advances the position by n
  /// or None if the position is less than n tokens from the end of the tokens.
  /// The tokens are returned as a slice.
  #[allow(dead_code)]
  fn next_n(&mut self, n: usize) -> Option<&[Token]> {
    let t = self.src.get(self.pos..self.pos + n);
    if let Some(t) = t {
      self.pos += n;
      self.src_pos = t[t.len() - 1].pos;
    }
    t
  }

  /// Parses a number from the tokens and returns it as an expression.
  fn parse_number(&mut self) -> Result<Expr> {
    // log!(DEBUG: "parsing number");
    if let Some(t) = self.next() {
      match t.t_type {
        TokenType::Number => {
          let n = t.lexeme.parse().unwrap();
          Ok(Expr::Number(n))
        },
        _ => {
          let t = self.next().unwrap();
          Err(format!("expected number, found {} at position {}", t, self.src_pos).into())
        },
      }
    } else {
      Err("expected number, found end of input".into())
    }
  }

  /// Parses an identifier from the tokens and returns it as an expression.
  fn parse_identifier(&mut self) -> Result<Expr> {
    // log!(DEBUG: "parsing identifier");
    if let Some(t) = self.next() {
      match t.t_type {
        TokenType::Identifier => Ok(Expr::Identifier(t.lexeme.clone())),
        _ => {
          let t = self.next().unwrap();
          Err(
            format!(
              "expected identifier, found {} at position {}",
              t, self.src_pos
            )
            .into(),
          )
        },
      }
    } else {
      Err("expected identifier, found end of input".into())
    }
  }

  /// Parses a call from the tokens and returns it as an expression.
  fn parse_call(&mut self) -> Result<Expr> {
    // log!(DEBUG: "parsing call");
    if let Some(t) = self.next() {
      match t.t_type {
        TokenType::Identifier => {
          let id = t.lexeme.clone();
          let mut args = Vec::new();
          self.next();
          loop {
            if let Some(t) = self.peek() {
              match t.t_type {
                TokenType::RParen => {
                  self.next();
                  break;
                },
                _ => {
                  let arg = self.parse()?;
                  args.push(arg);
                  if let Some(t) = self.peek() {
                    match t.t_type {
                      TokenType::Comma => {
                        self.next();
                      },
                      TokenType::RParen => {
                        self.next();
                        break;
                      },
                      _ => {
                        let t = self.next().unwrap();
                        return Err(
                          format!(
                            "expected ',' or ')', found {} at position {}",
                            t, self.src_pos
                          )
                          .into(),
                        );
                      },
                    }
                  } else {
                    return Err("expected ',' or ')', found end of input".into());
                  }
                },
              }
            } else {
              return Err("expected ')', found end of input".into());
            }
          }
          Ok(Expr::Call(id, args))
        },
        _ => {
          let t = self.next().unwrap();
          Err(
            format!(
              "expected identifier, found {} at position {}",
              t, self.src_pos
            )
            .into(),
          )
        },
      }
    } else {
      Err("expected identifier, found end of input".into())
    }
  }

  /// Parses a primary expression from the tokens and returns it as an
  /// expression.
  fn parse_primary(&mut self) -> Result<Expr> {
    // log!(DEBUG: "parsing primary");
    if let Some(t) = self.peek() {
      match t.t_type {
        TokenType::Number => self.parse_number(),
        TokenType::Identifier => {
          let old_pos = self.pos;
          let old_src_pos = self.src_pos;
          match self.parse_call() {
            Ok(expr) => Ok(expr),
            Err(_) => {
              self.pos = old_pos;
              self.src_pos = old_src_pos;
              self.parse_identifier()
            },
          }
        },
        TokenType::LParen => {
          self.next();
          let expr = self.parse()?;
          if let Some(t) = self.peek() {
            match t.t_type {
              TokenType::RParen => {
                self.next();
                Ok(expr)
              },
              _ => {
                let t = self.next().unwrap();
                Err(format!("expected ')', found {} at position {}", t, self.src_pos).into())
              },
            }
          } else {
            Err("expected ')', found end of input".into())
          }
        },
        _ => {
          let t = self.next().unwrap();
          Err(
            format!(
              "expected number, identifier, or '(', found {} at position {}",
              t, self.src_pos
            )
            .into(),
          )
        },
      }
    } else {
      Err("expected number, identifier, or '(', found end of input".into())
    }
  }

  /// Parses a binary expression from the tokens and returns it as an
  /// expression. The precedence of the current operator is compared to the
  /// precedence of the next operator to determine if the next operator should
  /// be parsed first.
  fn parse_binary(&mut self, precedence: i32) -> Result<Expr> {
    // log!(DEBUG: "parsing binary");
    let mut expr = self.parse_primary()?;
    while let Some(t) = self.peek() {
      match t.t_type {
        TokenType::Plus | TokenType::Minus | TokenType::Star | TokenType::Slash => {
          let next_precedence = match t.t_type {
            TokenType::Plus => 1,
            TokenType::Minus => 1,
            TokenType::Star => 2,
            TokenType::Slash => 2,
            _ => unreachable!(),
          };
          if next_precedence < precedence {
            break;
          }
          self.next();
          let right = self.parse_binary(next_precedence + 1)?;
          expr = Expr::Binary(Box::new(expr), t.t_type, Box::new(right));
        },
        _ => break,
      }
    }
    Ok(expr)
  }

  /// Parses an expression from the tokens and returns it as an expression.
  /// The precedence of the current operator is compared to the precedence of
  /// the next operator to determine if the next operator should be parsed
  /// first.
  fn parse(&mut self) -> Result<Expr> {
    // log!(DEBUG: "parsing");
    self.parse_binary(1)
  }
}

/// A function that evaluates an expression and returns the result as a float.
/// If the expression is invalid, an error is returned.
fn eval(expr: &Expr) -> Result<f64> {
  fn eval_(expr: &Expr, env: HashMap<Rc<str>, f64>) -> Result<f64> {
    let env = env;
    match expr {
      Expr::Number(n) => Ok(*n),
      Expr::Identifier(id) => {
        if let Some(n) = env.get(id) {
          Ok(*n)
        } else {
          Err(format!("undefined identifier: {}", id).into())
        }
      },
      Expr::Binary(left, op, right) => {
        let left = eval_(left, env.clone())?;
        let right = eval_(right, env.clone())?;
        match op {
          TokenType::Plus => Ok(left + right),
          TokenType::Minus => Ok(left - right),
          TokenType::Star => Ok(left * right),
          TokenType::Slash => Ok(left / right),
          _ => unreachable!(),
        }
      },
      Expr::Call(_, _) => Err("function calls are not yet implemented".into()),
    }
  }

  let mut env = HashMap::new();
  env.insert("pi".into(), std::f64::consts::PI);
  env.insert("e".into(), std::f64::consts::E);

  eval_(expr, env)
}

fn main() {
  log!(INFO: "sheets-rs v0.1.0");

  let mut input = String::new();
  print!("Enter a formula: ");
  std::io::stdout().flush().unwrap();
  std::io::stdin().read_line(&mut input).unwrap();

  let formula: Box<str> = input.trim().into();

  log!(INFO: "formula: {}", formula);
  log!(INFO: "lexing...");

  let mut lexer = Lexer::new(&formula);
  let tokens = match lexer.lex() {
    Ok(t) => t,
    Err(e) => {
      log!(ERROR: "{}", e);
      return;
    },
  };

  log!(OUTPUT: "tokens: {}", tokens.iter().map(|t| format!("{}", t)).collect::<Vec<_>>().join(", "));

  log!(INFO: "parsing...");

  let mut parser = Parser::new(&tokens);
  let expr = match parser.parse() {
    Ok(e) => e,
    Err(e) => {
      log!(ERROR: "{}", e);
      return;
    },
  };

  log!(OUTPUT: "expression: {:?}", expr);

  log!(INFO: "evaluating...");

  let result = match eval(&expr) {
    Ok(r) => r,
    Err(e) => {
      log!(ERROR: "{}", e);
      return;
    },
  };

  log!(OUTPUT: "result: {}", result);
}
