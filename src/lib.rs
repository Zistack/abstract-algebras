use std::collections::HashSet;

use proc_macro::TokenStream;
use syn::{Attribute, Ident, Expr, UnOp, BinOp, Token, parse_quote, parse_macro_input};
use syn::token::Paren;
use syn::punctuated::Punctuated;
use syn::fold::{Fold, fold_expr};
use syn_derive::Parse;
use quote::ToTokens;

fn un_op_ident (un_op: &UnOp) -> Option <Ident>
{
	match un_op
	{
		UnOp::Not (_) => Some (parse_quote! (not)),
		UnOp::Neg (_) => Some (parse_quote! (neg)),
		_ => None
	}
}

fn bin_op_ident (bin_op: &BinOp) -> Option <Ident>
{
	match bin_op
	{
		BinOp::Add (_) => Some (parse_quote! (add)),
		BinOp::Sub (_) => Some (parse_quote! (sub)),
		BinOp::Mul (_) => Some (parse_quote! (mul)),
		BinOp::Div (_) => Some (parse_quote! (div)),
		BinOp::Rem (_) => Some (parse_quote! (rem)),
		BinOp::And (_) => Some (parse_quote! (and)),
		BinOp::Or (_) => Some (parse_quote! (or)),
		BinOp::BitXor (_) => Some (parse_quote! (bitxor)),
		BinOp::BitAnd (_) => Some (parse_quote! (bitand)),
		BinOp::BitOr (_) => Some (parse_quote! (bitor)),
		BinOp::Shl (_) => Some (parse_quote! (shl)),
		BinOp::Shr (_) => Some (parse_quote! (shr)),
		BinOp::Eq (_) => Some (parse_quote! (eq)),
		BinOp::Lt (_) => Some (parse_quote! (lt)),
		BinOp::Le (_) => Some (parse_quote! (le)),
		BinOp::Ne (_) => Some (parse_quote! (ne)),
		BinOp::Ge (_) => Some (parse_quote! (ge)),
		BinOp::Gt (_) => Some (parse_quote! (gt)),
		BinOp::AddAssign (_) => Some (parse_quote! (add_assign)),
		BinOp::SubAssign (_) => Some (parse_quote! (sub_assign)),
		BinOp::MulAssign (_) => Some (parse_quote! (mul_assign)),
		BinOp::DivAssign (_) => Some (parse_quote! (div_assign)),
		BinOp::RemAssign (_) => Some (parse_quote! (rem_assign)),
		BinOp::BitXorAssign (_) => Some (parse_quote! (bitxor_assign)),
		BinOp::BitAndAssign (_) => Some (parse_quote! (bitand_assign)),
		BinOp::BitOrAssign (_) => Some (parse_quote! (bitor_assign)),
		BinOp::ShlAssign (_) => Some (parse_quote! (shl_assign)),
		BinOp::ShrAssign (_) => Some (parse_quote! (shr_assign)),
		_ => None
	}
}

struct AlgebraInjector
{
	algebra: Expr,
	unary_ops: HashSet <UnOp>,
	binary_ops: HashSet <BinOp>,
	methods: HashSet <Ident>,
}

impl Fold for AlgebraInjector
{
	fn fold_expr (&mut self, expr: Expr) -> Expr
	{
		match expr
		{
			Expr::Unary (expr) =>
			{
				if self . unary_ops . contains (&expr . op)
				{
					if let Some (op_ident) = un_op_ident (&expr . op)
					{
						let attrs: Vec <Attribute> = expr
							. attrs
							. into_iter ()
							. map (|attr| self . fold_attribute (attr))
							. collect ();
						let expr = self . fold_expr (*expr . expr);

						let algebra = &self . algebra;
						return parse_quote!
						(
							#(#attrs)*
							#algebra . clone () . #op_ident (#expr)
						);
					}
				}

				Expr::Unary (self . fold_expr_unary (expr))
			},
			Expr::Binary (expr) =>
			{
				if self . binary_ops . contains (&expr . op)
				{
					if let Some (op_ident) = bin_op_ident (&expr . op)
					{
						let attrs: Vec <Attribute> = expr
							. attrs
							. into_iter ()
							. map (|attr| self . fold_attribute (attr))
							. collect ();
						let left = self . fold_expr (*expr . left);
						let right = self . fold_expr (*expr . right);

						let algebra = &self . algebra;
						return parse_quote!
						(
							#(#attrs)*
							#algebra . clone () . #op_ident (#left, #right)
						);
					}
				}

				Expr::Binary (self . fold_expr_binary (expr))
			},
			Expr::MethodCall (expr) =>
			{
				if self . methods . contains (&expr . method)
				{
					let attrs: Vec <Attribute> = expr
						. attrs
						. into_iter ()
						. map (|attr| self . fold_attribute (attr))
						. collect ();
					let receiver = self . fold_expr (*expr . receiver);
					let method = expr . method;
					let turbofish = expr
						. turbofish
						. map (|args| self . fold_angle_bracketed_generic_arguments (args));
					let args: Punctuated <Expr, Token! [,]> = expr
						. args
						. into_iter ()
						. map (|arg| self . fold_expr (arg))
						. collect ();

					let algebra = &self . algebra;
					parse_quote!
					(
						#(#attrs)*
						#algebra . clone () . #method #turbofish (#receiver, #args)
					)
				}
				else
				{
					Expr::MethodCall (self . fold_expr_method_call (expr))
				}
			},
			_ => fold_expr (self, expr)
		}
	}
}

#[allow (dead_code)]
#[derive (Parse)]
struct UseAlgebra
{
	algebra: Expr,
	comma_token: Token! [,],
	expr: Expr,

	semicolon_token: Token! [;],

	#[syn (parenthesized)]
	u_paren_token: Paren,
	#[syn (in = u_paren_token)]
	#[parse (Punctuated::parse_terminated)]
	unary_ops: Punctuated <UnOp, Token! [,]>,

	#[syn (parenthesized)]
	b_paren_token: Paren,
	#[syn (in = b_paren_token)]
	#[parse (Punctuated::parse_terminated)]
	binary_ops: Punctuated <BinOp, Token! [,]>,

	#[syn (parenthesized)]
	m_paren_token: Paren,
	#[syn (in = m_paren_token)]
	#[parse (Punctuated::parse_terminated)]
	methods: Punctuated <Ident, Token! [,]>
}

#[proc_macro]
pub fn use_algebra (input: TokenStream) -> TokenStream
{
	let UseAlgebra {algebra, expr, unary_ops, binary_ops, methods, ..} =
		parse_macro_input! (input);

	AlgebraInjector
	{
		algebra,
		unary_ops: HashSet::from_iter (unary_ops),
		binary_ops: HashSet::from_iter (binary_ops),
		methods: HashSet::from_iter (methods)
	}
		. fold_expr (expr)
		. into_token_stream ()
		. into ()
}
