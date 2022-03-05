use proc_macro::TokenStream;
use quote::quote;
use syn::*;

#[proc_macro_derive(Lower)]
pub fn derive_lower(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let mut ex_generics: Generics = parse2(quote! { #impl_generics }).unwrap();
    let mut alt_generics: Generics = parse2(quote! { #ty_generics }).unwrap();
    let ex_lifetime: Lifetime = parse_quote! { '__lower };
    ex_generics.params.insert(0, GenericParam::Lifetime(LifetimeDef::new(ex_lifetime.clone())));

    // Substitute first lifetime parameter if it exists
    if let Some(GenericParam::Lifetime(def)) = &mut alt_generics.params.first_mut() {
         *def = LifetimeDef::new(ex_lifetime.clone())
    }
    
    // Add lifetime bound to where clause
    let add_where_clause: WhereClause = parse_quote! { where #name #alt_generics: #ex_lifetime };
    let where_clause = match where_clause {
        Some(cur_where_clause) => {
            let mut where_clause = cur_where_clause.clone();
            for predicate in add_where_clause.predicates {
                where_clause.predicates.push(predicate);
            }
            where_clause
        }
        None => add_where_clause
    };

    // Build implementation
    TokenStream::from(quote! {
        unsafe impl #ex_generics ::fortify::Lower<#ex_lifetime> for #name #ty_generics #where_clause {
            type Target = #name #alt_generics;
            fn lower_ref<'__ref>(&'__ref self) -> &'__ref Self::Target
            where
                Self: #ex_lifetime,
                #ex_lifetime: '__ref,
            {
                self
            }
        }
    })
}