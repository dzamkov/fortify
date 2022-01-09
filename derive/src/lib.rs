use proc_macro::TokenStream;
use quote::quote;
use syn::*;

#[proc_macro_derive(WithLifetime)]
pub fn derive_with_lifetime(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let mut ex_generics: Generics = parse2(quote! { #impl_generics }).unwrap();
    let mut alt_generics: Generics = parse2(quote! { #ty_generics }).unwrap();
    let ex_lifetime: Lifetime = parse_quote! { '__forify_new };
    let ex_lifetime_param = GenericParam::Lifetime(LifetimeDef::new(ex_lifetime.clone()));
    ex_generics.params.insert(0, ex_lifetime_param.clone());
    alt_generics.params[0] = ex_lifetime_param.clone();
    TokenStream::from(quote! {
        impl #ex_generics ::fortify::WithLifetime<#ex_lifetime> for #name #ty_generics #where_clause {
            type Target = #name #alt_generics;
        }
    })
}
