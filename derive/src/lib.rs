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
    match &mut alt_generics.params.first_mut() {
        Some(GenericParam::Lifetime(def)) => *def = LifetimeDef::new(ex_lifetime.clone()),
        _ => { } // No lifetime parameter to substitute
    }
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