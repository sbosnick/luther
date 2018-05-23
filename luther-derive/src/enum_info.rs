// Copyright 2018 Steven Bosnick
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE-2.0 or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms

use std::fmt;

use syn::{self, visit};

/// `EnumInfo` gathers the relevant information about an `enum`
/// for which `Lexer` is being derived. The main way of constructing
/// an `EnumInfo` is through its `From<syn::DeriveInput>` implementation.
pub struct EnumInfo<'ast> {
    pub name: &'ast syn::Ident,
    pub dfa_name: String,
    pub vis: &'ast syn::Visibility,
    pub variants: Vec<VariantInfo<'ast>>,
}

/// `VariantInfo` gathers the relevant information a variant of an `enum`
/// for which `Lexer` is being derived. The main way of constructing
/// a `VariantInfo` is through the `From<syn::DeriveInput> implementation
/// for `EnumInfo`.
pub struct VariantInfo<'ast> {
    pub name: &'ast syn::Ident,
    pub regex: String,
    pub priority_group: u32,
    pub field: Option<&'ast syn::Field>,
}

impl<'ast> From<&'ast syn::DeriveInput> for EnumInfo<'ast> {
    fn from(input: &'ast syn::DeriveInput) -> Self {
        let mut builder = EnumInfoBuilder::new(&input.ident, &input.vis);
        visit::visit_derive_input(&mut builder, input);

        let name = builder.name;
        let dfa_name = builder.dfa_name.unwrap_or_else(|| make_dfa_name(name));

        EnumInfo {
            name,
            dfa_name,
            vis: builder.vis,
            variants: builder.variants,
        }
    }
}

fn make_dfa_name(name: &syn::Ident) -> String {
    let mut name = name.to_string();
    name.push_str("Dfa");
    name
}

struct EnumInfoBuilder<'ast> {
    name: &'ast syn::Ident,
    vis: &'ast syn::Visibility,
    dfa_name: Option<String>,
    variants: Vec<VariantInfo<'ast>>,
}

impl<'ast> EnumInfoBuilder<'ast> {
    fn new(name: &'ast syn::Ident, vis: &'ast syn::Visibility) -> Self {
        EnumInfoBuilder {
            name,
            vis,
            dfa_name: None,
            variants: Vec::new(),
        }
    }
}

impl<'ast> visit::Visit<'ast> for EnumInfoBuilder<'ast> {
    fn visit_data_struct(&mut self, _: &'ast syn::DataStruct) {
        panic!("lunther: #[derive(Lexer)] not valid on a struct.");
    }

    fn visit_data_union(&mut self, _: &'ast syn::DataUnion) {
        panic!("lunther: #[derive(Lexer)] not valid on a union.");
    }

    fn visit_attribute(&mut self, i: &'ast syn::Attribute) {
        if !is_luther_path(&i.path) {
            return;
        }

        match i.interpret_meta() {
            None => panic!("luther: unrecognized form of luther attribute (interpret_meta)"),
            Some(m) => {
                let mut builder = LutherAttrBuilder::new();
                visit::visit_meta(&mut builder, &m);
                validate_luther_attr_for_enum(&builder);
                self.dfa_name = builder.dfa_name;
            }
        }
    }

    fn visit_variant(&mut self, i: &'ast syn::Variant) {
        let mut builder = VariantInfoBuilder::new(&i.ident);
        visit::visit_variant(&mut builder, i);

        if builder.regex.is_none() {
            return;
        }

        let info = VariantInfo {
            name: builder.name,
            regex: builder.regex.unwrap(),
            priority_group: builder
                .priority_group
                .map_or(0, |s| convert_priority_group(s)),
            field: builder.field,
        };

        self.variants.push(info);
    }
}

fn convert_priority_group(s: String) -> u32 {
    s.parse()
        .expect("luther: priority_group option on luther attribute must be an unsigned interger")
}

fn is_luther_path(path: &syn::Path) -> bool {
    !path.global() && path.segments.len() == 1 && if let Some(pair) = path.segments.first() {
        pair.value().ident == "luther"
    } else {
        false
    }
}

fn validate_luther_attr_for_enum(attr: &LutherAttrBuilder) {
    if attr.regex.is_some() {
        panic!("luther: regex option not valid on luther attribute for enum");
    }
    if attr.priority_group.is_some() {
        panic!("luther: priority_group option not valid on luther attribute for enum");
    }
}

fn validate_luther_attr_for_variant(attr: &LutherAttrBuilder) {
    if attr.dfa_name.is_some() {
        panic!("luther: dfa_name option not valid on luther attribute for variants");
    }
}

struct VariantInfoBuilder<'ast> {
    name: &'ast syn::Ident,
    regex: Option<String>,
    priority_group: Option<String>,
    field: Option<&'ast syn::Field>,
}

impl<'ast> VariantInfoBuilder<'ast> {
    fn new(name: &'ast syn::Ident) -> Self {
        VariantInfoBuilder {
            name,
            regex: None,
            priority_group: None,
            field: None,
        }
    }
}

impl<'ast> visit::Visit<'ast> for VariantInfoBuilder<'ast> {
    fn visit_attribute(&mut self, i: &'ast syn::Attribute) {
        if !is_luther_path(&i.path) {
            return;
        }

        match i.interpret_meta() {
            None => panic!("luther: unrecognized form of luther attribute (interpret_meta)"),
            Some(m) => {
                let mut builder = LutherAttrBuilder::new();
                visit::visit_meta(&mut builder, &m);
                validate_luther_attr_for_variant(&builder);
                self.regex = builder.regex;
                self.priority_group = builder.priority_group;
            }
        }
    }

    fn visit_fields_named(&mut self, _: &'ast syn::FieldsNamed) {
        panic!("luther: struct style enum variants not supported");
    }

    fn visit_field(&mut self, i: &'ast syn::Field) {
        if self.field.is_some() {
            panic!("luther: tuple style variants with more than one field not supported");
        }

        self.field = Some(i);
    }
}

struct LutherAttrBuilder {
    dfa_name: Option<String>,
    regex: Option<String>,
    priority_group: Option<String>,
    nested: bool,
}

impl LutherAttrBuilder {
    fn new() -> Self {
        LutherAttrBuilder {
            dfa_name: None,
            regex: None,
            priority_group: None,
            nested: false,
        }
    }
}

impl<'meta> visit::Visit<'meta> for LutherAttrBuilder {
    fn visit_meta_list(&mut self, meta: &'meta syn::MetaList) {
        if self.nested {
            panic!(
                "luther: unregcognized form of luther attribute (meta_list); {}",
                meta.ident
            );
        }

        if meta.ident == "luther" {
            visit::visit_meta_list(self, meta);
        }
    }

    fn visit_nested_meta(&mut self, meta: &'meta syn::NestedMeta) {
        if self.nested {
            panic!("luther: unregcognized form of luther attribute (nested_meta)");
        }

        self.nested = true;
        visit::visit_nested_meta(self, meta);
        self.nested = false;
    }

    fn visit_meta_name_value(&mut self, i: &'meta syn::MetaNameValue) {
        if !self.nested {
            panic!("luther: unrecognized form of luther attribute (meta_name_value)");
        }

        let mut option = LutherAttrOptionBuilder::new(i.ident.as_ref().into());
        visit::visit_lit(&mut option, &i.lit);

        match option.key {
            LutherAttrOption::Dfa => self.dfa_name = option.value,
            LutherAttrOption::Regex => self.regex = option.value,
            LutherAttrOption::PriorityGroup => self.priority_group = option.value,
        };
    }
}

#[derive(Debug)]
enum LutherAttrOption {
    Dfa,
    Regex,
    PriorityGroup,
}

impl<'a> From<&'a str> for LutherAttrOption {
    fn from(value: &'a str) -> Self {
        use self::LutherAttrOption::*;

        match value {
            "dfa" => Dfa,
            "regex" => Regex,
            "priority_group" => PriorityGroup,
            s => panic!("luther: {} is not a valid luther attribute option", s),
        }
    }
}

impl fmt::Display for LutherAttrOption {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use self::LutherAttrOption::*;

        let s = match self {
            &Dfa => "dfa",
            &Regex => "regex",
            &PriorityGroup => "priority_group",
        };

        f.write_str(s)
    }
}

struct LutherAttrOptionBuilder {
    key: LutherAttrOption,
    value: Option<String>,
}

impl LutherAttrOptionBuilder {
    fn new(key: LutherAttrOption) -> Self {
        LutherAttrOptionBuilder { key, value: None }
    }
}

impl<'meta> visit::Visit<'meta> for LutherAttrOptionBuilder {
    fn visit_lit_str(&mut self, lit: &'meta syn::LitStr) {
        self.value = Some(lit.value());
    }

    fn visit_lit_bool(&mut self, lit: &'meta syn::LitBool) {
        panic!(
            "luther: {} is not a valid value for luther attrubute option {}",
            lit.value, self.key
        );
    }

    fn visit_lit_byte(&mut self, lit: &'meta syn::LitByte) {
        panic!(
            "luther: {} is not a valid value for luther attrubute option {}",
            lit.value(),
            self.key
        );
    }

    fn visit_lit_byte_str(&mut self, _: &'meta syn::LitByteStr) {
        panic!(
            "luther: a byte string is not a valid value for luther attrubute option {}",
            self.key
        );
    }

    fn visit_lit_char(&mut self, lit: &'meta syn::LitChar) {
        panic!(
            "luther: {} is not a valid value for luther attrubute option {}",
            lit.value(),
            self.key
        );
    }

    fn visit_lit_float(&mut self, lit: &'meta syn::LitFloat) {
        panic!(
            "luther: {} is not a valid value for luther attrubute option {}",
            lit.value(),
            self.key
        );
    }

    fn visit_lit_int(&mut self, lit: &'meta syn::LitInt) {
        panic!(
            "luther: {} is not a valid value for luther attrubute option {}",
            lit.value(),
            self.key
        );
    }

    fn visit_lit_verbatim(&mut self, lit: &'meta syn::LitVerbatim) {
        panic!(
            "luther: {} is not a valid value for luther attrubute option {}",
            lit.token, self.key
        );
    }
}
