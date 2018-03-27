// Copyright 2018 Sergey Sherkunov <leinlawun@leinlawun.org>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(plugin_registrar, rustc_private, box_syntax)]

extern crate rustc_plugin;
extern crate syntax;
extern crate syntax_pos;

use rustc_plugin::Registry;
use syntax::ast::{
    AngleBracketedParameterData, Attribute, Block, ExprKind, FunctionRetTy,
    ImplItem, ImplItemKind, Item, ItemKind, MetaItem, MethodSig, Mod,
    ParenthesizedParameterData, PatKind, Path, PathParameters, PathSegment,
    SpannedIdent, StructField, Ty, TyKind, VariantData, Visibility,
    VisibilityKind, DUMMY_NODE_ID,
};
use syntax::ext::base::{Annotatable, ExtCtxt, SyntaxExtension};
use syntax::ext::build::AstBuilder;
use syntax::ext::quote::rt::Span;
use syntax::ptr::P;
use syntax::symbol::Symbol;
use syntax_pos::DUMMY_SP;
use syntax_pos::symbol::Ident;

fn sig_mod(
    cx: &mut ExtCtxt,
    visited: &[&Mod],
    injects: &mut [Vec<(P<Ty>, Vec<StructField>)>],
    item: &Mod,
) -> Mod
{
    let new_visited = [visited, &[&item]].concat();
    let visited_ref = new_visited.as_slice();
    let mut new_injects = [injects, &mut [vec![]]].concat();
    let injects_ref = new_injects.as_mut();
    let module = Mod {
        inner: item.inner,
        items: item.items
            .iter()
            .map(|item| sig_item(cx, visited_ref, injects_ref, item))
            .collect(),
    };

    injects_ref[injects_ref.len() - 1]
        .iter()
        .fold(module, |module, inject| {
            if let TyKind::Path(_, ref path) = inject.0.node {
                module
                    .items
                    .iter()
                    .enumerate()
                    .find(|&(_, item)| {
                        path == &Path::from_ident(path.span, item.ident)
                    })
            } else {
                cx.span_err(
                    inject.0.span,
                    "The structure for which the signals are implemented is \
                     not found in the current module. Please define the \
                     structure in the same location as the implementation. \
                     Perhaps in the future, this restriction will be removed.",
                );

                None
            }.map(|(number, item)| {
                (
                    number,
                    match item.node {
                        ItemKind::Struct(ref content, ref generics) => {
                            ItemKind::Struct(
                                match content {
                                    &VariantData::Struct(
                                        ref fields,
                                        node_id,
                                    ) => {
                                        VariantData::Struct(
                                            [fields.clone(), inject.1.clone()]
                                                .concat(),
                                            node_id,
                                        )
                                    },
                                    &VariantData::Tuple(
                                        ref fields,
                                        node_id,
                                    ) => {
                                        VariantData::Tuple(
                                            [fields.clone(), inject.1.clone()]
                                                .concat(),
                                            node_id,
                                        )
                                    },
                                    content => {
                                        cx.span_err(
                                            item.span,
                                            "Only structures and tuple \
                                             structures are supported.",
                                        );

                                        content.clone()
                                    },
                                },
                                generics.clone(),
                            )
                        },
                        ref node => {
                            cx.span_err(
                                item.span,
                                "Only structures and tuple structures are \
                                 supported.",
                            );

                            node.clone()
                        },
                    },
                )
            })
                .map_or_else(
                    || module.clone(),
                    |(number, item_node)| {
                        let module = module.clone();
                        let mut items = module.items;
                        let item = items[number].clone();
                        let item = P(Item {
                            ident: item.ident,
                            attrs: item.attrs.clone(),
                            id: item.id,
                            node: item_node,
                            vis: item.vis.clone(),
                            span: item.span,
                            tokens: item.tokens.clone(),
                        });

                        items[number] = item;

                        Mod {
                            inner: module.inner,
                            items,
                        }
                    },
                )
        })
}

fn sig_method(
    cx: &mut ExtCtxt,
    injects: &mut [Vec<(P<Ty>, Vec<StructField>)>],
    ty: &P<Ty>,
    ident: Ident,
    attrs: &[Attribute],
    sig: &MethodSig,
    body: &P<Block>,
) -> (MethodSig, P<Block>)
{
    attrs
        .iter()
        .find(|attr| {
            attr.path ==
                Path::from_ident(attr.path.span, Ident::from_str("sig"))
        })
        .and_then(|_| sig.decl.inputs.get(0))
        .and_then(|arg| {
            if let PatKind::Ident(
                _,
                SpannedIdent {
                    node: Ident { name, .. },
                    ..
                },
                ..,
            ) = arg.pat.node
            {
                if name == Symbol::intern("self") {
                    Some(arg)
                } else {
                    cx.span_err(
                        arg.pat.span,
                        "Static methods are not supported.",
                    );

                    None
                }
            } else {
                cx.span_err(arg.pat.span, "Unexpected pattern.");

                None
            }
        })
        .and_then(|_| {
            match sig.decl.output {
                FunctionRetTy::Default(_) => Some(()),
                FunctionRetTy::Ty(ref ty) => {
                    cx.span_err(
                        ty.span,
                        "A signal can only return an empty value. Perhaps in \
                         the future, this restriction will be removed.",
                    );

                    None
                },
            }
        })
        .map_or_else(
            || (sig.clone(), body.clone()),
            |_| {
                injects[injects.len() - 1].push((
                ty.clone(),
                vec![
                    StructField {
                        span: DUMMY_SP,
                        ident: Some(ident),
                        vis: Visibility {
                            node: VisibilityKind::Public,
                            span: DUMMY_SP,
                        },
                        id: DUMMY_NODE_ID,
                        ty: cx.ty_path(Path {
                            span: DUMMY_SP,
                            segments: vec![
                                PathSegment {
                                    identifier: Ident::from_str("Vec"),
                                    span: DUMMY_SP,
                                    parameters: Some(P(
                                        PathParameters::AngleBracketed(
                                            AngleBracketedParameterData {
                                                span: DUMMY_SP,
                                                lifetimes: vec![],
                                                types: vec![cx.ty_path(Path {
                                                    span: DUMMY_SP,
                                                    segments: vec![
                                                        PathSegment {
                                                            identifier: Ident::from_str("Rc"),
                                                            span: DUMMY_SP,
                                                            parameters: Some(P(
                                                                PathParameters::AngleBracketed(
                                                                    AngleBracketedParameterData {
                                                                        span: DUMMY_SP,
                                                                        lifetimes: vec![],
                                                                        types: vec![cx.ty_path(Path {
                                                                            span: DUMMY_SP,
                                                                            segments: vec![
                                                                                PathSegment {
                                                                                    identifier: Ident::from_str("Fn"),
                                                                                    span: DUMMY_SP,
                                                                                    parameters: Some(P(
                                                                                        PathParameters::Parenthesized(
                                                                                            ParenthesizedParameterData {
                                                                                                span: DUMMY_SP,
                                                                                                inputs: sig.decl.inputs[1..].iter().map(|arg| {
                                                                                                    arg.ty.clone()
                                                                                                }).collect(),
                                                                                                output: None,
                                                                                            },
                                                                                        ),
                                                                                    )),
                                                                                }
                                                                            ],
                                                                        })],
                                                                        bindings: vec![],
                                                                    },
                                                                ),
                                                            )),
                                                        }
                                                    ],
                                                })],
                                                bindings: vec![],
                                            },
                                        ),
                                    )),
                                },
                            ],
                        }),
                        attrs: vec![],
                    },
                ],
            ));

                let mut stmts = body.stmts.clone();

                stmts.push(
                    cx.stmt_expr(
                        cx.expr(
                            DUMMY_SP,
                            ExprKind::ForLoop(
                                cx.pat_ident(DUMMY_SP, Ident::from_str("slot")),
                                cx.expr_method_call(
                                    DUMMY_SP,
                                    cx.expr_field_access(
                                        DUMMY_SP,
                                        cx.expr_self(DUMMY_SP),
                                        ident,
                                    ),
                                    Ident::from_str("iter"),
                                    vec![],
                                ),
                                cx.block_expr(
                                    cx.expr_call(
                                        DUMMY_SP,
                                        cx.expr_ident(
                                            DUMMY_SP,
                                            Ident::from_str("slot"),
                                        ),
                                        sig.decl.inputs[1..]
                                            .iter()
                                            .map(|arg| {
                                                if let PatKind::Ident(
                                                    _,
                                                    ident,
                                                    _,
                                                ) = arg.pat.node
                                                {
                                                    cx.expr_ident(
                                                        DUMMY_SP,
                                                        ident.node,
                                                    )
                                                } else {
                                                    cx.span_err(
                                                        arg.pat.span,
                                                        "Unexpected pattern.",
                                                    );

                                                    cx.expr_ident(
                                                        DUMMY_SP,
                                                        Ident::from_str(""),
                                                    )
                                                }
                                            })
                                            .collect(),
                                    ),
                                ),
                                None,
                            ),
                        ),
                    ),
                );

                (sig.clone(), cx.block(body.span, stmts))
            },
        )
}

fn sig_impl_item(
    cx: &mut ExtCtxt,
    injects: &mut [Vec<(P<Ty>, Vec<StructField>)>],
    ty: &P<Ty>,
    item: &ImplItem,
) -> ImplItem
{
    if let ImplItemKind::Method(ref method, ref body) = item.node {
        let (method, body) = sig_method(
            cx,
            injects,
            ty,
            item.ident,
            &item.attrs,
            method,
            body,
        );

        ImplItem {
            id: item.id,
            ident: item.ident,
            vis: item.vis.clone(),
            defaultness: item.defaultness,
            attrs: item.attrs.clone(),
            generics: item.generics.clone(),
            node: ImplItemKind::Method(method, body),
            span: item.span,
            tokens: item.tokens.clone(),
        }
    } else {
        let sig_find = item.attrs.iter().any(|attr| {
            attr.path ==
                Path::from_ident(attr.path.span, Ident::from_str("sig"))
        });

        if sig_find {
            cx.span_err(
                item.span,
                "Using sig attribute is only allowed for methods and crates",
            );
        }

        item.clone()
    }
}

fn sig_impl_items(
    cx: &mut ExtCtxt,
    injects: &mut [Vec<(P<Ty>, Vec<StructField>)>],
    ty: &P<Ty>,
    items: &[ImplItem],
) -> Vec<ImplItem>
{
    items
        .iter()
        .map(|item| sig_impl_item(cx, injects, ty, item))
        .collect()
}

fn sig_item(
    cx: &mut ExtCtxt,
    visited: &[&Mod],
    injects: &mut [Vec<(P<Ty>, Vec<StructField>)>],
    item: &P<Item>,
) -> P<Item>
{
    let sig_find = item.attrs.iter().any(|attr| {
        attr.path == Path::from_ident(attr.path.span, Ident::from_str("sig"))
    });

    if sig_find {
        cx.span_err(
            item.span,
            "Using sig attribute is only allowed for methods and crates.",
        );

        item.clone()
    } else {
        match item.node {
            ItemKind::Mod(ref module) => {
                P(Item {
                    ident: item.ident,
                    attrs: item.attrs.clone(),
                    id: item.id,
                    node: ItemKind::Mod(sig_mod(cx, visited, injects, module)),
                    vis: item.vis.clone(),
                    span: item.span,
                    tokens: item.tokens.clone(),
                })
            },
            ItemKind::Impl(
                unsafety,
                impl_polarity,
                defaultness,
                ref generics,
                ref trait_ref,
                ref ty,
                ref items,
            ) => {
                if visited.is_empty() {
                    cx.span_err(
                        item.span,
                        "Using sig attribute is only allowed for methods and \
                         crates.",
                    );

                    item.clone()
                } else {
                    P(Item {
                        ident: item.ident,
                        attrs: item.attrs.clone(),
                        id: item.id,
                        node: ItemKind::Impl(
                            unsafety,
                            impl_polarity,
                            defaultness,
                            generics.clone(),
                            trait_ref.clone(),
                            ty.clone(),
                            sig_impl_items(cx, injects, ty, items),
                        ),
                        vis: item.vis.clone(),
                        span: item.span,
                        tokens: item.tokens.clone(),
                    })
                }
            },
            _ => {
                if visited.is_empty() {
                    cx.span_err(
                        item.span,
                        "Using sig attribute is only allowed for methods and \
                         crates.",
                    );

                    item.clone()
                } else {
                    item.clone()
                }
            },
        }
    }
}

fn sig(
    cx: &mut ExtCtxt,
    _span: Span,
    _meta_item: &MetaItem,
    item: Annotatable,
) -> Vec<Annotatable>
{
    vec![
        match item {
            Annotatable::Item(item) => {
                Annotatable::Item(sig_item(cx, &[], &mut [], &item))
            },
            Annotatable::TraitItem(item) => Annotatable::TraitItem(item),
            Annotatable::ImplItem(item) => Annotatable::ImplItem(item),
        },
    ]
}

#[plugin_registrar]
pub fn plugin_registrar(registry: &mut Registry) {
    registry.register_syntax_extension(
        Symbol::intern("sig"),
        SyntaxExtension::MultiModifier(box sig),
    );
}
