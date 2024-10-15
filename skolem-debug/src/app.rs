use gloo::events::EventListener;
use itertools::Itertools;
use skolem::{sat::cdcl::*, types::Literal};
use wasm_bindgen::JsCast;
use yew::prelude::*;

#[hook]
pub fn use_key_event<F>(callback: F)
where
    F: Fn(KeyboardEvent) + 'static,
{
    use gloo::utils::window;

    #[derive(PartialEq, Clone)]
    struct EventDependents {
        event_type: &'static str,
        callback: Callback<KeyboardEvent>,
    }

    let deps = EventDependents {
        event_type: "keydown",
        callback: Callback::from(callback),
    };

    use_effect_with(deps, |deps| {
        let EventDependents {
            event_type,
            callback,
        } = deps.clone();
        let listner = EventListener::new(&window(), event_type, move |e| {
            if let Ok(e) = e.clone().dyn_into() {
                callback.emit(e);
            }
        });
        move || drop(listner)
    })
}

#[derive(Properties, PartialEq)]
pub struct History {
    pub history: Vec<Snapshot>,
}

#[derive(Properties, PartialEq)]
pub struct WebClause {
    clause: ClauseSnapshot,
}

#[derive(Properties, PartialEq)]
pub struct WebState {
    state: SnapshotState,
}

#[derive(Properties, PartialEq)]
pub struct WebLit {
    lit: ClauseSnapshotLit,
}

#[function_component]
pub fn Lit(WebLit { lit }: &WebLit) -> Html {
    use skolem::types::Literal::*;
    let mut clss = classes!("lit");
    if lit.watched {
        clss.push("watched");
    }
    match lit.state {
        None => {}
        Some(true) => clss.push("true"),
        Some(false) => clss.push("false"),
    }
    let lit_html = match lit.lit {
        Pos(v) => format!("{}", v.0),
        Neg(v) => format!("-{}", v.0),
    };
    html! {
        <span class={clss}>{lit_html}</span>
    }
}

#[function_component]
pub fn Clause(WebClause { clause }: &WebClause) -> Html {
    html! {
        <li>
            {"("} {for clause.lits.iter().cloned().map(|lit| html!{ <Lit ..WebLit{lit} /> })} {")"}
        </li>
    }
}

fn fmt_lit(l: &Literal) -> String {
    match l {
        Literal::Pos(v) => format!("{}", v.0),
        Literal::Neg(v) => format!("-{}", v.0),
    }
}

#[function_component]
pub fn State(WebState { state }: &WebState) -> Html {
    use SnapshotState::*;
    let state = match state {
        Idle => html! { {"Idle"} },
        Backjumping {
            conflicting,
            resolution,
        } => {
            html! { <> {"Backjumping: "} <span class="lit">{fmt_lit(conflicting)}</span> {": ("} {for resolution.iter().map(|l| html!{<span class="lit"> {fmt_lit(l)} </span>})} {")"}  </> }
        }
        Propagating {
            unit: l,
            reason,
            target,
            units_detected,
        } => {
            let reason = match reason {
                None => html! {},
                Some(clause) => {
                    html! { <> {" reason: "} <Clause ..WebClause{clause: clause.clone()} /> </> }
                }
            };
            let target = match target {
                None => html! {},
                Some(target) => {
                    html! { <> {" to target: "} <Clause ..WebClause{clause: target.clone()} /> </> }
                }
            };
            html! { <> {"Propagating: "} <span class="lit">{fmt_lit(l)}</span> {reason} {target} {"(remaining: units: "} {for units_detected.iter().map(|(l, _)| html!{<span class="lit">{fmt_lit(l)}</span>})} {")"} </>  }
        }
    };
    html! {
        <div class="state">{ "State: "} { state }</div>
    }
}

#[derive(Properties, PartialEq)]
pub struct Decs {
    pub decs: Vec<Vec<(Literal, Option<Vec<Literal>>)>>,
}

#[function_component]
pub fn Assignemt(Decs { decs }: &Decs) -> Html {
    html! {
        <>
        { for decs.iter().map(|seq| html!{
            <>
                {for seq.iter().map(|(l, reason)|  {
                    let reason = if let Some(reason) = reason {
                        format!("({})", reason.iter().map(|l| fmt_lit(l)).intersperse(", ".to_string()).collect::<String>())
                    } else {
                        "Dec Var".to_string()
                    };
                    let reason = html!{<span class="tooltip-text">{reason}</span>};
                    let clss = classes!("lit", "tooltip");
                    html!{<span class={clss}>{reason}{fmt_lit(l)}</span>}
                })}
            </>
        }).intersperse("|".into())}
        </>
    }
}

#[function_component(App)]
pub fn app(History { history }: &History) -> Html {
    let counter = use_state(|| 0);
    let size = history.len();
    let snapshot = {
        let history = history.clone();
        use_memo(counter.clone(), move |idx| history[**idx].clone())
    };

    let onclick = {
        let counter = counter.clone();
        move |_| {
            let value = (*counter + 1) % size;
            counter.set(value);
        }
    };
    {
        let counter = counter.clone();
        use_key_event(move |e| {
            if e.code() == "ArrowRight" {
                let value = (*counter + 1) % size;
                counter.set(value);
                e.stop_propagation();
            } else if e.code() == "ArrowLeft" {
                let value = (*counter + size - 1) % size;
                counter.set(value);
                e.stop_propagation();
            }
        });
    }

    html! {
        <div>
            <main>
                <ul>
                    { for snapshot.clauses.iter().cloned().map(|clause| html!{ <Clause  ..WebClause{clause} />})}
                </ul>
                <State .. WebState{state: (*snapshot).clone().state} />
                <Assignemt .. Decs{decs: (*snapshot).clone().decisions} />
            </main>
            <footer>
                <p>
                    <button {onclick}>{ "+1" }</button>
                    <span>{ *counter } { " / " } { size }</span>
                </p>
            </footer>
        </div>
    }
}
