use gloo::events::EventListener;
use skolem::sat::cdcl::*;
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

#[function_component(App)]
pub fn app(History { history }: &History) -> Html {
    let counter = use_state(|| 0);
    let size = history.len();

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
        <>
            <main>
                <ul>
                    { for history[*counter].clauses.iter().cloned().map(|clause| html!{ <Clause  ..WebClause{clause} />})}
                </ul>
            </main>
            <div class="hooter">
                <button {onclick}>{ "+1" }</button>
                <span>{ *counter } { " / " } { size }</span>
            </div>
        </>
    }
}
