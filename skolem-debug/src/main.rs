use anyhow::Result;
use app::*;
use skolem::sat::cdcl::Snapshot;

mod app;

fn main() -> Result<()> {
    let history = include_str!("../../workspace/sat.json");
    let history: Vec<Snapshot> = serde_json::from_str(history)?;
    yew::Renderer::<App>::with_props(History { history }).render();
    Ok(())
}
