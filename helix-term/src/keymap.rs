pub mod default;
pub mod macros;

pub use crate::commands::MappableCommand;
use arc_swap::{
    access::{DynAccess, DynGuard},
    ArcSwap,
};
use chrono::{DateTime, Local};
use helix_core::unicode::segmentation::UnicodeSegmentation;
use helix_view::{
    document::Mode,
    info::Info,
    input::{KeyEvent, MouseButton, MouseEvent, MouseEventKind, MouseModifiers},
    keyboard::KeyModifiers,
};
use serde::Deserialize;
use std::{
    borrow::Cow,
    collections::{BTreeSet, HashMap},
    fmt::Display,
    hash::Hash,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    sync::Arc,
    time::Duration,
};

pub use default::{default, default_mouse};
use macros::key;

pub type ReverseInputmap<IE> = HashMap<String, Vec<Vec<IE>>>;
pub trait InputEvent:
    Eq
    + PartialEq
    + Ord
    + PartialOrd
    + Hash
    + Display
    + std::fmt::Debug
    + Copy
    + Ord
    + Default
    + Send
    + Sync
{
    fn check_before_get(&self, inputmaps: &mut Keymaps<Self>) -> InputmapResult<Self>;
    /// Format the key in such a way that a concatenated sequence
    /// of keys can be read easily.
    ///
    /// ```
    /// # use std::str::FromStr;
    /// # use helix_view::input::KeyEvent;
    /// # use helix_term::keymap::InputEventTrait;
    ///
    /// let k = KeyEvent::from_str("w").unwrap().key_sequence_format();
    /// assert_eq!(k, "w");
    ///
    /// let k = KeyEvent::from_str("C-w").unwrap().key_sequence_format();
    /// assert_eq!(k, "<C-w>");
    ///
    /// let k = KeyEvent::from_str(" ").unwrap().key_sequence_format();
    /// assert_eq!(k, "<space>");
    /// ```
    fn key_sequence_format(&self) -> String {
        let s = self.to_string();
        if s.graphemes(true).count() > 1 {
            format!("<{}>", s)
        } else {
            s
        }
    }
}
impl InputEvent for MouseEvent {
    fn check_before_get(&self, _: &mut Keymaps<Self>) -> InputmapResult<Self> {
        InputmapResult::NotFound
    }
}

impl InputEvent for KeyEvent {
    fn check_before_get(&self, inputmaps: &mut Keymaps<Self>) -> InputmapResult<Self> {
        if key!(Esc) == *self {
            if !inputmaps.pending().is_empty() {
                // Note that Esc is not included here
                return InputmapResult::Cancelled(inputmaps.pending_mut().drain(..).collect());
            }
            inputmaps.insert_sticky(None);
        }
        InputmapResult::NotFound
    }
}

#[derive(Debug)]
pub enum InputTrieCheckError {
    DoubleSequenceClick {
        parent_event: MouseEvent,
        child_event: MouseEvent,
    },
    ForbiddenMouseEvent {
        event: MouseEvent,
    },
}

impl std::fmt::Display for InputTrieCheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            InputTrieCheckError::DoubleSequenceClick {
                parent_event,
                child_event,
            } => f.write_fmt(format_args!(
                "You cannot put {} inside {}",
                child_event, parent_event,
            )),
            InputTrieCheckError::ForbiddenMouseEvent { event } => {
                f.write_fmt(format_args!("You cannot set a keymapping to {}", event))
            }
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum InputTrie<IE>
where
    IE: InputEvent + 'static,
{
    MappableCommand(MappableCommand<IE>),
    Sequence(Vec<MappableCommand<IE>>),
    Node(InputTrieNode<IE>),
}

impl<IE> InputTrie<IE>
where
    IE: InputEvent,
{
    pub fn reverse_map(&self) -> ReverseInputmap<IE> {
        let mut res = HashMap::new();
        self.map_node(&mut res, &mut Vec::new());
        res
    }
    /// recursively visit all nodes in keymap
    pub fn map_node(&self, cmd_map: &mut ReverseInputmap<IE>, keys: &mut Vec<IE>) {
        match self {
            InputTrie::MappableCommand(cmd) => {
                let name = cmd.name();
                if name != "no_op" {
                    cmd_map.entry(name.into()).or_default().push(keys.clone())
                }
            }
            InputTrie::Node(next) => {
                for (key, trie) in &next.map {
                    keys.push(*key);
                    trie.map_node(cmd_map, keys);
                    keys.pop();
                }
            }
            InputTrie::Sequence(_) => {}
        };
    }

    pub fn node(&self) -> Option<&InputTrieNode<IE>> {
        match *self {
            InputTrie::Node(ref node) => Some(node),
            InputTrie::MappableCommand(_) | InputTrie::Sequence(_) => None,
        }
    }

    pub fn node_mut(&mut self) -> Option<&mut InputTrieNode<IE>> {
        match *self {
            InputTrie::Node(ref mut node) => Some(node),
            InputTrie::MappableCommand(_) | InputTrie::Sequence(_) => None,
        }
    }

    /// Merge another InputTrie in, assuming that this InputTrie and the other
    /// are both Nodes. Panics otherwise.
    pub fn merge_nodes(&mut self, mut other: Self) {
        let node = std::mem::take(other.node_mut().unwrap());
        self.node_mut().unwrap().merge(node);
    }

    pub fn search(&self, keys: &[IE]) -> Option<&InputTrie<IE>> {
        let mut trie = self;
        for key in keys {
            trie = match trie {
                InputTrie::Node(map) => map.get(key),
                // leaf encountered while keys left to process
                InputTrie::MappableCommand(_) | InputTrie::Sequence(_) => None,
            }?
        }
        Some(trie)
    }
}

impl InputTrie<MouseEvent> {
    pub fn verify(&self) -> Result<(), InputTrieCheckError> {
        let mut res: Result<(), InputTrieCheckError> = Ok(());
        self.verify_recur(None, &mut res);
        res?;

        // check that 1-left is not a single or Sequences of MappableCommand
        res = match *self {
            InputTrie::Node(ref n) => {
                let forbidden_events = [MouseEvent {
                    kind: MouseEventKind::Down(MouseButton::Left),
                    column: 0,
                    row: 0,
                    modifiers: KeyModifiers::NONE,
                    mouse_modifiers: MouseModifiers::MultipleClick(1),
                }];
                for (event, node) in n.map.iter() {
                    match node {
                        InputTrie::Sequence(_) | InputTrie::MappableCommand(_) => {
                            if forbidden_events.contains(event) {
                                return Err(InputTrieCheckError::ForbiddenMouseEvent {
                                    event: event.clone_without_coords(),
                                });
                            }
                        }
                        InputTrie::Node(_) => (),
                    }
                }
                Ok(())
            }
            _ => Ok(()),
        };
        res?;
        return Ok(());
    }

    /// verify that there is no parent and children of the same button, example:
    /// 1-left = { 1-left = "goto_line_end", 1-right = "goto_last_line"} => this is not valid
    fn verify_recur(
        &self,
        parent_event: Option<&MouseEvent>,
        res: &mut Result<(), InputTrieCheckError>,
    ) {
        match *self {
            InputTrie::MappableCommand(_) => (),
            InputTrie::Sequence(_) => (),
            InputTrie::Node(ref n) => {
                for (event, trie) in n.map.iter() {
                    if let Some(parent) = parent_event {
                        if event.light_eq(parent) {
                            *res = Err(InputTrieCheckError::DoubleSequenceClick {
                                parent_event: parent.to_owned(),
                                child_event: event.to_owned(),
                            });
                            return;
                        }
                    }

                    trie.verify_recur(Some(&event), res);
                    if res.is_err() {
                        return;
                    }
                }
            }
        }
    }
}

impl<'de, IE> Deserialize<'de> for InputTrie<IE>
where
    IE: InputEvent + Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_any(InputTrieVisitor::<IE> {
            phantom: PhantomData,
        })
    }
}

struct InputTrieVisitor<IE>
where
    IE: InputEvent,
{
    phantom: PhantomData<IE>,
}

impl<'de, IE> Deserialize<'de> for InputTrieNode<IE>
where
    IE: InputEvent + Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let map = HashMap::<IE, InputTrie<IE>>::deserialize(deserializer)?;
        let order = map.keys().copied().collect::<Vec<_>>(); // NOTE: map.keys() has arbitrary order
        Ok(Self {
            map,
            order,
            ..Default::default()
        })
    }
}

impl<'de, IE> serde::de::Visitor<'de> for InputTrieVisitor<IE>
where
    IE: InputEvent + Deserialize<'de> + 'static,
{
    type Value = InputTrie<IE>;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(formatter, "a command, list of commands, or sub-keymap")
    }

    fn visit_str<E>(self, command: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        command
            .parse::<MappableCommand<IE>>()
            .map(InputTrie::MappableCommand)
            .map_err(E::custom)
    }

    fn visit_seq<S>(self, mut seq: S) -> Result<Self::Value, S::Error>
    where
        S: serde::de::SeqAccess<'de>,
    {
        let mut commands = Vec::new();
        while let Some(command) = seq.next_element::<String>()? {
            commands.push(
                command
                    .parse::<MappableCommand<IE>>()
                    .map_err(serde::de::Error::custom)?,
            )
        }
        Ok(InputTrie::Sequence(commands))
    }

    fn visit_map<M>(self, mut map: M) -> Result<Self::Value, M::Error>
    where
        M: serde::de::MapAccess<'de>,
    {
        let mut mapping = HashMap::new();
        let mut order = Vec::new();
        while let Some((key, value)) = map.next_entry::<IE, InputTrie<IE>>()? {
            mapping.insert(key, value);
            order.push(key);
        }
        Ok(InputTrie::Node(InputTrieNode::new("", mapping, order)))
    }
}

#[derive(Default, Clone, Debug)]
pub struct InputTrieNode<IE>
where
    IE: InputEvent + 'static,
{
    /// A label for keys coming under this node, like "Goto mode"
    name: String,
    map: HashMap<IE, InputTrie<IE>>,
    order: Vec<IE>,
    pub is_sticky: bool,
}

impl<IE> InputTrieNode<IE>
where
    IE: InputEvent,
{
    pub fn new(name: &str, map: HashMap<IE, InputTrie<IE>>, order: Vec<IE>) -> Self {
        Self {
            name: name.to_owned(),
            map,
            order,
            is_sticky: false,
        }
    }
    /// Merge another Node in. Leaves and subnodes from the other node replace
    /// corresponding keyevent in self, except when both other and self have
    /// subnodes for same key. In that case the merge is recursive.
    pub fn merge(&mut self, mut other: Self) {
        for (key, trie) in std::mem::take(&mut other.map) {
            if let Some(InputTrie::Node(node)) = self.map.get_mut(&key) {
                if let InputTrie::Node(other_node) = trie {
                    node.merge(other_node);
                    continue;
                }
            }
            self.map.insert(key, trie);
        }
        for &key in self.map.keys() {
            if !self.order.contains(&key) {
                self.order.push(key.to_owned());
            }
        }
    }

    pub fn infobox(&self) -> Info {
        let mut body: Vec<(BTreeSet<IE>, &str)> = Vec::with_capacity(self.len());
        for (&key, trie) in self.iter() {
            let desc = match trie {
                InputTrie::MappableCommand(cmd) => {
                    if cmd.name() == "no_op" {
                        continue;
                    }
                    cmd.doc()
                }
                InputTrie::Node(n) => &n.name,
                InputTrie::Sequence(_) => "[Multiple commands]",
            };
            match body.iter().position(|(_, d)| d == &desc) {
                Some(pos) => {
                    body[pos].0.insert(key);
                }
                None => body.push((BTreeSet::from([key]), desc)),
            }
        }
        body.sort_unstable_by_key(|(keys, _)| {
            self.order
                .iter()
                .position(|&k| k == *keys.iter().next().unwrap())
                .unwrap()
        });

        let body: Vec<_> = body
            .into_iter()
            .map(|(events, desc)| {
                let events = events.iter().map(ToString::to_string).collect::<Vec<_>>();
                (events.join(", "), desc)
            })
            .collect();
        Info::new(&self.name, &body)
    }
}
impl<IE> PartialEq for InputTrieNode<IE>
where
    IE: InputEvent,
{
    fn eq(&self, other: &InputTrieNode<IE>) -> bool {
        self.map == other.map
    }
}

impl<IE> Deref for InputTrieNode<IE>
where
    IE: InputEvent,
{
    type Target = HashMap<IE, InputTrie<IE>>;

    fn deref(&self) -> &Self::Target {
        &self.map
    }
}

impl<IE> DerefMut for InputTrieNode<IE>
where
    IE: InputEvent,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum InputmapResult<IE>
where
    IE: InputEvent + 'static,
{
    /// Needs more keys to execute a command. Contains valid keys for next keystroke.
    Pending(InputTrieNode<IE>),
    Matched(MappableCommand<IE>),
    /// Matched a sequence of commands to execute.
    MatchedSequence(Vec<MappableCommand<IE>>),
    /// Key was not found in the root keymap
    NotFound,
    /// Key is invalid in combination with previous keys. Contains keys leading upto
    /// and including current (invalid) key.
    Cancelled(Vec<IE>),
}

/// A map of command names to keybinds that will execute the command.

pub struct Keymaps<IE>
where
    IE: InputEvent + 'static,
{
    pub map: Box<dyn DynAccess<HashMap<Mode, InputTrie<IE>>>>,
    /// Stores pending keys waiting for the next key. This is relative to a
    /// sticky node if one is in use.
    state: Vec<IE>,
    /// Stores the sticky node if one is activated.
    pub sticky: Option<InputTrieNode<IE>>,
    last_time_mouse_pressed: DateTime<Local>,
}

impl Default for Keymaps<KeyEvent> {
    fn default() -> Self {
        Self::new(Box::new(ArcSwap::new(Arc::new(default()))))
    }
}

impl Default for Keymaps<MouseEvent> {
    fn default() -> Self {
        Self::new(Box::new(ArcSwap::new(Arc::new(default_mouse()))))
    }
}

impl<IE> Keymaps<IE>
where
    IE: InputEvent + 'static,
{
    pub fn new(map: Box<dyn DynAccess<HashMap<Mode, InputTrie<IE>>>>) -> Self {
        Self {
            map,
            state: Vec::new(),
            sticky: None,
            last_time_mouse_pressed: Local::now(),
        }
    }

    pub fn map(&self) -> DynGuard<HashMap<Mode, InputTrie<IE>>> {
        self.map.load()
    }

    /// Returns list of keys waiting to be disambiguated in current mode.
    pub fn pending(&self) -> &[IE] {
        &self.state
    }

    pub fn pending_mut(&mut self) -> &mut Vec<IE> {
        &mut self.state
    }

    pub fn sticky(&self) -> Option<&InputTrieNode<IE>> {
        self.sticky.as_ref()
    }

    pub fn insert_sticky(&mut self, node: Option<InputTrieNode<IE>>) {
        self.sticky = node;
    }
}

impl Keymaps<MouseEvent> {
    fn search_key(
        &self,
        values: &InputTrie<MouseEvent>,
        first: &MouseEvent,
    ) -> InputmapResult<MouseEvent> {
        let trie = match values.search(&[*first]) {
            Some(InputTrie::MappableCommand(ref cmd)) => {
                return InputmapResult::Matched(cmd.clone());
            }
            Some(InputTrie::Sequence(ref cmds)) => {
                return InputmapResult::MatchedSequence(cmds.clone());
            }
            None => {
                return InputmapResult::NotFound;
            }
            Some(t) => t,
        };
        return match trie.search(&self.state[1..]) {
            Some(InputTrie::Node(map)) => InputmapResult::Pending(map.clone()),
            Some(InputTrie::MappableCommand(cmd)) => InputmapResult::Matched(cmd.clone()),
            Some(InputTrie::Sequence(cmds)) => InputmapResult::MatchedSequence(cmds.clone()),
            None => InputmapResult::Cancelled(vec![]),
        };
    }
    pub fn get(
        &mut self,
        mode: Mode,
        key: MouseEvent,
        mouse_idle: &Duration,
    ) -> InputmapResult<MouseEvent> {
        let keymaps = &*self.map();

        if let Some(values) = keymaps.get(&mode) {
            match key.kind {
                MouseEventKind::Down(_) => {
                    let current_date = Local::now();
                    let diff = current_date - self.last_time_mouse_pressed;
                    self.last_time_mouse_pressed = current_date;
                    let mut push_key = true;
                    if diff.num_milliseconds() as u128 > mouse_idle.as_millis() {
                        self.state.clear();
                    } else if let Some(last_mouse_event) = self.state.last_mut() {
                        // same modifiers (not mouse_mofifiers) and buttons (columns are excepted)
                        if last_mouse_event.light_eq(&key) {
                            last_mouse_event.mouse_modifiers =
                                match last_mouse_event.mouse_modifiers {
                                    MouseModifiers::MultipleClick(v) => {
                                        MouseModifiers::MultipleClick(v + 1)
                                    }
                                };
                            push_key = false;
                        }
                    }

                    if push_key {
                        self.state.push(key.clone_without_coords());
                    }
                    let res = self.search_key(values, self.state.get(0).unwrap_or(&key));
                    return res;
                }
                MouseEventKind::ScrollDown | MouseEventKind::ScrollUp => {
                    self.state.clear();
                    let res = self.search_key(values, &key.clone_without_coords());
                    return res;
                }
                _ => (),
            }
        }
        return InputmapResult::NotFound;
    }
}

impl Keymaps<KeyEvent> {
    /// Lookup `key` in the keymap to try and find a command to execute. Escape
    /// key cancels pending keystrokes. If there are no pending keystrokes but a
    /// sticky node is in use, it will be cleared.
    pub fn get(&mut self, mode: Mode, key: KeyEvent) -> InputmapResult<KeyEvent> {
        // TODO: remove the sticky part and look up manually
        let keymaps = &*self.map();
        let keymap = &keymaps[&mode];

        let res = key.check_before_get(self);
        match res {
            InputmapResult::NotFound => (),
            _ => return res,
        }

        let first = self.state.get(0).unwrap_or(&key);
        let trie_node = match self.sticky {
            Some(ref trie) => Cow::Owned(InputTrie::Node(trie.clone())),
            None => Cow::Borrowed(keymap),
        };

        let trie = match trie_node.search(&[*first]) {
            Some(InputTrie::MappableCommand(ref cmd)) => {
                return InputmapResult::Matched(cmd.clone());
            }
            Some(InputTrie::Sequence(ref cmds)) => {
                return InputmapResult::MatchedSequence(cmds.clone());
            }
            None => return InputmapResult::NotFound,
            Some(t) => t,
        };

        self.state.push(key);
        match trie.search(&self.state[1..]) {
            Some(InputTrie::Node(map)) => {
                if map.is_sticky {
                    self.state.clear();
                    self.sticky = Some(map.clone());
                }
                InputmapResult::Pending(map.clone())
            }
            Some(InputTrie::MappableCommand(cmd)) => {
                self.state.clear();
                InputmapResult::Matched(cmd.clone())
            }
            Some(InputTrie::Sequence(cmds)) => {
                self.state.clear();
                InputmapResult::MatchedSequence(cmds.clone())
            }
            None => InputmapResult::Cancelled(self.state.drain(..).collect()),
        }
    }
}

// Merge default config keys with user overwritten keys for custom user config.
pub fn merge_inputs<IE>(
    dst: &mut HashMap<Mode, InputTrie<IE>>,
    mut delta: HashMap<Mode, InputTrie<IE>>,
) where
    IE: InputEvent,
{
    for (mode, keys) in dst {
        keys.merge_nodes(
            delta
                .remove(mode)
                .unwrap_or_else(|| InputTrie::Node(InputTrieNode::default())),
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::keymap;

    use super::*;
    use arc_swap::access::Constant;
    use helix_core::hashmap;

    #[test]
    #[should_panic]
    fn duplicate_keys_should_panic() {
        let _: InputTrie<KeyEvent> = keymap!({ "Normal mode"
            "i" => normal_mode,
            "i" => goto_definition,
        });
    }

    #[test]
    #[should_panic]
    fn duplicate_mouses_should_panic() {
        let _: InputTrie<MouseEvent> = keymap!({ "Normal mode"
            "2-left" => normal_mode,
            "2-left" => goto_definition,
        });
    }

    #[test]
    fn check_duplicate_keys_in_default_keymap() {
        // will panic on duplicate keys, assumes that `Keymaps` uses keymap! macro
        Keymaps::<KeyEvent>::default();
    }

    #[test]
    fn check_duplicate_mouses_in_default_mousemap() {
        Keymaps::<MouseEvent>::default();
    }

    #[test]
    fn merge_partial_keys() {
        let keymap = hashmap! {
            Mode::Normal => keymap!({ "Normal mode"
                "i" => normal_mode,
                "无" => insert_mode,
                "z" => jump_backward,
                "g" => { "Merge into goto mode"
                    "$" => goto_line_end,
                    "g" => delete_char_forward,
                },
            })
        };
        let mut merged_keyamp = default();
        merge_inputs(&mut merged_keyamp, keymap.clone());
        assert_ne!(keymap, merged_keyamp);

        let mut keymap = Keymaps::new(Box::new(Constant(merged_keyamp.clone())));
        assert_eq!(
            keymap.get(Mode::Normal, key!('i')),
            InputmapResult::Matched(MappableCommand::normal_mode),
            "Leaf should replace leaf"
        );
        assert_eq!(
            keymap.get(Mode::Normal, key!('无')),
            InputmapResult::Matched(MappableCommand::insert_mode),
            "New leaf should be present in merged keymap"
        );
        // Assumes that z is a node in the default keymap
        assert_eq!(
            keymap.get(Mode::Normal, key!('z')),
            InputmapResult::Matched(MappableCommand::jump_backward),
            "Leaf should replace node"
        );

        let keymap = merged_keyamp.get_mut(&Mode::Normal).unwrap();
        // Assumes that `g` is a node in default keymap
        assert_eq!(
            keymap.search(&[key!('g'), key!('$')]).unwrap(),
            &InputTrie::MappableCommand(MappableCommand::goto_line_end),
            "Leaf should be present in merged subnode"
        );
        // Assumes that `gg` is in default keymap
        assert_eq!(
            keymap.search(&[key!('g'), key!('g')]).unwrap(),
            &InputTrie::MappableCommand(MappableCommand::delete_char_forward),
            "Leaf should replace old leaf in merged subnode"
        );
        // Assumes that `ge` is in default keymap
        assert_eq!(
            keymap.search(&[key!('g'), key!('e')]).unwrap(),
            &InputTrie::MappableCommand(MappableCommand::goto_last_line),
            "Old leaves in subnode should be present in merged node"
        );

        assert!(
            merged_keyamp
                .get(&Mode::Normal)
                .and_then(|key_trie| key_trie.node())
                .unwrap()
                .len()
                > 1
        );
        assert!(
            merged_keyamp
                .get(&Mode::Insert)
                .and_then(|key_trie| key_trie.node())
                .unwrap()
                .len()
                > 0
        );
    }

    #[test]
    fn order_should_be_set() {
        let keymap = hashmap! {
            Mode::Normal => keymap!({ "Normal mode"
                "space" => { ""
                    "s" => { ""
                        "v" => vsplit,
                        "c" => hsplit,
                    },
                },
            })
        };
        let mut merged_keyamp = default();
        merge_inputs(&mut merged_keyamp, keymap.clone());
        assert_ne!(keymap, merged_keyamp);
        let keymap = merged_keyamp.get_mut(&Mode::Normal).unwrap();
        // Make sure mapping works
        assert_eq!(
            keymap.search(&[key!(' '), key!('s'), key!('v')]).unwrap(),
            &InputTrie::<KeyEvent>::MappableCommand(MappableCommand::vsplit),
            "Leaf should be present in merged subnode"
        );
        // Make sure an order was set during merge
        let node = keymap.search(&[crate::key!(' ')]).unwrap();
        assert!(!node.node().unwrap().order.as_slice().is_empty())
    }

    #[test]
    fn aliased_modes_are_same_in_default_keymap() {
        let keymaps = Keymaps::default().map();
        let root = keymaps.get(&Mode::Normal).unwrap();
        assert_eq!(
            root.search(&[key!(' '), key!('w')]).unwrap(),
            root.search(&["C-w".parse::<KeyEvent>().unwrap()]).unwrap(),
            "Mismatch for window mode on `Space-w` and `Ctrl-w`"
        );
        assert_eq!(
            root.search(&[key!('z')]).unwrap(),
            root.search(&[key!('Z')]).unwrap(),
            "Mismatch for view mode on `z` and `Z`"
        );
    }

    #[test]
    fn reverse_map() {
        let normal_mode = keymap!({ "Normal mode"
            "i" => insert_mode,
            "g" => { "Goto"
                "g" => goto_file_start,
                "e" => goto_file_end,
            },
            "j" | "k" => move_line_down,
        });
        let keymap = normal_mode;
        let mut reverse_map = keymap.reverse_map();

        // sort keybindings in order to have consistent tests
        // HashMaps can be compared but we can still get different ordering of bindings
        // for commands that have multiple bindings assigned
        for v in reverse_map.values_mut() {
            v.sort()
        }

        assert_eq!(
            reverse_map,
            HashMap::from([
                ("insert_mode".to_string(), vec![vec![key!('i')]]),
                (
                    "goto_file_start".to_string(),
                    vec![vec![key!('g'), key!('g')]]
                ),
                (
                    "goto_file_end".to_string(),
                    vec![vec![key!('g'), key!('e')]]
                ),
                (
                    "move_line_down".to_string(),
                    vec![vec![key!('j')], vec![key!('k')]]
                ),
            ]),
            "Mismatch"
        )
    }

    #[test]
    fn escaped_keymap() {
        use crate::commands::MappableCommand;
        use helix_view::input::{KeyCode, KeyEvent, KeyModifiers};

        let keys = r#"
"+" = [
    "select_all",
    ":pipe sed -E 's/\\s+$//g'",
]
        "#;

        let key = KeyEvent {
            code: KeyCode::Char('+'),
            modifiers: KeyModifiers::NONE,
        };

        let expectation = InputTrie::<KeyEvent>::Node(InputTrieNode::<KeyEvent>::new(
            "",
            hashmap! {
                key => InputTrie::<KeyEvent>::Sequence(vec!{
                    MappableCommand::select_all,
                    MappableCommand::Typable {
                        name: "pipe".to_string(),
                        args: vec!{
                            "sed".to_string(),
                            "-E".to_string(),
                            "'s/\\s+$//g'".to_string()
                        },
                        doc: "".to_string(),
                    },
                })
            },
            vec![key],
        ));

        assert_eq!(toml::from_str(keys), Ok(expectation));
    }
}
