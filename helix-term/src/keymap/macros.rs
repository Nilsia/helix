#[macro_export]
macro_rules! key {
    ($key:ident) => {
        ::helix_view::input::KeyEvent {
            code: ::helix_view::keyboard::KeyCode::$key,
            modifiers: ::helix_view::keyboard::KeyModifiers::NONE,
        }
    };
    ($($ch:tt)*) => {
        ::helix_view::input::KeyEvent {
            code: ::helix_view::keyboard::KeyCode::Char($($ch)*),
            modifiers: ::helix_view::keyboard::KeyModifiers::NONE,
        }
    };
}

#[macro_export]
macro_rules! shift {
    ($key:ident) => {
        ::helix_view::input::KeyEvent {
            code: ::helix_view::keyboard::KeyCode::$key,
            modifiers: ::helix_view::keyboard::KeyModifiers::SHIFT,
        }
    };
    ($($ch:tt)*) => {
        ::helix_view::input::KeyEvent {
            code: ::helix_view::keyboard::KeyCode::Char($($ch)*),
            modifiers: ::helix_view::keyboard::KeyModifiers::SHIFT,
        }
    };
}

#[macro_export]
macro_rules! ctrl {
    ($key:ident) => {
        ::helix_view::input::KeyEvent {
            code: ::helix_view::keyboard::KeyCode::$key,
            modifiers: ::helix_view::keyboard::KeyModifiers::CONTROL,
        }
    };
    ($($ch:tt)*) => {
        ::helix_view::input::KeyEvent {
            code: ::helix_view::keyboard::KeyCode::Char($($ch)*),
            modifiers: ::helix_view::keyboard::KeyModifiers::CONTROL,
        }
    };
}

#[macro_export]
macro_rules! alt {
    ($key:ident) => {
        ::helix_view::input::KeyEvent {
            code: ::helix_view::keyboard::KeyCode::$key,
            modifiers: ::helix_view::keyboard::KeyModifiers::ALT,
        }
    };
    ($($ch:tt)*) => {
        ::helix_view::input::KeyEvent {
            code: ::helix_view::keyboard::KeyCode::Char($($ch)*),
            modifiers: ::helix_view::keyboard::KeyModifiers::ALT,
        }
    };
}

/// Macro for defining a `InputTrie<InputEventTrait>`. Example:
///
/// ```
/// # use helix_core::hashmap;
/// # use helix_term::{keymap, keymap::InputTrie};
/// # use helix_view::input::{MouseEvent, KeyEvent};
/// let normal_mode: InputTrie<KeyEvent> = keymap!({ "Normal mode"
///     "i" => insert_mode,
///     "g" => { "Goto"
///         "g" => goto_file_start,
///         "e" => goto_file_end,
///     },
///     "j" | "down" => move_line_down,
/// });
/// let keymap = normal_mode;
/// // OR
/// let normal_mode_mouse: InputTrie<MouseEvent> = keymap!({
///     "Normal mode"
///     "1-right" => goto_line_end,
///     "2-left" => move_char_left,
/// });
/// // You cannot have both
/// ```
#[macro_export]
macro_rules! keymap {
    (@trie $cmd:ident) => {
        $crate::keymap::InputTrie::MappableCommand($crate::commands::MappableCommand::$cmd)
    };

    (@trie
        { $label:literal $(sticky=$sticky:literal)? $($($key:literal)|+ => $value:tt,)+ }
    ) => {
        keymap!({ $label $(sticky=$sticky)? $($($key)|+ => $value,)+ })
    };

    (@trie [$($cmd:ident),* $(,)?]) => {
        $crate::keymap::InputTrie::Sequence(vec![$($crate::commands::MappableCommand::$cmd),*])
    };

    (
        { $label:literal $(sticky=$sticky:literal)? $($($key:literal)|+ => $value:tt,)+ }
    ) => {
        // modified from the hashmap! macro
        {
            let _cap = hashmap!(@count $($($key),+),*);
            // let mut _map: HashMap<$($gene)+, $crate::keymap::InputTrie<$($gene)+>> = ::std::collections::HashMap::with_capacity(_cap);
            let mut _map = ::std::collections::HashMap::with_capacity(_cap);
            let mut _order = ::std::vec::Vec::with_capacity(_cap);
            $(
                $(
                    let _key = $key.parse().unwrap();
                    let _duplicate = _map.insert(
                        _key,
                        keymap!(@trie $value)
                    );
                    assert!(_duplicate.is_none(), "Duplicate key found: {:?}", _duplicate.unwrap());
                    _order.push(_key);
                )+
            )*
            let mut _node = $crate::keymap::InputTrieNode::new($label, _map, _order);
            $( _node.is_sticky = $sticky; )?
            $crate::keymap::InputTrie::Node(_node)
        }
    };
}

pub use alt;
pub use ctrl;
pub use key;
pub use keymap;
pub use shift;
