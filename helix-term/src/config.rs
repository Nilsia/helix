use crate::keymap::{self, merge_inputs, InputTrie, InputTrieCheckError};
use helix_loader::merge_toml_values;
use helix_view::document::Mode;
use helix_view::input::{KeyEvent, MouseEvent};
use serde::Deserialize;
use std::collections::HashMap;
use std::fmt::Display;
use std::fs;
use std::io::Error as IOError;
use toml::de::Error as TomlError;

#[derive(Debug, Clone, PartialEq)]
pub struct Config {
    pub theme: Option<String>,
    pub keys: HashMap<Mode, InputTrie<KeyEvent>>,
    pub mouse: HashMap<Mode, InputTrie<MouseEvent>>,
    pub editor: helix_view::editor::Config,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConfigRaw {
    pub theme: Option<String>,
    pub keys: Option<HashMap<Mode, InputTrie<KeyEvent>>>,
    pub mouse: Option<HashMap<Mode, InputTrie<MouseEvent>>>,
    pub editor: Option<toml::Value>,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            theme: None,
            keys: keymap::default(),
            mouse: keymap::default_mouse(),
            editor: helix_view::editor::Config::default(),
        }
    }
}

#[derive(Debug)]
pub enum ConfigLoadError {
    BadConfig(TomlError),
    Error(IOError),
    ErrorOnVerify(InputTrieCheckError),
}

impl Default for ConfigLoadError {
    fn default() -> Self {
        ConfigLoadError::Error(IOError::new(std::io::ErrorKind::NotFound, "place holder"))
    }
}

impl Display for ConfigLoadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConfigLoadError::BadConfig(err) => err.fmt(f),
            ConfigLoadError::Error(err) => err.fmt(f),
            ConfigLoadError::ErrorOnVerify(err) => err.fmt(f),
        }
    }
}

impl Config {
    pub fn load(
        global: Result<String, ConfigLoadError>,
        local: Result<String, ConfigLoadError>,
    ) -> Result<Config, ConfigLoadError> {
        let global_config: Result<ConfigRaw, ConfigLoadError> =
            global.and_then(|file| toml::from_str(&file).map_err(ConfigLoadError::BadConfig));
        let local_config: Result<ConfigRaw, ConfigLoadError> =
            local.and_then(|file| toml::from_str(&file).map_err(ConfigLoadError::BadConfig));
        let res = match (global_config, local_config) {
            (Ok(global), Ok(local)) => {
                let mut keys: HashMap<Mode, InputTrie<KeyEvent>> = keymap::default();
                let mut mouse: HashMap<Mode, InputTrie<MouseEvent>> = keymap::default_mouse();
                if let Some(global_keys) = global.keys {
                    merge_inputs(&mut keys, global_keys)
                }
                if let Some(local_keys) = local.keys {
                    merge_inputs(&mut keys, local_keys)
                }
                if let Some(global_mouses) = global.mouse {
                    merge_inputs(&mut mouse, global_mouses)
                }
                if let Some(local_mouses) = local.mouse {
                    merge_inputs(&mut mouse, local_mouses)
                }
                for trie in mouse.values() {
                    if let Err(e) = trie.verify() {
                        return Err(ConfigLoadError::ErrorOnVerify(e));
                    }
                }
                let editor = match (global.editor, local.editor) {
                    (None, None) => helix_view::editor::Config::default(),
                    (None, Some(val)) | (Some(val), None) => {
                        val.try_into().map_err(ConfigLoadError::BadConfig)?
                    }
                    (Some(global), Some(local)) => merge_toml_values(global, local, 3)
                        .try_into()
                        .map_err(ConfigLoadError::BadConfig)?,
                };

                Config {
                    theme: local.theme.or(global.theme),
                    keys,
                    mouse,
                    editor,
                }
            }
            // if any configs are invalid return that first
            (_, Err(ConfigLoadError::BadConfig(err)))
            | (Err(ConfigLoadError::BadConfig(err)), _) => {
                return Err(ConfigLoadError::BadConfig(err))
            }
            (Ok(config), Err(_)) | (Err(_), Ok(config)) => {
                let mut keys: HashMap<Mode, InputTrie<KeyEvent>> = keymap::default();
                let mut mouse: HashMap<Mode, InputTrie<MouseEvent>> = keymap::default_mouse();
                if let Some(keymap) = config.keys {
                    merge_inputs(&mut keys, keymap);
                }
                if let Some(mousemap) = config.mouse {
                    merge_inputs(&mut mouse, mousemap)
                }
                for trie in mouse.values() {
                    if let Err(e) = trie.verify() {
                        return Err(ConfigLoadError::ErrorOnVerify(e));
                    }
                }
                Config {
                    theme: config.theme,
                    keys,
                    // TODO move this in arguments
                    mouse,
                    editor: config.editor.map_or_else(
                        || Ok(helix_view::editor::Config::default()),
                        |val| val.try_into().map_err(ConfigLoadError::BadConfig),
                    )?,
                }
            }

            // these are just two io errors return the one for the global config
            (Err(err), Err(_)) => return Err(err),
        };

        Ok(res)
    }

    pub fn load_default() -> Result<Config, ConfigLoadError> {
        let global_config =
            fs::read_to_string(helix_loader::config_file()).map_err(ConfigLoadError::Error);
        let local_config = fs::read_to_string(helix_loader::workspace_config_file())
            .map_err(ConfigLoadError::Error);
        Config::load(global_config, local_config)
    }
}

#[cfg(test)]
mod tests {
    use crate::keymap;

    use super::*;

    impl Config {
        fn load_test(config: &str) -> Config {
            Config::load(Ok(config.to_owned()), Err(ConfigLoadError::default())).unwrap()
        }
    }

    #[test]
    fn parsing_keymaps_config_file() {
        use crate::keymap;
        use helix_core::hashmap;
        use helix_view::document::Mode;

        let sample_keymaps = r#"
            [keys.insert]
            y = "move_line_down"
            S-C-a = "delete_selection"

            [keys.normal]
            A-F12 = "move_next_word_end"

            [mouse.normal]
            1-right = "move_char_right"

            [mouse.insert]
            1-right = "goto_line_end"
        "#;

        let mut keys = keymap::default();
        let mut mouse = keymap::default_mouse();
        merge_inputs(
            &mut keys,
            hashmap! {
                Mode::Insert => keymap!({ "Insert mode"
                    "y" => move_line_down,
                    "S-C-a" => delete_selection,
                }),
                Mode::Normal => keymap!({ "Normal mode"
                    "A-F12" => move_next_word_end,
                }),
            },
        );

        merge_inputs(
            &mut mouse,
            hashmap! {
                Mode::Normal => keymap!({ "Normal mode"
                    "1-right" => move_char_right,
                }),
                Mode::Insert => keymap!({ "Insert mode"
                    "1-right" => goto_line_end,
                }),
            },
        );

        assert_eq!(
            Config::load_test(sample_keymaps),
            Config {
                keys,
                mouse,
                ..Default::default()
            }
        );
    }
    #[test]
    fn keys_resolve_to_correct_defaults() {
        // From serde default
        let config = Config::load_test("");
        assert_eq!(config.keys, keymap::default());
        assert_eq!(config.mouse, keymap::default_mouse());

        // From the Default trait
        let config = Config::default();
        assert_eq!(config.keys, keymap::default());
        assert_eq!(config.mouse, keymap::default_mouse());
    }

    #[test]
    #[should_panic]
    fn forbid_specific_mousemaps_to_be_remapped() {
        let config_content = r#"[mouse.normal]
            1-left = "goto_line_end"
            "#;
        let _ = Config::load_test(config_content);
    }

    #[test]
    #[should_panic]
    fn same_mouse_button_inside_self_node() {
        // in this example this should be wrap into 2-right
        let config_content = r#"[mouse.normal]
            1-right = { 1-right = "goto_line_end" }
            "#;
        let _ = Config::load_test(config_content);
    }
}
