use std::{
    collections::HashSet,
    env, fs,
    path::{Path, PathBuf},
    process::ExitCode,
};

use proc_macro2::LineColumn;
use syn::{Attribute, Block, ImplItemFn, ItemFn, ItemMod, ItemUse, spanned::Spanned, visit::Visit};

struct ModuleImports {
    indent: String,
    fallback: usize,
    insertion: Option<usize>,
    existing: HashSet<String>,
    moved: Vec<String>,
}

struct LocalImport {
    line: usize,
    start: usize,
    end: usize,
}

struct ImportVisitor<'a> {
    source: &'a str,
    lines: Vec<usize>,
    block_depth: usize,
    cfg_stack: Vec<String>,
    modules: Vec<ModuleImports>,
    module_stack: Vec<usize>,
    local: Vec<LocalImport>,
}

impl<'a> ImportVisitor<'a> {
    fn new(source: &'a str) -> Self {
        let mut lines = vec![0];
        lines.extend(source.match_indices('\n').map(|(index, _)| index + 1));
        Self {
            source,
            lines,
            block_depth: 0,
            cfg_stack: Vec::new(),
            modules: vec![ModuleImports {
                indent: String::new(),
                fallback: 0,
                insertion: None,
                existing: HashSet::new(),
                moved: Vec::new(),
            }],
            module_stack: vec![0],
            local: Vec::new(),
        }
    }

    fn offset(&self, location: LineColumn) -> usize {
        self.lines[location.line - 1] + location.column
    }

    fn line_start(&self, offset: usize) -> usize {
        self.source[..offset]
            .rfind('\n')
            .map_or(0, |index| index + 1)
    }

    fn line_end(&self, offset: usize) -> usize {
        self.source[offset..]
            .find('\n')
            .map_or(self.source.len(), |index| offset + index + 1)
    }

    fn cfg_text(&self, attributes: &[Attribute]) -> String {
        attributes
            .iter()
            .filter(|attribute| attribute.path().is_ident("cfg"))
            .map(|attribute| {
                let span = attribute.span();
                self.source[self.offset(span.start())..self.offset(span.end())]
                    .trim()
                    .to_string()
                    + "\n"
            })
            .collect()
    }
}

impl<'ast> Visit<'ast> for ImportVisitor<'_> {
    fn visit_block(&mut self, block: &'ast Block) {
        self.block_depth += 1;
        syn::visit::visit_block(self, block);
        self.block_depth -= 1;
    }

    fn visit_item_fn(&mut self, function: &'ast ItemFn) {
        self.cfg_stack.push(self.cfg_text(&function.attrs));
        self.visit_block(&function.block);
        self.cfg_stack.pop();
    }

    fn visit_impl_item_fn(&mut self, function: &'ast ImplItemFn) {
        self.cfg_stack.push(self.cfg_text(&function.attrs));
        self.visit_block(&function.block);
        self.cfg_stack.pop();
    }

    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        let Some((brace, items)) = &module.content else {
            return;
        };
        let index = self.modules.len();
        self.modules.push(ModuleImports {
            indent: items.first().map_or_else(
                || "    ".to_string(),
                |item| " ".repeat(item.span().start().column),
            ),
            fallback: self.offset(brace.span.open().end()),
            insertion: None,
            existing: HashSet::new(),
            moved: Vec::new(),
        });
        self.module_stack.push(index);
        let saved_depth = self.block_depth;
        self.block_depth = 0;
        for item in items {
            self.visit_item(item);
        }
        self.block_depth = saved_depth;
        self.module_stack.pop();
    }

    fn visit_item_use(&mut self, item: &'ast ItemUse) {
        let span = item.span();
        let start = self.offset(span.start());
        let end = self.offset(span.end());
        let text = self.source[start..end].trim();
        let module_index = *self.module_stack.last().expect("root module");
        let insertion = self.line_end(end);
        let item_cfg = self.cfg_text(&item.attrs);
        let key = normalize(&(self.cfg_stack.concat() + &item_cfg + text));
        let module = &mut self.modules[module_index];
        if self.block_depth == 0 {
            module.existing.insert(key);
            module.insertion = Some(insertion);
            return;
        }

        if module.existing.insert(key) {
            let mut moved = self.cfg_stack.concat();
            moved.push_str(&item_cfg);
            moved.push_str(text);
            module.moved.push(moved);
        }
        let first = item.attrs.first().map_or(span, Attribute::span);
        self.local.push(LocalImport {
            line: span.start().line,
            start: self.line_start(self.offset(first.start())),
            end: self.line_end(end),
        });
    }
}

fn normalize(text: &str) -> String {
    text.chars()
        .filter(|character| !character.is_whitespace())
        .collect()
}

fn rust_files(root: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    for entry in fs::read_dir(root).map_err(|error| format!("{}: {error}", root.display()))? {
        let path = entry.map_err(|error| error.to_string())?.path();
        if path.is_dir() {
            if !matches!(
                path.file_name().and_then(|name| name.to_str()),
                Some(".git" | "target")
            ) {
                rust_files(&path, files)?;
            }
        } else if path.extension().and_then(|extension| extension.to_str()) == Some("rs") {
            files.push(path);
        }
    }
    Ok(())
}

fn inspect(path: &Path, fix: bool) -> Result<bool, String> {
    let mut source = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let syntax =
        syn::parse_file(&source).map_err(|error| format!("{}: {error}", path.display()))?;
    let mut visitor = ImportVisitor::new(&source);
    visitor.modules[0].fallback = syntax.attrs.last().map_or(0, |attribute| {
        visitor.line_end(visitor.offset(attribute.span().end()))
    });
    visitor.visit_file(&syntax);
    if visitor.local.is_empty() {
        return Ok(true);
    }
    if !fix {
        for import in visitor.local {
            eprintln!("{}:{}: block-local import", path.display(), import.line);
        }
        return Ok(false);
    }

    let mut edits = visitor
        .local
        .iter()
        .map(|import| (import.start, import.end, String::new()))
        .collect::<Vec<_>>();
    for module in &visitor.modules {
        if module.moved.is_empty() {
            continue;
        }
        if module.insertion.is_none() && module.fallback == 0 {
            return Err(format!(
                "{}: module has no import insertion point",
                path.display()
            ));
        }
        let insertion = module.insertion.unwrap_or(module.fallback);
        let mut text = if module.insertion.is_none() {
            "\n".to_string()
        } else {
            String::new()
        };
        for import in &module.moved {
            for line in import.lines() {
                text.push_str(&module.indent);
                text.push_str(line);
                text.push('\n');
            }
        }
        edits.push((insertion, insertion, text));
    }
    edits.sort_by_key(|(start, end, _)| (*start, *end));
    for (start, end, replacement) in edits.into_iter().rev() {
        source.replace_range(start..end, &replacement);
    }
    fs::write(path, source).map_err(|error| error.to_string())?;
    Ok(true)
}

fn run(root: &Path, fix: bool) -> Result<bool, String> {
    let mut files = Vec::new();
    rust_files(root, &mut files)?;
    files.sort();
    let mut clean = true;
    for path in files {
        clean &= inspect(&path, fix)?;
    }
    Ok(clean)
}

fn main() -> ExitCode {
    let mut args = env::args_os().skip(1);
    let first = args.next();
    let fix = first.as_deref() == Some(std::ffi::OsStr::new("--fix"));
    let root =
        if fix { args.next() } else { first }.map_or_else(|| PathBuf::from("."), PathBuf::from);
    match run(&root, fix) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(error) => {
            eprintln!("import lint failed: {error}");
            ExitCode::FAILURE
        }
    }
}
