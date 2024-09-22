use std::{cmp::{max, min}, fmt::Display, ops::Range};

use crate::annotations;

#[derive(Debug)]

pub struct Suggestion {
    loc: usize,
    msg: String,
    suggestion: String,

    source_edited: String, // Gets filled in when SyntaxErr is rendered @Hack @TODO @Speed @Memory This is copying the entire source, where this can be avoided if the annotations module handled inserting the suggestion 
}

#[derive(Debug)]
pub struct SyntaxErr<'source> {
    pub filename: Option<String>,
    pub source: &'source str,

    pub in_interactive_interpreter_should_discard_and_instead_read_more_lines: bool, // For unescaped brackets or multiline string literals

    pub loc: Range<usize>,
    pub msg: String,

    pub help_msg: Option<(Range<usize>, String)>,

    pub suggestions: Vec<Suggestion>,
    pub annotations: Vec<(annotations::Level, Range<usize>, String, bool)>,

    renderer: annotations::Renderer,
}

impl<'source> SyntaxErr<'source> {  
    pub fn new(filename: Option<String>, source: &'source str) -> Self {
        Self {
            filename,
            source,
            in_interactive_interpreter_should_discard_and_instead_read_more_lines: false,
            loc: 0..0,
            msg: String::new(),
            help_msg: None,
            suggestions: Vec::new(),
            annotations: Vec::new(),
            renderer: annotations::Renderer::styled()
        }
    }

    pub fn loc(mut self, loc: Range<usize>) -> Self {
        self.loc = loc;
        self
    }

    pub fn msg(mut self, msg: &str) -> Self {
        self.msg = msg.to_string();
        self
    }

    pub fn loc_msg(self, loc: Range<usize>, msg: &str) -> Self { self.loc(loc).msg(msg) }

    pub fn help(mut self, loc: Range<usize>, msg: &str) -> Self {
        self.help_msg = Some((loc, msg.to_string()));
        self
    }

    pub fn annotation(mut self, level: annotations::Level, loc: Range<usize>, msg: &str, inline: bool) -> Self {
        self.annotations.push((level, loc, msg.to_string(), inline));
        self
    }

    pub fn suggestion(mut self, loc: usize, suggestion: &str, msg: &str) -> Self {
        let mut s = Suggestion {
            loc: min(max(0, loc), self.source.len()),
            msg: msg.to_string(),
            suggestion: suggestion.to_string(),
            source_edited: self.source.to_string(),
        };
        
        s.source_edited.insert_str(s.loc, &format!("{}{}{}", 
            self.renderer.stylesheet.suggestion.render(), 
            s.suggestion, 
            self.renderer.stylesheet.suggestion.render_reset()
        ));
        self.suggestions.push(s);
            
        self
    }

    pub fn suggestion_replace(mut self, replace: Range<usize>, suggestion: &str, msg: &str) -> Self {
        let checked_range = min(max(0, replace.start), self.source.len())..min(max(0, replace.end), self.source.len());

        let mut s = Suggestion {
            loc: checked_range.start,
            msg: msg.to_string(),
            suggestion: suggestion.to_string(),
            source_edited: self.source.to_string(),
        };

        s.source_edited.replace_range(checked_range.clone(), &format!("{}{}{}", 
            self.renderer.stylesheet.suggestion.render(), 
            s.suggestion, 
            self.renderer.stylesheet.suggestion.render_reset()
        ));
        self.suggestions.push(s);

        self
    }

    pub fn in_interactive_interpreter_should_discard_and_instead_read_more_lines(mut self, should_it: bool) -> Self {
        self.in_interactive_interpreter_should_discard_and_instead_read_more_lines = should_it;
        self
    }
}

impl<'source> Display for SyntaxErr<'source> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let checked_loc = min(max(0, self.loc.start), self.source.len())..min(max(0, self.loc.end), self.source.len());
        let mut snippet_err = annotations::Snippet::source(&self.source)
            .line_start(1)
            .fold(true)
            .annotation(
                annotations::Level::Error
                    .span(checked_loc)
                    .label(&self.msg)
            );        
            
        if let Some(filename) = &self.filename {
            snippet_err = snippet_err.origin(filename);
        }

        for a in &self.annotations {
            if a.3 { // inline
                let annotation_checked_range = min(max(0, a.1.start), self.source.len())..min(max(0, a.1.end), self.source.len());
                snippet_err = snippet_err.annotation(a.0.span(annotation_checked_range).label(&a.2));
            }
        }

        let mut msg_to_render = annotations::Level::Error
            .title("syntax")
            .snippet(snippet_err);

        if let Some((help_loc, help_msg)) = &self.help_msg {
            let checked_range = min(max(0, help_loc.start), self.source.len())..min(max(0, help_loc.end), self.source.len());

            let help_snippet = annotations::Snippet::source(&self.source)
                .line_start(1)
                .fold(true)
                .annotation(
                    annotations::Level::Error
                        .span(checked_range)
                        .label(help_msg),
                );
            msg_to_render = msg_to_render.snippet(help_snippet);
        }
        
        for a in &self.annotations {
            if !a.3 { // ... now do those not inline
                let annotation_checked_range = min(max(0, a.1.start), self.source.len())..min(max(0, a.1.end), self.source.len());

                let annotation_snippet = annotations::Snippet::source(&self.source)
                    .line_start(1)
                    .fold(true)
                    .annotation(
                        a.0.span(annotation_checked_range).label(&a.2)
                );
                msg_to_render = msg_to_render.snippet(annotation_snippet);
            }
        }

        for s in &self.suggestions {
            msg_to_render = msg_to_render.snippet(annotations::Snippet::source(&s.source_edited)
                .line_start(1)
                .fold(true)
                .annotation(
                    annotations::Level::Suggestion
                        .span((s.loc+1)..(s.loc+1+s.suggestion.len()))
                        .label(&s.msg),
                )
            );
        }

        write!(f, "{}", self.renderer.render(msg_to_render))
    }

}