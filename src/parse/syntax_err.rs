use std::{cmp::{max, min}, fmt::Display, ops::Range};

use crate::annotations;


pub struct Suggestion {
    loc: usize,
    starting_line: usize, // Starting line of the beginning of `source_edited`

    msg: String,
    suggestion: String,

    source_edited: String, // Part of the source copied, along with the rendered suggestion
}

pub struct Annotation {
    loc: Range<usize>, 
    msg: String, 

    level: annotations::Level, 
    inline: bool,
}

pub struct SyntaxErr {
    pub filename: Option<String>,
    pub source: &'static str,

    pub in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines: bool, // For unescaped brackets or multiline string literals

    pub loc: Range<usize>,
    pub msg: String,

    pub help_msg: Option<(Range<usize>, String)>,

    pub suggestions: Vec<Suggestion>,
    pub annotations: Vec<Annotation>,

    renderer: annotations::Renderer,
}

pub type SyntaxErrRef = &'static mut SyntaxErr;

impl<'source> SyntaxErr {  
    pub fn new(filename: Option<String>, source: &'static str) -> Self {
        Self {
            filename,
            source: source,
            in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines: false,
            loc: 0..0,
            msg: String::new(),
            help_msg: None,
            suggestions: Vec::new(),
            annotations: Vec::new(),
            renderer: annotations::Renderer::styled()
        }
    }

    pub fn loc(&mut self, loc: Range<usize>) -> &mut Self {
        self.loc = self.check_range(loc);
        self
    }

    pub fn msg(&mut self, msg: &str) -> &mut Self {
        self.msg = msg.to_string();
        self
    }

    pub fn loc_msg(&mut self, loc: Range<usize>, msg: &str) -> &mut Self { 
        self.loc(loc).msg(msg) 
    }

    pub fn help(&mut self, loc: Range<usize>, msg: &str) -> &mut Self {
        self.help_msg = Some((self.check_range(loc), msg.to_string()));
        self
    }

    pub fn annotation(&mut self, level: annotations::Level, loc: Range<usize>, msg: &str, inline: bool) -> &mut Self {
        self.annotations.push(Annotation { level, loc: self.check_range(loc), msg: msg.to_string(), inline} );
        self
    }
    
    fn check_range(&self, range: Range<usize>) -> Range<usize> {
        min(max(0, range.start), self.source.len())..min(max(0, range.end), self.source.len())
    }

    fn check_loc(&self, l: usize) -> usize {
        min(max(0, l), self.source.len())
    }

    pub fn suggestion(&mut self, loc: usize, suggestion: &str, msg: &str) -> &mut Self {        
        let mut loc = self.check_loc(loc);
        
        // Instead of copying and editing entire source, just do +- 1024 bytes around the suggestion
        let source_range = self.check_range(loc.saturating_sub(1024)..loc.saturating_add(suggestion.len() + 1024));
        let starting_line = max(1, (&self.source[..source_range.start]).lines().count());

        loc -= source_range.start;

        let mut s = Suggestion {
            loc,
            starting_line,
            msg: msg.to_string(),
            suggestion: suggestion.to_string(),
            source_edited: self.source[source_range].to_string(),
        };
        
        s.source_edited.insert_str(s.loc, &format!("{}{}{}", 
            self.renderer.stylesheet.suggestion.render(), 
            s.suggestion, 
            self.renderer.stylesheet.suggestion.render_reset()
        ));
        self.suggestions.push(s);
            
        self
    }

    pub fn suggestion_replace(&mut self, replace: Range<usize>, suggestion: &str, msg: &str) -> &mut Self {
        // Instead of copying and editing entire source, just do +- 1024 bytes around the suggestion
        let source_range = self.check_range(replace.start.saturating_sub(1024)..replace.end.saturating_add(suggestion.len() + 1024));

        let starting_line = max(1, (&self.source[..source_range.start]).lines().count());
        let replace = replace.start-source_range.start..replace.end-source_range.start;

        let mut s: Suggestion = Suggestion {
            loc: replace.start,
            starting_line,
            msg: msg.to_string(),
            suggestion: suggestion.to_string(),
            source_edited: self.source[source_range].to_string(),
        };

        s.source_edited.replace_range(replace, &format!("{}{}{}", 
            self.renderer.stylesheet.suggestion.render(), 
            s.suggestion, 
            self.renderer.stylesheet.suggestion.render_reset()
        ));
        self.suggestions.push(s);

        self
    }

    pub fn in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines(&mut self, should_it: bool) -> &mut Self {
        self.in_interactive_interpreter_should_discard_syntax_error_and_instead_read_more_lines = should_it;
        self
    }
}

impl<'source> Display for SyntaxErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut snippet_err = annotations::Snippet::source(&self.source)
            .line_start(1)
            .fold(true)
            .annotation(
                annotations::Level::Error
                    .span(self.loc.clone())
                    .label(&self.msg)
            );        
            
        if let Some(filename) = &self.filename {
            snippet_err = snippet_err.origin(filename);
        }

        for a in &self.annotations {
            if a.inline { snippet_err = snippet_err.annotation(a.level.span(a.loc.clone()).label(&a.msg)); }
        }

        let mut msg_to_render = annotations::Level::Error
            .title("syntax")
            .snippet(snippet_err);

        if let Some((help_loc, help_msg)) = &self.help_msg {
            let help_snippet = annotations::Snippet::source(&self.source)
                .line_start(1)
                .fold(true)
                .annotation(
                    annotations::Level::Error
                        .span(help_loc.clone())
                        .label(help_msg),
                );
            msg_to_render = msg_to_render.snippet(help_snippet);
        }
        
        for a in &self.annotations {
            if !a.inline { 
                let annotation_snippet = annotations::Snippet::source(&self.source)
                    .line_start(1)
                    .fold(true)
                    .annotation(a.level.span(a.loc.clone()).label(&a.msg)
                );
                msg_to_render = msg_to_render.snippet(annotation_snippet);
            }
        }

        for s in &self.suggestions {
            msg_to_render = msg_to_render.snippet(annotations::Snippet::source(&s.source_edited)
                .line_start(s.starting_line)
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