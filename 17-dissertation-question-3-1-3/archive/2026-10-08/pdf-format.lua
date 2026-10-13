-- Retain the supplied paper's text, with its first two blocks as title metadata.
function Pandoc(doc)
  local title = doc.blocks[1]
  local revision = doc.blocks[2]
  assert(title.t == 'Header' and title.level == 1, 'Expected the paper title')
  assert(pandoc.utils.stringify(revision) == 'Revised prose proof — 8 October 2026',
         'Expected the supplied paper revision line')
  doc.meta.title = pandoc.MetaInlines(title.content)
  doc.meta.subtitle = pandoc.MetaString('Revised prose proof')
  doc.meta.date = pandoc.MetaString('8 October 2026')
  doc.blocks:remove(2)
  doc.blocks:remove(1)
  return doc:walk({
    Header = function(header)
      header.level = header.level - 1
      return header
    end,
    Code = function(code)
      -- Permit line breaks within long Lean module names in the references.
      local rendered = pandoc.write(pandoc.Pandoc({pandoc.Plain({code})}), 'latex')
      rendered = rendered:gsub('([a-z])([A-Z])', '%1\\allowbreak{}%2')
      return pandoc.RawInline('latex', rendered:gsub('\n$', ''))
    end,
  })
end
