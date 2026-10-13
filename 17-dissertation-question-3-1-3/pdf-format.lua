-- Use title/date metadata and typeset the standalone abstract as an abstract.
function Pandoc(doc)
  local title = doc.blocks[1]
  local date = doc.blocks[2]
  assert(title.t == 'Header' and title.level == 1, 'Expected the paper title')
  assert(pandoc.utils.stringify(date) == '13 October 2026',
         'Expected the standalone edition date')
  assert(doc.blocks[3].t == 'Header' and
         pandoc.utils.stringify(doc.blocks[3]) == 'Abstract',
         'Expected the abstract heading')
  assert(doc.blocks[4].t == 'Para', 'Expected one abstract paragraph')
  doc.meta.title = pandoc.MetaInlines(title.content)
  doc.meta.subtitle = pandoc.MetaString("A proof of Alexander's Question 3-1-3")
  doc.meta.date = pandoc.MetaString('13 October 2026')
  doc.meta.abstract = pandoc.MetaBlocks({doc.blocks[4]})
  doc.blocks:remove(4)
  doc.blocks:remove(3)
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
