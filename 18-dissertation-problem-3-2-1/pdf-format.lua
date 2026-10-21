-- One canonical Markdown source; generated title, abstract and proof endings.
function Pandoc(doc)
  local title, date = doc.blocks[1], doc.blocks[2]
  assert(title.t == 'Header' and title.level == 1, 'Expected paper title')
  assert(pandoc.utils.stringify(date) == '20 October 2026', 'Unexpected edition date')
  assert(doc.blocks[3].t == 'Header' and
         pandoc.utils.stringify(doc.blocks[3]) == 'Abstract', 'Expected abstract')
  assert(doc.blocks[4].t == 'Para', 'Expected one abstract paragraph')
  doc.meta.title = pandoc.MetaInlines(title.content)
  doc.meta.date = pandoc.MetaString('20 October 2026')
  doc.meta.abstract = pandoc.MetaBlocks({doc.blocks[4]})
  for i = 1, 4 do doc.blocks:remove(1) end
  return doc:walk({
    Header = function(h) h.level = h.level - 1; return h end,
    Math = function(m)
      if m.text == '\\square' then
        return pandoc.RawInline('latex', '\\hfill\\(\\square\\)')
      end
    end,
  })
end
