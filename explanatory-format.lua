return {
  {Math = function(m)
    if m.text == '\\square' then
      return pandoc.RawInline('latex', '\\hfill\\(\\square\\)')
    end
  end},
}
