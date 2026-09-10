path = 'Exotic/ERL/FullCoupled/CompleteSafe_v147.agda'
s = File.read(path)

pattern = /\nqRunTerminalKKT_v147 :\n(?:--.*\n)+/

unless pattern.match?(s)
  puts 'v168 terminal KKT stub already removed'
else
  s.sub!(pattern, "\n")
end

File.write(path, s)
puts 'v168 dangling terminal KKT stub: PASS'