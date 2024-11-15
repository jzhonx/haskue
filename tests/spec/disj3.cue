a0: "tcp" | "udp"
a1: *"tcp" | "udp"
a2: (*1 | 2) + (2 | *3)

b0: (*1 | 2 | 3) | (1 | *2 | 3)
b1: (*1 | 2 | 3) & (1 | *2 | 3)

c0: (*"tcp" | "udp") & ("udp" | *"tcp")
c1: (*"tcp" | "udp") & ("udp" | "tcp")
c2: (*"tcp" | "udp") & "tcp"
c3: (*"tcp" | "udp") & (*"udp" | "tcp")

d0: (*true | false) & (true | false)

e0: {a: 1} | {b: 1}
e1: {a: 1} | *{b: 1}
e2: *{a: 1} | *{b: 1}
e3: ({a: 1} | {b: 1}) & {a: 1}
e4: ({a: 1} | *{b: 1}) & ({a: 1} | *{b: 1})
