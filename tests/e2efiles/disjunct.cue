{
	"x1": *"tcp" | "udp"
	"x2": *1 | 2 | 3
	"x3": (*1 | 2 | 3) | (1 | *2 | 3)
	"x4": (*1 | 2 | 3) | *(1 | *2 | 3)
	"x5": (*1 | 2 | 3) | (1 | *2 | 3) & 2
	"x6": (*1 | 2) & (1 | *2)
}
