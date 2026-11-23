package owns

// Cache owns its map, which Put makes when it is nil.
//
// @Owns m
type Cache struct {
	m map[string]int
}

// Put stores v under k.
//
// @Requires c != nil
// @Modifies c
// @Ensures has(c.m', k) And c.m'[k] = v
func (c *Cache) Put(k string, v int) {
	if c.m == nil {
		c.m = make(map[string]int)
	}
	c.m[k] = v
}

// PutTwo puts twice into a cache it is handed.
//
// @Requires c != nil
// @Modifies c
// @Ensures has(c.m', "b") And c.m'["b"] = 2
func PutTwo(c *Cache) {
	c.Put("a", 1)
	c.Put("b", 2)
}

// Config is what a Server owns through a pointer.
type Config struct {
	port int
}

// Server owns the Config its pointer points to.
//
// @Owns cfg
type Server struct {
	cfg  *Config
	name string
}

// SetPort writes the Config under Modifies s.
//
// @Requires s != nil And s.cfg != nil
// @Modifies s
// @Ensures s.cfg'.port = p
func (s *Server) SetPort(p int) {
	s.cfg.port = p
}

// NewServer makes a Server whose Config is new.
//
// @Ensures r != nil And r.cfg != nil And r.cfg.port = 80
func NewServer() (r *Server) {
	return &Server{cfg: &Config{port: 80}}
}
