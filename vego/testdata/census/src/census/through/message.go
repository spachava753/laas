package through

// Message is an interface of the module whose one method has no contract.
// Send calls the method in a statement, which asks whether the call ends
// the process, and Make converts a value to the interface: both take the
// method with the weakest contract of a method, without its receiver
// among the parameters (F29 of the review).
type Message interface{ marshal(to *wire) }

type wire struct{ a, b int }

type Request struct{ x any }

func (r *Request) marshal(to *wire) {}

func Send(m Message) { m.marshal(&wire{}) }

func Make() (m Message, err error) { return &Request{}, nil }
