// Package mcp stands for the package of the MCP SDK
// (github.com/modelcontextprotocol/go-sdk/mcp) that the guide's handler
// uses: a module of its own, with the shape of the SDK's Content,
// TextContent, and CallToolResult.
package mcp

import "encoding/json"

// Content is the content of a result.
type Content interface {
	MarshalJSON() ([]byte, error)
	fromWire(text string)
}

// TextContent is textual content.
type TextContent struct {
	Text string
	Meta map[string]any
}

// MarshalJSON encodes the text.
func (c *TextContent) MarshalJSON() ([]byte, error) {
	return json.Marshal(struct {
		Type string `json:"type"`
		Text string `json:"text"`
	}{"text", c.Text})
}

func (c *TextContent) fromWire(text string) { c.Text = text }

// CallToolResult is what a tool handler returns.
type CallToolResult struct {
	Content []Content
	IsError bool
}
