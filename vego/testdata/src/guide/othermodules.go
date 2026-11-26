package guide

import "mcp"

// Reply is the guide's tool handler, which builds a result of the MCP SDK
// for the SDK to send (Values of another module's types).
//
// @Ensures result != nil
func Reply(msg string) (result *mcp.CallToolResult) {
	return &mcp.CallToolResult{
		Content: []mcp.Content{&mcp.TextContent{Text: msg}},
	}
}
