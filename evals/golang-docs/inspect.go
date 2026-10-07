package main

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"sort"
	"strings"
)

type span struct {
	Start int `json:"start"`
	End   int `json:"end"`
}

type document struct {
	Text string `json:"text"`
	Name string `json:"name"`
}

type inspection struct {
	Kind        string              `json:"kind"`
	Docs        map[string]document `json:"docs"`
	Ranges      []span              `json:"ranges"`
	Fingerprint string              `json:"fingerprint"`
	Declaration string              `json:"declaration"`
}

// inspect finds exactly one named function, method, or type, then separates
// its associated documentation from the rest of the file. Struct field
// comments are included; interface member comments remain unchanged.
func inspect(src []byte, symbol string) (inspection, error) {
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "source.go", src, parser.ParseComments|parser.AllErrors)
	if err != nil {
		return inspection{}, err
	}
	result := inspection{Docs: map[string]document{}, Ranges: []span{}}
	var node ast.Node
	matches := 0
	for _, decl := range file.Decls {
		switch d := decl.(type) {
		case *ast.FuncDecl:
			name := d.Name.Name
			kind := "function"
			if d.Recv != nil {
				name = receiverName(d.Recv.List[0].Type) + "." + name
				kind = "method"
			}
			if name == symbol {
				matches++
				node = d
				result.Kind = kind
				result.addDoc(fset, "$doc", d.Name.Name, d.Doc)
			}
		case *ast.GenDecl:
			if d.Tok != token.TYPE {
				continue
			}
			for _, spec := range d.Specs {
				s := spec.(*ast.TypeSpec)
				if s.Name.Name != symbol {
					continue
				}
				matches++
				node = s
				result.Kind = "type"
				doc := s.Doc
				if doc == nil && len(d.Specs) == 1 {
					doc = d.Doc
				} else if doc == nil && d.Doc != nil {
					return inspection{}, fmt.Errorf("%s has a shared type-group comment", symbol)
				}
				result.addDoc(fset, "$doc", s.Name.Name, doc)
				if st, ok := s.Type.(*ast.StructType); ok {
					result.Kind = "struct"
					for _, field := range st.Fields.List {
						names := []string{}
						for _, n := range field.Names {
							names = append(names, n.Name)
						}
						if len(names) == 0 {
							names = append(names, receiverName(field.Type))
						}
						name := strings.Join(names, ",")
						result.addDoc(fset, name, names[0], field.Doc, field.Comment)
					}
				}
			}
		}
	}
	if matches != 1 {
		return inspection{}, fmt.Errorf("expected one declaration for %s; found %d", symbol, matches)
	}
	sort.Slice(result.Ranges, func(i, j int) bool { return result.Ranges[i].Start < result.Ranges[j].Start })
	masked := append([]byte(nil), src...)
	for _, r := range result.Ranges {
		for _, line := range strings.Split(string(src[r.Start:r.End]), "\n") {
			line = strings.TrimSpace(line)
			if strings.HasPrefix(line, "//go:") || strings.HasPrefix(line, "//line ") || strings.HasPrefix(line, "/*line ") {
				return inspection{}, fmt.Errorf("compiler and line directives are not documentation")
			}
		}
		for i := r.Start; i < r.End; i++ {
			if masked[i] != '\n' && masked[i] != '\r' {
				masked[i] = ' '
			}
		}
	}
	// Scanning ignores whitespace, but retains every non-target comment,
	// identifier, literal, operator, and implicit semicolon.
	var scan scanner.Scanner
	scanFile := token.NewFileSet().AddFile("masked.go", -1, len(masked))
	scan.Init(scanFile, masked, nil, scanner.ScanComments)
	hash := sha256.New()
	for {
		_, tok, literal := scan.Scan()
		if tok == token.EOF {
			break
		}
		fmt.Fprintf(hash, "%d:%d:%s\n", tok, len(literal), literal)
	}
	result.Fingerprint = hex.EncodeToString(hash.Sum(nil))
	result.Declaration = string(masked[fset.Position(node.Pos()).Offset:fset.Position(node.End()).Offset])
	return result, nil
}

// addDoc records both leading and trailing field comments as one scoring unit,
// while preserving their separate byte ranges for safe stripping.
func (r *inspection) addDoc(fset *token.FileSet, key, name string, groups ...*ast.CommentGroup) {
	var texts []string
	for _, group := range groups {
		if group == nil {
			continue
		}
		texts = append(texts, group.Text())
		r.Ranges = append(r.Ranges, span{fset.Position(group.Pos()).Offset, fset.Position(group.End()).Offset})
	}
	r.Docs[key] = document{Text: strings.TrimSpace(strings.Join(texts, "\n")), Name: name}
}

func receiverName(expr ast.Expr) string {
	switch e := expr.(type) {
	case *ast.Ident:
		return e.Name
	case *ast.StarExpr:
		return receiverName(e.X)
	case *ast.IndexExpr:
		return receiverName(e.X)
	case *ast.IndexListExpr:
		return receiverName(e.X)
	case *ast.ParenExpr:
		return receiverName(e.X)
	case *ast.SelectorExpr:
		return e.Sel.Name
	default:
		return ""
	}
}
