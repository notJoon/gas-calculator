package calculator

import (
	"fmt"
	"go/ast"
	"go/token"
	"strconv"
	"strings"
)

// default gas cost based on GasMeter
type GasCost struct {
	// basic costs
	AddCost int64
	SubCost int64
	MulCost int64
	DivCost int64
	ModCost int64
	AndCost int64
	OrCost  int64
	XorCost int64
	NotCost int64
	NegCost int64
	ShlCost int64
	ShrCost int64

	// memory access costs
	HasCost          int64
	DeleteCost       int64
	ReadCostFlat     int64
	ReadCostPerByte  int64
	WriteCostFlat    int64
	WriteCostPerByte int64

	// function call
	FunctionCallCost int64

	// for-range iteration
	IterNextCostFlat int64
	ValueCostPerByte int64 // literal value (or variable) per byte
}

func DefaultGasCost() GasCost {
	return GasCost{
		AddCost: 1000,
		SubCost: 1000,
		MulCost: 2000,
		DivCost: 2000,
		ModCost: 2000,

		AndCost: 500,
		OrCost:  500,
		XorCost: 500,
		NotCost: 500,
		NegCost: 1000,
		ShlCost: 1000,
		ShrCost: 1000,

		FunctionCallCost: 1000,
		HasCost:          1000,
		DeleteCost:       1000,
		ReadCostFlat:     1000,
		ReadCostPerByte:  3,
		WriteCostFlat:    2000,
		WriteCostPerByte: 30,
		IterNextCostFlat: 30,
		ValueCostPerByte: 10,
	}
}

type FunctionAnalysis struct {
	Package        string
	Name           string
	TotalGasCost   int64
	OperationCosts map[string]int64
	Calls          []string // store the called functions in package.function format
}

// Analyzer analyzes the code base
type Analyzer struct {
	fset     *token.FileSet
	gasCosts GasCost
	analysis map[string]*FunctionAnalysis // key: "package.function"
}

func NewAnalyzer(fset *token.FileSet, gasCosts GasCost) *Analyzer {
	return &Analyzer{
		fset:     fset,
		gasCosts: gasCosts,
		analysis: make(map[string]*FunctionAnalysis),
	}
}

func (a *Analyzer) analyzeFile(pkgName string, file *ast.File) {
	ast.Inspect(file, func(n ast.Node) bool {
		if n == nil {
			return false
		}
		if funcDecl, ok := n.(*ast.FuncDecl); ok {
			qualifiedName := pkgName + "." + funcDecl.Name.Name
			analysis := &FunctionAnalysis{
				Package:        pkgName,
				Name:           funcDecl.Name.Name,
				OperationCosts: make(map[string]int64),
			}
			a.analyzeFuncionBody(funcDecl.Body, analysis)
			a.analysis[qualifiedName] = analysis
		}
		return true
	})
}

func (a *Analyzer) analyzeFuncionBody(body *ast.BlockStmt, analysis *FunctionAnalysis) {
	if body == nil {
		return
	}
	for _, stmt := range body.List {
		a.analyzeStatement(stmt, analysis)
	}
}

// analyzeStatement analyzes individual statements
func (a *Analyzer) analyzeStatement(stmt ast.Stmt, analysis *FunctionAnalysis) {
	switch s := stmt.(type) {
	case *ast.AssignStmt:
		a.analyzeAssignment(s, analysis)
	case *ast.IfStmt:
		a.analyzeIfStatement(s, analysis)
	case *ast.ForStmt:
		a.analyzeForStatement(s, analysis)
	case *ast.RangeStmt:
		a.analyzeRangeStatement(s, analysis)
	case *ast.ReturnStmt:
		a.analyzeReturnStatement(s, analysis)
	case *ast.ExprStmt:
		a.analyzeExpression(s.X, analysis)
	}
}

func (a *Analyzer) analyzeAssignment(stmt *ast.AssignStmt, analysis *FunctionAnalysis) {
	for _, lhs := range stmt.Lhs {
		a.analyzeLHS(lhs, analysis)
	}
	for _, rhs := range stmt.Rhs {
		a.analyzeExpression(rhs, analysis)
	}
}

func (a *Analyzer) analyzeLHS(expr ast.Expr, analysis *FunctionAnalysis) {
	switch e := expr.(type) {
	case *ast.Ident:
		defaultVarSize := 8
		analysis.OperationCosts["Write"] += a.gasCosts.WriteCostFlat + a.gasCosts.WriteCostPerByte*int64(defaultVarSize)
	case *ast.IndexExpr:
		defaultElementSize := 8
		analysis.OperationCosts["Write"] += a.gasCosts.WriteCostFlat + a.gasCosts.WriteCostPerByte*int64(defaultElementSize)
		a.analyzeExpression(e.X, analysis)
		a.analyzeExpression(e.Index, analysis)
	default:
		analysis.OperationCosts["Write"] += a.gasCosts.WriteCostFlat + a.gasCosts.WriteCostPerByte*8
	}
}

func (a *Analyzer) analyzeExpression(expr ast.Expr, analysis *FunctionAnalysis) {
	switch e := expr.(type) {
	case *ast.BinaryExpr:
		a.analyzeBinaryExpression(e, analysis)
	case *ast.CallExpr:
		a.analyzeCallExpression(e, analysis)
	case *ast.UnaryExpr:
		a.analyzeUnaryExpression(e, analysis)
	case *ast.BasicLit:
		a.analyzeBasicLit(e, analysis)
	case *ast.Ident:
		defaultVarSize := 8
		analysis.OperationCosts["Read"] += a.gasCosts.ReadCostFlat + a.gasCosts.ReadCostPerByte*int64(defaultVarSize)
	case *ast.IndexExpr:
		defaultElementSize := 8
		analysis.OperationCosts["Read"] += a.gasCosts.ReadCostFlat + a.gasCosts.ReadCostPerByte*int64(defaultElementSize)
		a.analyzeExpression(e.X, analysis)
		a.analyzeExpression(e.Index, analysis)
	}
}

func (a *Analyzer) analyzeBinaryExpression(expr *ast.BinaryExpr, analysis *FunctionAnalysis) {
	switch expr.Op {
	case token.ADD:
		analysis.OperationCosts[ADD] += a.gasCosts.AddCost
	case token.SUB:
		analysis.OperationCosts[SUB] += a.gasCosts.SubCost
	case token.MUL:
		analysis.OperationCosts[MUL] += a.gasCosts.MulCost
	case token.QUO:
		analysis.OperationCosts[DIV] += a.gasCosts.DivCost
	case token.REM:
		analysis.OperationCosts[MOD] += a.gasCosts.ModCost
	case token.AND:
		analysis.OperationCosts[AND] += a.gasCosts.AndCost
	case token.OR:
		analysis.OperationCosts[OR] += a.gasCosts.OrCost
	case token.XOR:
		analysis.OperationCosts[XOR] += a.gasCosts.XorCost
	case token.SHL:
		analysis.OperationCosts[SHL] += a.gasCosts.ShlCost
	case token.SHR:
		analysis.OperationCosts[SHR] += a.gasCosts.ShrCost
	}
	// analyze lhs, rhs accordingly
	a.analyzeExpression(expr.X, analysis)
	a.analyzeExpression(expr.Y, analysis)
}

func (a *Analyzer) analyzeCallExpression(expr *ast.CallExpr, analysis *FunctionAnalysis) {
	// apply function call cost
	analysis.OperationCosts[FunctionCall] += a.gasCosts.FunctionCallCost

	// extract called function name
	switch fun := expr.Fun.(type) {
	case *ast.Ident:
		// called from the same package:
		// package name is assumed to be the package of the function being analyzed
		qualifiedName := fmt.Sprintf("%s.%s", analysis.Package, fun.Name)
		analysis.Calls = append(analysis.Calls, qualifiedName)
	case *ast.SelectorExpr:
		// called from another package
		if ident, ok := fun.X.(*ast.Ident); ok {
			qualifiedName := fmt.Sprintf("%s.%s", ident.Name, fun.Sel.Name)
			analysis.Calls = append(analysis.Calls, qualifiedName)
		}
	}

	// apply analysis to arguments
	for _, arg := range expr.Args {
		a.analyzeExpression(arg, analysis)
	}
}

func (a *Analyzer) analyzeUnaryExpression(expr *ast.UnaryExpr, analysis *FunctionAnalysis) {
	switch expr.Op {
	case token.NOT:
		analysis.OperationCosts[NOT] += a.gasCosts.NotCost
	case token.SUB:
		analysis.OperationCosts[NEG] += a.gasCosts.NegCost
	}
	a.analyzeExpression(expr.X, analysis)
}

func (a *Analyzer) analyzeBasicLit(lit *ast.BasicLit, analysis *FunctionAnalysis) {
	var byteCount int
	switch lit.Kind {
	case token.STRING:
		s, err := strconv.Unquote(lit.Value)
		if err != nil {
			s = lit.Value
		}
		byteCount = len(s)
	default:
		byteCount = len(lit.Value)
	}
	analysis.OperationCosts["ValueBytes"] += a.gasCosts.ValueCostPerByte * int64(byteCount)
}

func (a *Analyzer) analyzeIfStatement(stmt *ast.IfStmt, analysis *FunctionAnalysis) {
	if stmt.Cond != nil {
		a.analyzeExpression(stmt.Cond, analysis)
	}
	if stmt.Body != nil {
		a.analyzeFuncionBody(stmt.Body, analysis)
	}
	if stmt.Else != nil {
		if elseBlock, ok := stmt.Else.(*ast.BlockStmt); ok {
			a.analyzeFuncionBody(elseBlock, analysis)
		} else {
			a.analyzeStatement(stmt.Else, analysis)
		}
	}
}

func (a *Analyzer) analyzeForStatement(stmt *ast.ForStmt, analysis *FunctionAnalysis) {
	if stmt.Cond != nil {
		a.analyzeExpression(stmt.Cond, analysis)
	}
	if stmt.Body != nil {
		a.analyzeFuncionBody(stmt.Body, analysis)
	}
}

func (a *Analyzer) analyzeRangeStatement(stmt *ast.RangeStmt, analysis *FunctionAnalysis) {
	// In static analysis, we don't know the exact number of iterations,
	// so by default we assume a single application
	analysis.OperationCosts["IterNext"] += a.gasCosts.IterNextCostFlat

	// slice, map etc.
	a.analyzeExpression(stmt.X, analysis)

	// analyze body
	a.analyzeFuncionBody(stmt.Body, analysis)
}

func (a *Analyzer) analyzeReturnStatement(stmt *ast.ReturnStmt, analysis *FunctionAnalysis) {
	for _, expr := range stmt.Results {
		a.analyzeExpression(expr, analysis)
	}
}

func (a *Analyzer) printAnalyses() {
	for qualifiedName, analysis := range a.analysis {
		fmt.Printf("Fn: %s\n", qualifiedName)
		var total int64 = 0
		for op, cost := range analysis.OperationCosts {
			fmt.Printf("  %s: %d\n", op, cost)
			total += cost
		}
		analysis.TotalGasCost = total
		fmt.Printf("  approx total gas consumed: %d\n", analysis.TotalGasCost)
		if len(analysis.Calls) > 0 {
			fmt.Printf("  called functions: %s\n", strings.Join(analysis.Calls, ", "))
		}
		fmt.Println("--------------------------------------------------")
	}
}
