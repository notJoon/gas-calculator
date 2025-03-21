package calculator

import (
	"go/ast"
	"go/parser"
	"go/token"
	"slices"
	"testing"
)

func TestAnalyzeBinaryExpression(t *testing.T) {
	fset := token.NewFileSet()
	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	testCases := []struct {
		name     string
		op       token.Token
		costKey  string
		expected int64
	}{
		{"Addition", token.ADD, ADD, gasCosts.AddCost},
		{"Subtraction", token.SUB, SUB, gasCosts.SubCost},
		{"Multiplication", token.MUL, MUL, gasCosts.MulCost},
		{"Division", token.QUO, DIV, gasCosts.DivCost},
		{"Remainder", token.REM, MOD, gasCosts.ModCost},
		{"Bitwise AND", token.AND, AND, gasCosts.AndCost},
		{"Bitwise OR", token.OR, OR, gasCosts.OrCost},
		{"Bitwise XOR", token.XOR, XOR, gasCosts.XorCost},
		{"Shift Left", token.SHL, SHL, gasCosts.ShlCost},
		{"Shift Right", token.SHR, SHR, gasCosts.ShrCost},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			analysis := &FunctionAnalysis{
				Package:        "test",
				Name:           "testFunc",
				OperationCosts: make(map[string]int64),
			}

			expr := &ast.BinaryExpr{
				X:  &ast.Ident{Name: "a"},
				Op: tc.op,
				Y:  &ast.Ident{Name: "b"},
			}

			analyzer.analyzeBinaryExpression(expr, analysis)

			if got := analysis.OperationCosts[tc.costKey]; got != tc.expected {
				t.Errorf("analyzeBinaryExpression() for %s: got cost %d, want %d", tc.name, got, tc.expected)
			}
		})
	}
}

func TestAnalyzeUnaryExpression(t *testing.T) {
	fset := token.NewFileSet()
	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	testCases := []struct {
		name     string
		op       token.Token
		costKey  string
		expected int64
	}{
		{"Logical NOT", token.NOT, NOT, gasCosts.NotCost},
		{"Negation", token.SUB, NEG, gasCosts.NegCost},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			analysis := &FunctionAnalysis{
				Package:        "test",
				Name:           "testFunc",
				OperationCosts: make(map[string]int64),
			}

			expr := &ast.UnaryExpr{
				X:  &ast.Ident{Name: "a"},
				Op: tc.op,
			}

			analyzer.analyzeUnaryExpression(expr, analysis)

			if got := analysis.OperationCosts[tc.costKey]; got != tc.expected {
				t.Errorf("analyzeUnaryExpression() for %s: got cost %d, want %d", tc.name, got, tc.expected)
			}
		})
	}
}

func TestAnalyzeCallExpression(t *testing.T) {
	fset := token.NewFileSet()
	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	t.Run("Same package call", func(t *testing.T) {
		analysis := &FunctionAnalysis{
			Package:        "test",
			Name:           "caller",
			OperationCosts: make(map[string]int64),
			Calls:          []string{},
		}

		expr := &ast.CallExpr{
			Fun: &ast.Ident{Name: "callee"},
		}

		analyzer.analyzeCallExpression(expr, analysis)

		// Check cost is added
		if got := analysis.OperationCosts[FunctionCall]; got != gasCosts.FunctionCallCost {
			t.Errorf("analyzeCallExpression(): got cost %d, want %d", got, gasCosts.FunctionCallCost)
		}

		// Check call is recorded
		expectedCall := "test.callee"
		if len(analysis.Calls) != 1 || analysis.Calls[0] != expectedCall {
			t.Errorf("analyzeCallExpression(): got calls %v, want [%s]", analysis.Calls, expectedCall)
		}

		analyzer.printAnalyses()
	})

	t.Run("Different package call", func(t *testing.T) {
		analysis := &FunctionAnalysis{
			Package:        "test",
			Name:           "caller",
			OperationCosts: make(map[string]int64),
			Calls:          []string{},
		}

		expr := &ast.CallExpr{
			Fun: &ast.SelectorExpr{
				X:   &ast.Ident{Name: "fmt"},
				Sel: &ast.Ident{Name: "Println"},
			},
		}

		analyzer.analyzeCallExpression(expr, analysis)

		// Check cost is added
		if got := analysis.OperationCosts[FunctionCall]; got != gasCosts.FunctionCallCost {
			t.Errorf("analyzeCallExpression(): got cost %d, want %d", got, gasCosts.FunctionCallCost)
		}

		// Check call is recorded
		expectedCall := "fmt.Println"
		if len(analysis.Calls) != 1 || analysis.Calls[0] != expectedCall {
			t.Errorf("analyzeCallExpression(): got calls %v, want [%s]", analysis.Calls, expectedCall)
		}

		analyzer.printAnalyses()
	})
}

func TestAnalyzeFile(t *testing.T) {
	srcCode := `
package test

func Add(a, b int) int {
	return a + b
}

func Calculate(x, y int) int {
	z := x * y
	if z > 10 {
		return z + Add(x, y)
	} else {
		return z - 5
	}
}
`

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "test.go", srcCode, 0)
	if err != nil {
		t.Fatalf("Failed to parse test code: %v", err)
	}

	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	analyzer.analyzeFile("test", file)

	// Check if both functions were analyzed
	if len(analyzer.analysis) != 2 {
		t.Errorf("analyzeFile(): expected 2 functions analyzed, got %d", len(analyzer.analysis))
	}

	// Check the Add function
	addAnalysis, ok := analyzer.analysis["test.Add"]
	if !ok {
		t.Fatalf("analyzeFile(): missing analysis for test.Add")
	}

	if addAnalysis.Package != "test" || addAnalysis.Name != ADD {
		t.Errorf("analyzeFile(): incorrect package/name for Add, got %s/%s, want test/Add",
			addAnalysis.Package, addAnalysis.Name)
	}

	if addAnalysis.OperationCosts[ADD] != gasCosts.AddCost {
		t.Errorf("analyzeFile(): Add function should have addition cost of %d, got %d",
			gasCosts.AddCost, addAnalysis.OperationCosts[ADD])
	}

	// Check the Calculate function
	calcAnalysis, ok := analyzer.analysis["test.Calculate"]
	if !ok {
		t.Fatalf("analyzeFile(): missing analysis for test.Calculate")
	}

	if calcAnalysis.Package != "test" || calcAnalysis.Name != "Calculate" {
		t.Errorf("analyzeFile(): incorrect package/name for Calculate, got %s/%s, want test/Calculate",
			calcAnalysis.Package, calcAnalysis.Name)
	}

	// Calculate should have multiplication
	if calcAnalysis.OperationCosts[MUL] != gasCosts.MulCost {
		t.Errorf("analyzeFile(): Calculate function should have multiplication cost of %d, got %d",
			gasCosts.MulCost, calcAnalysis.OperationCosts[MUL])
	}

	// Calculate should call Add
	found := false
	if slices.Contains(calcAnalysis.Calls, "test.Add") {
		found = true
	}
	if !found {
		t.Errorf("analyzeFile(): Calculate function should call test.Add, got calls: %v", calcAnalysis.Calls)
	}

	analyzer.printAnalyses()
}

func TestAnalyzeIfStatement(t *testing.T) {
	srcCode := `
package test

func TestIf(a, b int) int {
	if a > b {
		return a + b
	} else if a < b {
		return a * b
	} else {
		return a - b
	}
}
`

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "test.go", srcCode, 0)
	if err != nil {
		t.Fatalf("Failed to parse test code: %v", err)
	}

	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	// Analyze the file
	analyzer.analyzeFile("test", file)

	// Get the analysis for TestIf
	analysis, ok := analyzer.analysis["test.TestIf"]
	if !ok {
		t.Fatalf("analyzeFile(): missing analysis for test.TestIf")
	}

	// TestIf should have addition, multiplication and subtraction
	ops := []struct {
		op   string
		cost int64
	}{
		{ADD, gasCosts.AddCost},
		{SUB, gasCosts.SubCost},
		{MUL, gasCosts.MulCost},
	}

	for _, op := range ops {
		if cost, exists := analysis.OperationCosts[op.op]; !exists || cost != op.cost {
			t.Errorf("analyzeIfStatement(): TestIf should have %s cost of %d, got %d (exists: %v)",
				op.op, op.cost, cost, exists)
		}
	}

	analyzer.printAnalyses()
}

func TestAnalyzeForStatement(t *testing.T) {
	srcCode := `
package test

func TestLoop(n int) int {
	sum := 0
	for i := 0; i < n; i++ {
		sum = sum + i * 2
	}
	return sum
}
`

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "test.go", srcCode, 0)
	if err != nil {
		t.Fatalf("Failed to parse test code: %v", err)
	}

	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	// Analyze the file
	analyzer.analyzeFile("test", file)

	// Get the analysis for TestLoop
	analysis, ok := analyzer.analysis["test.TestLoop"]
	if !ok {
		t.Fatalf("analyzeFile(): missing analysis for test.TestLoop")
	}

	// TestLoop should have addition and multiplication
	addCost, hasAddCost := analysis.OperationCosts[ADD]
	if !hasAddCost || addCost != gasCosts.AddCost {
		t.Errorf("analyzeForStatement(): TestLoop should have addition cost of %d, got %d (exists: %v)",
			gasCosts.AddCost, addCost, hasAddCost)
	}

	if analysis.OperationCosts[MUL] != gasCosts.MulCost {
		t.Errorf("analyzeForStatement(): TestLoop should have multiplication cost of %d, got %d",
			gasCosts.MulCost, analysis.OperationCosts[MUL])
	}

	analyzer.printAnalyses()
}

func TestAnalyzeRangeStatement(t *testing.T) {
	const src = `
package main

func iterate(values []int) int {
	sum := 0
	for _, v := range values {
		sum = sum + v
	}
	return sum
}

func main() {
	nums := []int{1, 2, 3, 4}
	iterate(nums)
}
`

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "test.go", src, 0)
	if err != nil {
		t.Fatalf("Failed to parse test code: %v", err)
	}

	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	analyzer.analyzeFile("main", file)

	if analyzer.analysis["main.iterate"].OperationCosts[IterNext] != gasCosts.IterNextCostFlat {
		t.Errorf("analyzeRangeStatement(): IterNext should have cost of %d, got %d",
			gasCosts.IterNextCostFlat, analyzer.analysis["main.iterate"].OperationCosts[IterNext])
	}

	if analyzer.analysis["main.iterate"].OperationCosts[ADD] != gasCosts.AddCost {
		t.Errorf("analyzeRangeStatement(): Add should have cost of %d, got %d", gasCosts.AddCost, analyzer.analysis["main.iterate"].OperationCosts[ADD])
	}

	analyzer.printAnalyses()
}

func TestBasicLit(t *testing.T) {
	const src = `
package main

func greet(name string) string {
	return "Hello, " + name
}

func main() {
	s := greet("World")
	println(s)
}
`

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "test.go", src, 0)
	if err != nil {
		t.Fatalf("Failed to parse test code: %v", err)
	}

	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	analyzer.analyzeFile("main", file)

	greetAnalysis, ok := analyzer.analysis["main.greet"]
	if !ok {
		t.Fatalf("analyzeFile(): main.greet is missing")
	}

	// string operation cost verification
	if greetAnalysis.OperationCosts[ADD] != gasCosts.AddCost {
		t.Errorf("greet function has wrong string operation cost. expected: %d, got: %d",
			gasCosts.AddCost, greetAnalysis.OperationCosts[ADD])
	}

	// main function analysis verification
	mainAnalysis, ok := analyzer.analysis["main.main"]
	if !ok {
		t.Fatalf("analyzeFile(): main.main is missing")
	}

	expectedCalls := []string{"main.greet", "main.println"}

	if mainAnalysis.OperationCosts[FunctionCall] != gasCosts.FunctionCallCost*int64(len(expectedCalls)) {
		t.Errorf("main function has wrong function call cost. expected: %d, got: %d",
			gasCosts.FunctionCallCost, mainAnalysis.OperationCosts[FunctionCall])
	}

	for _, call := range expectedCalls {
		if !slices.Contains(mainAnalysis.Calls, call) {
			t.Errorf("main function is missing call to %s", call)
		}
	}

	analyzer.printAnalyses()
}

func TestAnalyzeStatements(t *testing.T) {
	const src = `
package main

func greet(name string) string {
    return "Hello, " + name
}

func sum(arr []int) int {
    total := 0
    for i := 0; i < len(arr); i++ {
        total = total + arr[i]
    }
    return total
}

func main() {
    msg := greet("World")
    println(msg)
    nums := []int{1, 2, 3, 4}
    sum(nums)
}
`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "test.go", src, 0)
	if err != nil {
		t.Fatalf("Failed to parse test code: %v", err)
	}

	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)
	analyzer.analyzeFile("main", file)

	t.Run("greet function analysis", func(t *testing.T) {
		greetAnalysis, ok := analyzer.analysis["main.greet"]
		if !ok {
			t.Fatal("greet function analysis result is missing")
		}

		// string operation cost verification
		if greetAnalysis.OperationCosts[ADD] != gasCosts.AddCost {
			t.Errorf("string operation cost is wrong. expected: %d, got: %d",
				gasCosts.AddCost, greetAnalysis.OperationCosts[ADD])
		}

		// string literal value cost verification
		if _, exists := greetAnalysis.OperationCosts[ValueBytes]; !exists {
			t.Error("string literal value cost is not calculated")
		}
	})

	t.Run("sum function analysis", func(t *testing.T) {
		sumAnalysis, ok := analyzer.analysis["main.sum"]
		if !ok {
			t.Fatal("sum function analysis result is missing")
		}

		// array read cost verification
		if _, exists := sumAnalysis.OperationCosts[Read]; !exists {
			t.Error("array read cost is not calculated")
		}

		// addition operation cost verification
		if sumAnalysis.OperationCosts[ADD] != gasCosts.AddCost {
			t.Errorf("addition operation cost is wrong. expected: %d, got: %d",
				gasCosts.AddCost, sumAnalysis.OperationCosts[ADD])
		}

		// variable write cost verification (total variable)
		if _, exists := sumAnalysis.OperationCosts[Write]; !exists {
			t.Error("variable write cost is not calculated")
		}
	})
	t.Run("main function analysis", func(t *testing.T) {
		mainAnalysis, ok := analyzer.analysis["main.main"]
		if !ok {
			t.Fatal("main function analysis result is missing")
		}

		// function call cost verification
		expectedCalls := []string{"main.greet", "main.println", "main.sum"}
		for _, call := range expectedCalls {
			if !slices.Contains(mainAnalysis.Calls, call) {
				t.Errorf("function call %s is missing", call)
			}
		}

		// function call cost verification
		expectedCallCost := gasCosts.FunctionCallCost * int64(len(expectedCalls))
		if mainAnalysis.OperationCosts[FunctionCall] != expectedCallCost {
			t.Errorf("function call cost is wrong. expected: %d, got: %d",
				expectedCallCost, mainAnalysis.OperationCosts[FunctionCall])
		}

		// slice initialization cost verification
		if _, exists := mainAnalysis.OperationCosts[Write]; !exists {
			t.Error("slice initialization cost is not calculated")
		}
	})

	analyzer.printAnalyses()
}

func TestAnalyzeIndexExpression(t *testing.T) {
	const src = `
package main

func arrayAccess() {
    arr := make([]int, 5)
    arr[0] = 10 // write to array

    x := arr[1] // read from array

    arr[2] = arr[3] // read and write to array
}
`
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "test.go", src, 0)
	if err != nil {
		t.Fatalf("Failed to parse test code: %v", err)
	}

	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)
	analyzer.analyzeFile("main", file)

	analysis, ok := analyzer.analysis["main.arrayAccess"]
	if !ok {
		t.Fatal("arrayAccess function analysis result is missing")
	}

	t.Run("array access cost verification", func(t *testing.T) {
		// write cost verification
		writeCost, hasWrite := analysis.OperationCosts[Write]
		if !hasWrite {
			t.Error("array write cost is not calculated")
		}

		readCost, hasRead := analysis.OperationCosts[Read]
		if !hasRead {
			t.Error("array read cost is not calculated")
		}

		t.Logf("actual write cost: %d", writeCost)
		t.Logf("actual read cost: %d", readCost)

		minWriteOps := 3
		minReadOps := 2
		minWriteCost := gasCosts.WriteCostFlat * int64(minWriteOps)
		minReadCost := gasCosts.ReadCostFlat * int64(minReadOps)

		if writeCost < minWriteCost {
			t.Errorf("write cost is less than minimum expected value. expected: %d, got: %d",
				minWriteCost, writeCost)
		}
		if readCost < minReadCost {
			t.Errorf("read cost is less than minimum expected value. expected: %d, got: %d",
				minReadCost, readCost)
		}
	})

	analyzer.printAnalyses()
}

func TestFullAnalysis(t *testing.T) {
	srcCode := `
package complex

func Factorial(n int) int {
	if n <= 1 {
		return 1
	}
	return n * Factorial(n-1)
}

func Fibonacci(n int) int {
	if n <= 1 {
		return n
	}
	return Fibonacci(n-1) + Fibonacci(n-2)
}

func MathOperations(a, b int) int {
	// Use explicit expressions so analyzer can detect operations
	c := a + b
	c2 := a - b
	c3 := c * c2
	d := c3 / 2
	e := c3 % d
	f := a << 2
	g := b >> 1
	h := a & b
	i := a | b
	j := a ^ b
	k := ^a
	l := -b
	m := !true
	n := !false

	return e + f + g + h + i + j + k + l + m + n
}
`

	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "complex.go", srcCode, 0)
	if err != nil {
		t.Fatalf("Failed to parse test code: %v", err)
	}

	gasCosts := DefaultGasCost()
	analyzer := NewAnalyzer(fset, gasCosts)

	analyzer.analyzeFile("complex", file)

	// Check that all functions were analyzed
	functionNames := []string{"Factorial", "Fibonacci", "MathOperations"}
	for _, name := range functionNames {
		qualifiedName := "complex." + name
		if _, ok := analyzer.analysis[qualifiedName]; !ok {
			t.Errorf("fullAnalysis: missing analysis for %s", qualifiedName)
		}
	}

	// Check Factorial function
	factorial := analyzer.analysis["complex.Factorial"]
	if len(factorial.Calls) != 1 || factorial.Calls[0] != "complex.Factorial" {
		t.Errorf("fullAnalysis: Factorial should call itself, got calls: %v", factorial.Calls)
	}
	if factorial.OperationCosts[MUL] != gasCosts.MulCost {
		t.Errorf("fullAnalysis: Factorial should have multiplication cost, got: %d", factorial.OperationCosts["Mul"])
	}
	if factorial.OperationCosts[SUB] != gasCosts.SubCost {
		t.Errorf("fullAnalysis: Factorial should have subtraction cost, got: %d", factorial.OperationCosts["Sub"])
	}

	// Check Fibonacci function
	fibonacci := analyzer.analysis["complex.Fibonacci"]
	if len(fibonacci.Calls) != 2 {
		t.Errorf("fullAnalysis: Fibonacci should call itself twice, got calls: %v", fibonacci.Calls)
	}
	fibCalls := make(map[string]bool)
	for _, call := range fibonacci.Calls {
		fibCalls[call] = true
	}
	if !fibCalls["complex.Fibonacci"] {
		t.Errorf("fullAnalysis: Fibonacci should call itself, got calls: %v", fibonacci.Calls)
	}
	if fibonacci.OperationCosts[ADD] != gasCosts.AddCost {
		t.Errorf("fullAnalysis: Fibonacci should have addition cost, got: %d", fibonacci.OperationCosts["Add"])
	}
	if fibonacci.OperationCosts[SUB] != gasCosts.SubCost*2 {
		t.Errorf("fullAnalysis: Fibonacci should have two subtraction costs, got: %d", fibonacci.OperationCosts["Sub"])
	}

	// Check MathOperations function
	mathOps := analyzer.analysis["complex.MathOperations"]

	// All operations should be present
	expectedOps := map[string]int64{
		ADD: gasCosts.AddCost, // Addition operations
		SUB: gasCosts.SubCost, // Subtraction operations
		MUL: gasCosts.MulCost, // Multiplication operations
		DIV: gasCosts.DivCost, // Division operations
		MOD: gasCosts.ModCost, // Modulo operations
		SHL: gasCosts.ShlCost, // Shift left operations
		SHR: gasCosts.ShrCost, // Shift right operations
		AND: gasCosts.AndCost, // Bitwise AND operations
		OR:  gasCosts.OrCost,  // Bitwise OR operations
		XOR: gasCosts.XorCost, // Bitwise XOR operations
		NOT: gasCosts.NotCost, // Bitwise NOT operations
		NEG: gasCosts.NegCost, // Negation operations
	}

	for op, expectedCost := range expectedOps {
		if cost, exists := mathOps.OperationCosts[op]; !exists {
			t.Errorf("fullAnalysis: MathOperations missing operation: %s", op)
		} else if cost < expectedCost {
			// We don't check exact counts due to implementation details that might vary,
			// but we ensure that the operations are at least identified
			t.Errorf("fullAnalysis: MathOperations has unexpectedly low cost for %s: got %d, expected at least %d",
				op, cost, expectedCost)
		}
	}

	analyzer.printAnalyses()
}
