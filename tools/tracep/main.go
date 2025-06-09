package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"regexp"
)

func main() {
	// Define command-line flags for input and output file paths
	inputFilePath := flag.String("input", "", "Path to the input log file")
	outputFilePath := flag.String("output", "trace.json", "Path to the output JSON file")

	// Parse the flags
	flag.Parse()

	// Ensure input file is provided
	if *inputFilePath == "" {
		fmt.Println("Error: Input file path is required. Use -input flag to specify it.")
		return
	}

	// Open the input file
	inputFile, err := os.Open(*inputFilePath)
	if err != nil {
		fmt.Println("Error opening input file:", err)
		return
	}
	defer inputFile.Close()

	scanner := bufio.NewScanner(inputFile)
	debugRegex := regexp.MustCompile(`^ChromeTrace(.*)`)

	// Increase buffer size to handle long lines
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024) // Set max token size to 1MB

	traceList := []any{}

	for scanner.Scan() {
		line := scanner.Text()

		// Match lines starting with [Debug] ChromeTrace
		match := debugRegex.FindStringSubmatch(line)
		if len(match) == 0 {
			continue
		}

		var v any
		err := json.Unmarshal([]byte(match[1]), &v)
		if err != nil {
			fmt.Println("Error unmarshalling JSON:", err)
			os.Exit(1)
		}
		traceList = append(traceList, v)
	}

	if err := scanner.Err(); err != nil {
		fmt.Println("Error reading input file:", err)
	}

	// Create the output file
	outputFile, err := os.Create(*outputFilePath)
	if err != nil {
		fmt.Println("Error creating output file:", err)
		os.Exit(1)
	}
	defer outputFile.Close()

	// Write the trace list to the output file in JSON format
	encoder := json.NewEncoder(outputFile)
	err = encoder.Encode(traceList)
	if err != nil {
		fmt.Println("Error writing to output file:", err)
		os.Exit(1)
	}

	fmt.Println("Log converted to Trace JSON:", *outputFilePath)
}
