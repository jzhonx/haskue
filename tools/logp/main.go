package main

import (
    "bufio"
    "flag"
    "fmt"
    "os"
    "regexp"
    "strings"
)

func main() {
    // Define command-line flags for input and output file paths
    inputFilePath := flag.String("input", "", "Path to the input log file")
    outputFilePath := flag.String("output", "output.md", "Path to the output Markdown file")

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

    // Create the output file
    outputFile, err := os.Create(*outputFilePath)
    if err != nil {
        fmt.Println("Error creating output file:", err)
        return
    }
    defer outputFile.Close()

    scanner := bufio.NewScanner(inputFile)
    debugRegex := regexp.MustCompile(`^\[Debug\]\s+(.*)`)

    insideCodeBlock := true
    outputFile.WriteString("```\n")

    for scanner.Scan() {
        line := scanner.Text()

        // Match lines starting with [Debug]
        match := debugRegex.FindStringSubmatch(line)
        if len(match) > 0 {
            outputFile.WriteString(fmt.Sprintf("%s\n", match[1]))
        } else {
          if strings.Contains(line, "```mermaid") {
            if insideCodeBlock {
                // Close the previous code block if open
                outputFile.WriteString("```\n")
                insideCodeBlock = false
            }
            insideCodeBlock = false
          } 
          // Write normal log lines into the markdown file
          outputFile.WriteString(line + "\n")
          if strings.Contains(line, "```") && !strings.Contains(line, "```mermaid") {
              insideCodeBlock = true
              outputFile.WriteString("```\n")
          }
        }
    }

    // Close any open code block
    if insideCodeBlock {
        outputFile.WriteString("```\n")
    }

    if err := scanner.Err(); err != nil {
        fmt.Println("Error reading input file:", err)
    }

    fmt.Println("Log converted to Markdown:", *outputFilePath)
}

