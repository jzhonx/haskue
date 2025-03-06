package main

import (
    "flag"
    "fmt"
    "os"
    "path/filepath"

    "golang.org/x/tools/txtar"
)

// writeFirstTxtarFile reads a txtar file from sourcePath and writes its first file to destPath
func writeFirstTxtarFile(sourcePath, destPath string) error {
    // Read the entire txtar file
    data, err := os.ReadFile(sourcePath)
    if err != nil {
        return fmt.Errorf("failed to read txtar file: %v", err)
    }

    // Parse the txtar archive
    archive := txtar.Parse(data)
    if len(archive.Files) == 0 {
        return fmt.Errorf("txtar file contains no files")
    }

    // Get the first file
    firstFile := archive.Files[0]

    // Ensure destination directory exists
    destDir := filepath.Dir(destPath)
    if err := os.MkdirAll(destDir, 0755); err != nil {
        return fmt.Errorf("failed to create destination directory: %v", err)
    }

    // Write the first file to the destination path
    err = os.WriteFile(destPath, firstFile.Data, 0644)
    if err != nil {
        return fmt.Errorf("failed to write output file: %v", err)
    }

    fmt.Printf("Successfully wrote '%s' to %s\n", firstFile.Name, destPath)
    return nil
}

func main() {
    // Define flags
    sourcePath := flag.String("input", "", "path to the source txtar file")
    destPath := flag.String("output", "", "destination path for the first file")

    // Parse flags
    flag.Parse()

    // Validate that both flags are provided
    if *sourcePath == "" || *destPath == "" {
        fmt.Fprintf(os.Stderr, "Error: both source and destination paths are required\n")
        fmt.Fprintf(os.Stderr, "Usage: %s -source <txtar-source-path> -dest <destination-path>\n", os.Args[0])
        flag.PrintDefaults()
        os.Exit(1)
    }

    // Execute the function
    if err := writeFirstTxtarFile(*sourcePath, *destPath); err != nil {
        fmt.Fprintf(os.Stderr, "Error: %v\n", err)
        os.Exit(1)
    }
}
