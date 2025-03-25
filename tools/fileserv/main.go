package main

import (
	"flag"
	"fmt"
	"log"
	"net/http"
	"path/filepath"
)

func main() {
	port := flag.Int("port", 8080, "Port to serve the file on")
	filePath := flag.String("file", "", "File to serve")
	flag.Parse()

	if *filePath == "" {
		log.Fatal("Usage: fileserver -file=<file> [options]")
	}

	absPath, err := filepath.Abs(*filePath)
	if err != nil {
		log.Fatalf("Error getting absolute path: %v", err)
	}

	fileName := filepath.Base(absPath)
	http.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path != "/"+fileName {
			http.NotFound(w, r)
			return
		}
		http.ServeFile(w, r, absPath)
	})

	url := fmt.Sprintf("http://localhost:%d/%s", *port, fileName)
	fmt.Printf("Serving %s at %s\n", absPath, url)

	log.Fatal(http.ListenAndServe(fmt.Sprintf(":%d", *port), nil))
}
