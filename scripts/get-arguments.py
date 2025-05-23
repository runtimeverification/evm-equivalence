import re
import argparse

def arguments(text : str) -> str:
    return ' '.join(re.findall(r'\{([a-zA-Z0-9_\ ]+)\ :', text))

if __name__ == "__main__":
	parser = argparse.ArgumentParser(description="Extract text from curly brackets")
	parser.add_argument("file_path", help="The path to the file containing the text")
	args = parser.parse_args()

	try:
	    with open(args.file_path, "r") as file:
	        text = file.read()
	        print(arguments(text))
	except FileNotFoundError:
	    print(f"Error: The file '{args.file_path}' does not exist")
	except Exception as e:
	    print(f"An error occurred: {e}")
