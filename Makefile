
# this is the name of the main maude module
LANGUAGE_NAME = KWALA

# this is the name of the interesting modules (used by make latex/pdf) 
LANGUAGE_MODULES = KWALA-SYNTAX KWALA

# this is the basename of the main file
MAIN_FILE = kwala

TOOL_DIR =  $(K_BASE)/tools/
include $(TOOL_DIR)make-helper.mk
