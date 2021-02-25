-- FNAM: lexit.lua
-- DESC: A Lua module. The module does lexical analysis; it is written as a hand-coded state machine.
-- AUTH: Timothy Albert Kline
--       Glenn G. Chappell       
-- CRSE: CS F331 - Programming Languages
-- PROF: Glenn G. Chappell
-- STRT: 15 February 2021
-- UPDT: 16 February 2021
-- VERS: 1.0 (based on v3.0 of lexer.lua)

-- Usage:
--
--    program = "print a+b;"  -- program to lex
--    for lexstr, cat in lexit.lex(program) do
--        -- lexstr is the string form of a lexeme.
--        -- cat is a number representing the lexeme category.
--        --  It can be used as an index for array lexer.catnames.
--    end


-- *********************************************************************
-- Module Table Initialization
-- *********************************************************************


local lexit = {}  -- Our module; members are added below


-- *********************************************************************
-- Public Constants
-- *********************************************************************


-- Numeric constants representing lexeme categories
lexit.KEY = 1
lexit.ID = 2
lexit.NUMLIT = 3
lexit.STRLIT = 4
lexit.OP = 5
lexit.PUNCT = 6
lexit.MAL = 7


-- catnames
-- Array of names of lexeme categories.
-- Human-readable strings. Indices are above numeric constants.
lexit.catnames = {
  "Keyword",
  "Identifier",
  "NumericLiteral",
  "StringLiteral",
  "Operator",
  "Punctuation",
  "Malformed"
}


-- *********************************************************************
-- Kind-of-Character Functions
-- *********************************************************************

-- All functions return false when given a string whose length is not
-- exactly 1.

-- isNotCharLength(c)
-- checks if the given string is not length 1
local function isNotCharLength(c)
  if c:len() ~= 1 then
      return true
  else
      return false
  end
end

-- isLetter
-- Returns true if string c is a letter character, false otherwise.
local function isLetter(c)
    if isNotCharLength(c) then
        return false
    elseif c >= "A" and c <= "Z" then
        return true
    elseif c >= "a" and c <= "z" then
        return true
    else
        return false
    end
end


-- isDigit
-- Returns true if string c is a digit character, false otherwise.
local function isDigit(c)
    if isNotCharLength(c) then
        return false
    elseif c >= "0" and c <= "9" then
        return true
    else
        return false
    end
end


-- isWhitespace
-- Returns true if string c is a whitespace character, false otherwise.
local function isWhitespace(c)
    if isNotCharLength(c) then
        return false
    elseif c == " " or c == "\t" or c == "\v" or c == "\n"
      or c == "\r" or c == "\f" then
        return true
    else
        return false
    end
end


-- isPrintableASCII
-- Returns true if string c is a printable ASCII character (codes 32 " "
-- through 126 "~"), false otherwise.
local function isPrintableASCII(c)
    if isNotCharLength(c) then
        return false
    elseif c >= " " and c <= "~" then
        return true
    else
        return false
    end
end


-- isIllegal
-- Returns true if string c is an illegal character, false otherwise.
local function isIllegal(c)
    if isNotCharLength(c) then
        return false
    elseif isWhitespace(c) then
        return false
    elseif isPrintableASCII(c) then
        return false
    else
        return true
    end
end

-- Set
-- A function for creating a set of items initializing to true
-- Sources:
-- http://lua-users.org/wiki/SetOperations
-- https://www.lua.org/pil/11.5.html
local function Set (list)
    local set = {}
    for _, v in pairs(list) do
        set[v] = true
    end
    return set
end

-- keywords
-- the list of reserved words in Caracal
local keywords = Set{
  "and", "char",
  "cr", "def",
  "dq", "elseif",
  "else", "false",
  "for", "if",
  "not", "or",
  "readnum", "return",
  "true", "write"
}

-- relOprChars
-- set of chars related to relational operators
local relOprChars = Set{
  "=",
  "!",
  "<",
  ">"
}

-- arithOprChars
-- set of chars related to arithmetic operators
local arithOprChars = Set{
  "+",
  "-",
  "*",
  "/",
  "%",
  "[",
  "]"
}

-- *********************************************************************
-- The Lexer
-- *********************************************************************


-- lex
-- Our lexer
-- Intended for use in a for-in loop:
--     for lexstr, cat in lexer.lex(program) do
-- Here, lexstr is the string form of a lexeme, and cat is a number
-- representing a lexeme category. (See Public Constants.)
function lexit.lex(program)
    -- ***** Variables (like class data members) *****

    local pos       -- Index of next character in program
                    -- INVARIANT: when getLexeme is called, pos is
                    --  EITHER the index of the first character of the
                    --  next lexeme OR program:len()+1
    local state     -- Current state for our state machine
    local ch        -- Current character
    local lexstr    -- The lexeme, so far
    local category  -- Category of lexeme, set when state set to DONE
    local handlers  -- Dispatch table; value created later

    -- ***** States *****

    local DONE   = 0
    local START  = 1
    local LETTER = 2
    local DIGIT  = 3
    local DIGEXPO = 4
    local EXPO    = 5
    local STRING = 6
    local RELOPR   = 7

    -- ***** Character-Related Utility Functions *****

    -- currChar
    -- Return the current character, at index pos in program. Return
    -- value is a single-character string, or the empty string if pos is
    -- past the end.
    local function currChar()
        return program:sub(pos, pos)
    end

    -- nextChar
    -- Return the next character, at index pos+1 in program. Return
    -- value is a single-character string, or the empty string if pos+1
    -- is past the end.
    local function nextChar()
        return program:sub(pos+1, pos+1)
    end

    -- drop1
    -- Move pos to the next character.
    local function drop1()
        pos = pos+1
    end
    
    -- Move pos to the previous character.
    local function fallback1()
        pos = pos-1
    end

    -- add1
    -- Add the current character to the lexeme, moving pos to the next
    -- character.
    local function add1()
        lexstr = lexstr .. currChar()
        drop1()
    end

    -- skipWhitespace
    -- Skip whitespace and comments, moving pos to the beginning of
    -- the next lexeme, or to program:len()+1.
    local function skipWhitespace()
        while true do
            -- Skip whitespace characters
            while isWhitespace(currChar()) do
                drop1()
            end

            -- Done if no comment
            if currChar() ~= "#" then
                break
            end

            -- Skip comment
            drop1()  -- Drop leading "#"
            while true do
                if currChar() == "\n" then
                    drop1()  -- Drop trailing "\n"
                    break
                elseif currChar() == "" then  -- End of input?
                   return
                end
                drop1()  -- Drop character inside comment
            end
        end
    end

    -- ***** State-Handler Functions *****

    -- A function with a name like handle_XYZ is the handler function
    -- for state XYZ

    -- State DONE: lexeme is done; this handler should not be called.
    local function handle_DONE()
        error("'DONE' state should not be handled\n")
    end

    -- State EQLRELT: no character read yet.
    local function handle_START()
        if isIllegal(ch) then
            add1()
            state = DONE
            category = lexit.MAL
        elseif isLetter(ch) or ch == "_" then
            add1()
            state = LETTER
        elseif isDigit(ch) then
            add1()
            state = DIGIT
        elseif ch == "\"" then
            add1()
            state = STRING
        elseif relOprChars[ch] then
            add1()
            state = RELOPR
        elseif arithOprChars[ch] then
            add1()
            state = DONE
            category = lexit.OP
        else
            add1()
            state = DONE
            category = lexit.PUNCT
        end
    end

    -- State LETTER: we are in an ID.
    local function handle_LETTER()
        if isLetter(ch) or ch == "_" or isDigit(ch) then
            add1()
        else
            state = DONE
              if keywords[lexstr] then
                  category = lexit.KEY
              else
                  category = lexit.ID
              end
        end
    end

    -- State DIGIT: we are in a NUMLIT, and we have NOT seen "e" or "E".
    local function handle_DIGIT()
        if isDigit(ch) then
            add1()
        elseif ch == "e" or ch == "E" then
            state = EXPO
        else
            state = DONE
            category = lexit.NUMLIT
        end
    end

    -- State DIGEXPO: we are in a NUMLIT, and we have seen "e", "E", "E+", or "e+".
    local function handle_DIGEXPO()
        if isDigit(ch) then
            add1()
        else
            state = DONE
            category = lexit.NUMLIT
        end
    end

    -- State EXPO: we have seen an EXPO ("e" or "E") from a NUMLIT.
    local function handle_EXPO() -- pos is looking at "e"
        if isDigit(nextChar()) then
            add1() -- .."E" or "e"
            state = DIGEXPO
        elseif nextChar() == "+" then
            drop1() --look ahead
            if isDigit(nextChar()) then
                fallback1()
                add1() -- .."e" or "E"
                add1() -- .."+"
                state = DIGEXPO
            else
                fallback1()
                state = DONE
                category = lexit.NUMLIT
            end
        else
            state = DONE
            category = lexit.NUMLIT
        end
    end

    -- State STRING: We have seen a "\"" and we are in a STRLIT
    local function handle_STRING()
        if ch == "\"" then
            add1()
            state = DONE
            category = lexit.STRLIT
        elseif ch == "\n" or ch == "" then -- an ending "\"" is never found
            state = DONE
            category = lexit.MAL
        else -- concatenate the string
           add1()
        end
    end
    
    --State RELOPR: We are in an OP and we have seen <, >, =, or !
    local function handle_RELOPR()
        if ch == "=" then
          add1()
          state = DONE
          category = lexit.OP
        elseif lexstr == "!" then
          state = DONE
          category = lexit.PUNCT
        else
          state = DONE
          category = lexit.OP
        end
    end
    
    
    -- ***** Table of State-Handler Functions *****

    handlers = {
        [DONE]=handle_DONE,
        [START]=handle_START,
        [LETTER]=handle_LETTER,
        [DIGIT]=handle_DIGIT,
        [DIGEXPO]=handle_DIGEXPO,
        [EXPO]=handle_EXPO,
        [STRING]=handle_STRING,
        [RELOPR]=handle_RELOPR
    }

    -- ***** Iterator Function *****

    -- getLexeme
    -- Called each time through the for-in loop.
    -- Returns a pair: lexeme-string (string) and category (int), or
    -- nil, nil if no more lexemes.
    local function getLexeme(dummy1, dummy2)
        if pos > program:len() then
            return nil, nil
        end
        lexstr = ""
        state = START
        while state ~= DONE do
            ch = currChar()
            handlers[state]()
        end

        skipWhitespace()
        return lexstr, category
    end

    -- ***** Body of Function lex *****

    -- Initialize & return the iterator function
    pos = 1
    skipWhitespace()
    return getLexeme, nil, nil
end


---EXAMP. USE/TEST
--[==[
program = "!=1"

for lexstr, cat in lexit.lex(program) do
    print(lexstr, lexit.catnames[cat])
end
--]==]

-- *********************************************************************
-- Module Table Return
-- *********************************************************************
return lexit


