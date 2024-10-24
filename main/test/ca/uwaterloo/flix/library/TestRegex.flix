/*
 *  Copyright 2023 Stephen Tetley
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

mod TestRegex {

    /////////////////////////////////////////////////////////////////////////////
    // Pattern.toString                                                        //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def toString01(): Bool =
        ToString.toString(Regex.unmatchable()) != ""

    /////////////////////////////////////////////////////////////////////////////
    // compile                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def compile01(): Bool =
        Regex.compile("\\p{Alpha}+") |> Result.isOk

    @test
    def compile02(): Bool =
        Regex.compile("\\p{Alpha+") |> Result.isErr

    /////////////////////////////////////////////////////////////////////////////
    // compileWithFlags                                                        //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def compileWithFlags01(): Bool =
        use Regex.Flag.{CaseInsenstive};
        Regex.compileWithFlags("\\p{Alpha}+", Set#{CaseInsenstive}) |> Result.isOk

    @test
    def compileWithFlags02(): Bool =
        use Regex.Flag.{CaseInsenstive};
        Regex.compileWithFlags("\\p{Alpha+", Set#{CaseInsenstive}) |> Result.isErr


    @test
    def compileWithFlags03(): Bool =
        use Regex.Flag.{CaseInsenstive, Multiline};
        Regex.compileWithFlags("\\p{Alpha}+", Set#{CaseInsenstive, Multiline}) |> Result.isOk


    /////////////////////////////////////////////////////////////////////////////
    // unmatchable                                                             //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def unmatchable01(): Bool =
        Regex.unmatchable() |> Regex.pattern == "^\\b$"

    /////////////////////////////////////////////////////////////////////////////
    // quote                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def quote01(): Bool =
        Regex.quote("ab") == "\\Qab\\E"

    @test
    def quote02(): Bool =
        Regex.quote("a*b") == "\\Qa*b\\E"

    /////////////////////////////////////////////////////////////////////////////
    // pattern                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def pattern01(): Bool =
        Result.map(Regex.pattern, Regex.compile("a*b")) == Ok("a*b")

    @test
    def pattern02(): Bool =
        Result.map(Regex.pattern, Regex.compile("\\p{Blank}+")) == Ok("\\p{Blank}+")

    /////////////////////////////////////////////////////////////////////////////
    // flags                                                                   //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def flags01(): Bool =
        Result.map(Regex.flags, Regex.compile("\\p{Blank}+")) == Ok(Set#{})

    @test
    def flags02(): Bool =
        Result.map(Regex.flags, Regex.compileWithFlags("\\p{Blank}+", Set#{})) == Ok(Set#{})

    @test
    def flags03(): Bool =
        use Regex.Flag.{CaseInsenstive};
        Result.map(Regex.flags, Regex.compileWithFlags("\\p{Blank}", Set#{CaseInsenstive})) == Ok(Set#{CaseInsenstive})

    @test
    def flags04(): Bool =
        use Regex.Flag.{CaseInsenstive, Multiline};
        Result.map(Regex.flags, Regex.compileWithFlags("\\p{Blank}", Set#{CaseInsenstive, Multiline})) == Ok(Set#{CaseInsenstive, Multiline})

    /////////////////////////////////////////////////////////////////////////////
    // isMatch                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def isMatch01(): Bool =
        Result.map(patt -> Regex.isMatch(patt, ""),
            Regex.compile("a+")) == Ok(false)

    @test
    def isMatch02(): Bool =
        Result.map(patt -> Regex.isMatch(patt, ""),
            Regex.compile("a*")) == Ok(true)

    @test
    def isMatch03(): Bool =
        Result.map(patt -> Regex.isMatch(patt, "a"),
            Regex.compile("a*")) == Ok(true)

    @test
    def isMatch04(): Bool =
        Result.map(patt -> Regex.isMatch(patt, "aa"),
            Regex.compile("a*")) == Ok(true)

    @test
    def isMatch05(): Bool =
        Result.map(patt -> Regex.isMatch(patt, "aab"),
            Regex.compile("a*")) == Ok(false)

    @test
    def isMatch06(): Bool =
        Result.map(patt -> Regex.isMatch(patt, "aab"),
            Regex.compile("a*b")) == Ok(true)

    /////////////////////////////////////////////////////////////////////////////
    // isMatch                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def isSubmatch01(): Bool =
        Result.map(patt -> Regex.isSubmatch(patt, ""),
            Regex.compile("a+")) == Ok(false)

    @test
    def isSubmatch02(): Bool =
        Result.map(patt -> Regex.isSubmatch(patt, "a"),
            Regex.compile("a*")) == Ok(true)

    @test
    def isSubmatch03(): Bool =
        Result.map(patt -> Regex.isSubmatch(patt, "aa"),
            Regex.compile("a*")) == Ok(true)

    @test
    def isSubmatch04(): Bool =
        Result.map(patt -> Regex.isSubmatch(patt, "aab"),
            Regex.compile("a*")) == Ok(true)

    @test
    def isSubmatch05(): Bool =
        Result.map(patt -> Regex.isSubmatch(patt, "aab"),
            Regex.compile("a*b")) == Ok(true)

    @test
    def isSubmatch06(): Bool =
        Result.map(patt -> Regex.isSubmatch(patt, "aab"),
            Regex.compile("b+")) == Ok(true)

    @test
    def isSubmatch07(): Bool =
        Result.map(patt -> Regex.isSubmatch(patt, "bbbc"),
            Regex.compile("b+")) == Ok(true)

    @test
    def isSubmatch08(): Bool =
        Result.map(patt -> Regex.isSubmatch(patt, "aabbbc"),
            Regex.compile("b+")) == Ok(true)

    /////////////////////////////////////////////////////////////////////////////
    // indices                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def indices01(): Bool =
        Regex.indices(substr = Regex.unmatchable(), "") == List#{}

    @test
    def indices02(): Bool =
        Regex.indices(substr = Regex.unmatchable(), "a::b::c") == List#{}

    @test
    def indices03(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, ""),
            Regex.compile(":{2}")) == Ok(List#{})

    @test
    def indices04(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "a"),
            Regex.compile(":{2}")) == Ok(List#{})

    @test
    def indices05(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "::"),
            Regex.compile(":{2}")) == Ok(List#{0})

    @test
    def indices06(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "ab"),
            Regex.compile(":{2}")) == Ok(List#{})

    @test
    def indices07(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "::a"),
            Regex.compile(":{2}")) == Ok(List#{0})

    @test
    def indices08(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "a::"),
            Regex.compile(":{2}")) == Ok(List#{1})

    @test
    def indices09(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "a::b::"),
            Regex.compile(":{2}")) == Ok(List#{1, 4})

    @test
    def indices10(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "a::b::c"),
            Regex.compile(":{2}")) == Ok(List#{1, 4})

    @test
    def indices11(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "a::b::c:"),
            Regex.compile(":{2}")) == Ok(List#{1, 4})

    @test
    def indices12(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, ":a::b::c"),
            Regex.compile(":{2}")) == Ok(List#{2, 5})

    @test
    def indices13(): Bool =
        Result.map(patt -> Regex.indices(substr = patt, "::::"),
            Regex.compile(":{2}")) == Ok(List#{0, 2})


    /////////////////////////////////////////////////////////////////////////////
    // submatches                                                              //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def submatches01(): Bool =
        Regex.submatches(substr = Regex.unmatchable(), "") == List#{}

    @test
    def submatches02(): Bool =
        Regex.submatches(substr = Regex.unmatchable(), "a::b::c") == List#{}

    @test
    def submatches03(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{})

    @test
    def submatches04(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "a"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{"a"})

    @test
    def submatches05(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "::"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{})

    @test
    def submatches06(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{"ab"})

    @test
    def submatches07(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "::a"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{"a"})

    @test
    def submatches08(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "a::"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{"a"})

    @test
    def submatches09(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "a::b::"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{"a", "b"})

    @test
    def submatches10(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "a::b::c"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{"a", "b", "c"})

    @test
    def submatches11(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "a::b::c:"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{"a", "b", "c"})

    @test
    def submatches12(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, ":a::b::c"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{"a", "b", "c"})

    @test
    def submatches13(): Bool =
        Result.map(patt -> Regex.submatches(substr = patt, "::::"),
            Regex.compile("\\p{Alpha}+")) == Ok(List#{})


    /////////////////////////////////////////////////////////////////////////////
    // countSubmatches                                                         //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def countSubmatches01(): Bool =
        Regex.countSubmatches(substr = Regex.unmatchable(), "") == 0

    @test
    def countSubmatches02(): Bool =
        Regex.countSubmatches(substr = Regex.unmatchable(), "a::b::c") == 0

    @test
    def countSubmatches03(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(0)

    @test
    def countSubmatches04(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "a"),
            Regex.compile("\\p{Alpha}+")) == Ok(1)

    @test
    def countSubmatches05(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "::"),
            Regex.compile("\\p{Alpha}+")) == Ok(0)

    @test
    def countSubmatches06(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(1)

    @test
    def countSubmatches07(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "::a"),
            Regex.compile("\\p{Alpha}+")) == Ok(1)

    @test
    def countSubmatches08(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "a::"),
            Regex.compile("\\p{Alpha}+")) == Ok(1)

    @test
    def countSubmatches09(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "a::b::"),
            Regex.compile("\\p{Alpha}+")) == Ok(2)

    @test
    def countSubmatches10(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "a::b::c"),
            Regex.compile("\\p{Alpha}+")) == Ok(3)

    @test
    def countSubmatches11(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "a::b::c:"),
            Regex.compile("\\p{Alpha}+")) == Ok(3)

    @test
    def countSubmatches12(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, ":a::b::c"),
            Regex.compile("\\p{Alpha}+")) == Ok(3)

    @test
    def countSubmatches13(): Bool =
        Result.map(patt -> Regex.countSubmatches(substr = patt, "::::"),
            Regex.compile("\\p{Alpha}+")) == Ok(0)

    /////////////////////////////////////////////////////////////////////////////
    // split                                                                   //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def split01(): Bool =
        Result.map(patt -> Regex.split(pattern = patt, "A B C"),
            Regex.compile("\\p{Blank}+")) == Ok(List#{"A", "B", "C"})

    @test
    def split02(): Bool =
        Result.map(patt -> Regex.split(pattern = patt, "A  B   C"),
            Regex.compile("\\p{Blank}+")) == Ok(List#{"A", "B", "C"})

    @test
    def split03(): Bool =
        Result.map(patt -> Regex.split(pattern = patt, "ABC"),
            Regex.compile("\\p{Blank}+")) == Ok(List#{"ABC"})

    /////////////////////////////////////////////////////////////////////////////
    // replace                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def replace01(): Bool =
        Result.map(patt -> Regex.replace(from = patt, to = "_", ""),
            Regex.compile("\\p{Blank}+")) == Ok("")

    @test
    def replace02(): Bool =
        Result.map(patt -> Regex.replace(from = patt, to = "_", "A B C"),
            Regex.compile("\\p{Blank}+")) == Ok("A_B_C")

    @test
    def replace03(): Bool =
        Result.map(patt -> Regex.replace(from = patt, to = "_", "A  B   C"),
            Regex.compile("\\p{Blank}+")) == Ok("A_B_C")

    @test
    def replace04(): Bool =
        Result.map(patt -> Regex.replace(from = patt, to = "_", "ABC"),
            Regex.compile("\\p{Blank}+")) == Ok("ABC")

    @test
    def replace05(): Bool =
        Result.map(patt -> Regex.replace(from = patt, to = "__", "A B  C"),
            Regex.compile("\\p{Blank}+")) == Ok("A__B__C")

    @test
    def replace06(): Bool =
        Result.map(patt -> Regex.replace(from = patt, to = "__", " A B  C  "),
            Regex.compile("\\p{Blank}+")) == Ok("__A__B__C__")

    /////////////////////////////////////////////////////////////////////////////
    // replaceFirst                                                            //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def replaceFirst01(): Bool =
        Result.map(patt -> Regex.replaceFirst(from = patt, to = "_", ""),
            Regex.compile("\\p{Blank}+")) == Ok("")

    @test
    def replaceFirst02(): Bool =
        Result.map(patt -> Regex.replaceFirst(from = patt, to = "_", "A B C"),
            Regex.compile("\\p{Blank}+")) == Ok("A_B C")

    @test
    def replaceFirst03(): Bool =
        Result.map(patt -> Regex.replaceFirst(from = patt, to = "_", "A  B   C"),
            Regex.compile("\\p{Blank}+")) == Ok("A_B   C")

    @test
    def replaceFirst04(): Bool =
        Result.map(patt -> Regex.replaceFirst(from = patt, to = "_", "ABC"),
            Regex.compile("\\p{Blank}+")) == Ok("ABC")

    @test
    def replaceFirst05(): Bool =
        Result.map(patt -> Regex.replaceFirst(from = patt, to = "__", "A B  C"),
            Regex.compile("\\p{Blank}+")) == Ok("A__B  C")

    @test
    def replaceFirst06(): Bool =
        Result.map(patt -> Regex.replaceFirst(from = patt, to = "__", " A B  C  "),
            Regex.compile("\\p{Blank}+")) == Ok("__A B  C  ")

    /////////////////////////////////////////////////////////////////////////////
    // startsWith                                                              //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def startsWith01(): Bool =
        Regex.startsWith(prefix = Regex.unmatchable(), "") == false

    @test
    def startsWith02(): Bool =
        Regex.startsWith(prefix = Regex.unmatchable(), "A B C") == false

    @test
    def startsWith03(): Bool =
        Result.map(patt -> Regex.startsWith(prefix = patt, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(false)

    @test
    def startsWith04(): Bool =
        Result.map(patt -> Regex.startsWith(prefix = patt, "   A B C"),
            Regex.compile("\\p{Alpha}+")) == Ok(false)

    @test
    def startsWith05(): Bool =
        Result.map(patt -> Regex.startsWith(prefix = patt, "A B C"),
            Regex.compile("\\p{Alpha}+")) == Ok(true)

    @test
    def startsWith06(): Bool =
        Result.map(patt -> Regex.startsWith(prefix = patt, "AA BBB CCCC"),
            Regex.compile("\\p{Alpha}+")) == Ok(true)

    /////////////////////////////////////////////////////////////////////////////
    // endsWith                                                                //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def endsWith01(): Bool =
        Regex.endsWith(suffix = Regex.unmatchable(), "") == false

    @test
    def endsWith02(): Bool =
        Regex.endsWith(suffix = Regex.unmatchable(), "A B C") == false

    @test
    def endsWith03(): Bool =
        Result.map(patt -> Regex.endsWith(suffix = patt, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(false)

    @test
    def endsWith04(): Bool =
        Result.map(patt -> Regex.endsWith(suffix = patt, "A B C  "),
            Regex.compile("\\p{Alpha}+")) == Ok(false)
    @test
    def endsWith05(): Bool =
        Result.map(patt -> Regex.endsWith(suffix = patt, "A B C"),
            Regex.compile("\\p{Alpha}+")) == Ok(true)
    @test
    def endsWith06(): Bool =
        Result.map(patt -> Regex.endsWith(suffix = patt, "AA BBB CCCC"),
            Regex.compile("\\p{Alpha}+")) == Ok(true)

    /////////////////////////////////////////////////////////////////////////////
    // stripPrefix                                                             //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def stripPrefix01(): Bool =
        Regex.stripPrefix(substr = Regex.unmatchable(), "") == None

    @test
    def stripPrefix02(): Bool =
        Regex.stripPrefix(substr = Regex.unmatchable(), "A B C") == None

    @test
    def stripPrefix03(): Bool =
        Result.map(patt -> Regex.stripPrefix(substr = patt, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def stripPrefix04(): Bool =
        Result.map(patt -> Regex.stripPrefix(substr = patt, "   A B C"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def stripPrefix05(): Bool =
        Result.map(patt -> Regex.stripPrefix(substr = patt, "A B C"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(" B C"))

    @test
    def stripPrefix06(): Bool =
        Result.map(patt -> Regex.stripPrefix(substr = patt, "AA BBB CCCC"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(" BBB CCCC"))

    /////////////////////////////////////////////////////////////////////////////
    // stripSuffix                                                             //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def stripSuffix01(): Bool =
        Regex.stripSuffix(substr = Regex.unmatchable(), "") == None

    @test
    def stripSuffix02(): Bool =
        Regex.stripSuffix(substr = Regex.unmatchable(), "A B C") == None

    @test
    def stripSuffix03(): Bool =
        Result.map(patt -> Regex.stripSuffix(substr = patt, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def stripSuffix04(): Bool =
        Result.map(patt -> Regex.stripSuffix(substr = patt, "A B C  "),
            Regex.compile("\\p{Alpha}+")) == Ok(None)
    @test
    def stripSuffix05(): Bool =
        Result.map(patt -> Regex.stripSuffix(substr = patt, "A B C"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some("A B "))
    @test
    def stripSuffix06(): Bool =
        Result.map(patt -> Regex.stripSuffix(substr = patt, "AA BBB CCCC"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some("AA BBB "))

    /////////////////////////////////////////////////////////////////////////////
    // indexOfFirst                                                            //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def indexOfFirst01(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfFirst02(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, "_"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfFirst03(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, "a"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfFirst04(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, "__"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfFirst05(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, "ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfFirst06(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, "_b"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(1))

    @test
    def indexOfFirst07(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, "ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfFirst08(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, "ab_"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfFirst09(): Bool =
        Result.map(patt -> Regex.indexOfFirst(substr = patt, "_bc"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(1))

    /////////////////////////////////////////////////////////////////////////////
    // indexOfLast                                                             //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def indexOfLast01(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLast02(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, "_"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLast03(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, "a"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfLast04(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, "__"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLast05(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, "a_"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfLast06(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, "_b"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(1))

    @test
    def indexOfLast07(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, "aa"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfLast08(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, "ab"),
            Regex.compile("\\p{Alpha}{2}")) == Ok(Some(0))

    @test
    def indexOfLast09(): Bool =
        Result.map(patt -> Regex.indexOfLast(substr = patt, "abcd"),
            Regex.compile("\\p{Alpha}{2}")) == Ok(Some(2))

    /////////////////////////////////////////////////////////////////////////////
    // indexOfFirstWithOffset                                                   //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def indexOfFirstWithOffset01(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 0, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfFirstWithOffset02(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 0, "_"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfFirstWithOffset03(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 0, "a"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfFirstWithOffset04(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 1, "a"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfFirstWithOffset05(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 0, "ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfFirstWithOffset06(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 1, "aa"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(1))

    @test
    def indexOfFirstWithOffset07(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 0, "_b"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(1))

    @test
    def indexOfFirstWithOffset08(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 0, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfFirstWithOffset09(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 1, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(1))

    @test
    def indexOfFirstWithOffset10(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 2, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(3))

    @test
    def indexOfFirstWithOffset11(): Bool =
        Result.map(patt -> Regex.indexOfFirstWithOffset(substr = patt, offset = 3, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(3))

    /////////////////////////////////////////////////////////////////////////////
    // indexOfLastWithOffset                                                   //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def indexOfLastWithOffset01(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 0, ""),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLastWithOffset02(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 0, "_"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLastWithOffset03(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 0, "a"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(0))

    @test
    def indexOfLastWithOffset04(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 1, "a"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLastWithOffset05(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 1, "ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(1))

    @test
    def indexOfLastWithOffset06(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 2, "aa"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLastWithOffset07(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 3, "ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLastWithOffset08(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 3, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(3))

    @test
    def indexOfLastWithOffset09(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset= 2, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(3))

    @test
    def indexOfLastWithOffset10(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 1, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(3))

    @test
    def indexOfLastWithOffset11(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 0, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(Some(3))

    @test
    def indexOfLastWithOffset12(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = -1, "ab ab"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    @test
    def indexOfLastWithOffset13(): Bool =
        Result.map(patt -> Regex.indexOfLastWithOffset(substr = patt, offset = 2, "ab __"),
            Regex.compile("\\p{Alpha}+")) == Ok(None)

    /////////////////////////////////////////////////////////////////////////////
    // breakOnFirst                                                            //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def breakOnFirst01(): Bool =
        Result.map(patt -> Regex.breakOnFirst(substr = patt, ""),
            Regex.compile(":{2}")) == Ok(("", ""))

    @test
    def breakOnFirst02(): Bool =
        Result.map(patt -> Regex.breakOnFirst(substr = patt, "aaa"),
            Regex.compile(":{2}")) == Ok(("aaa", ""))

    @test
    def breakOnFirst03(): Bool =
        Result.map(patt -> Regex.breakOnFirst(substr = patt, "::"),
            Regex.compile(":{2}")) == Ok(("", "::"))

    @test
    def breakOnFirst04(): Bool =
        Result.map(patt -> Regex.breakOnFirst(substr = patt, "::aaa"),
            Regex.compile(":{2}")) == Ok(("", "::aaa"))

    @test
    def breakOnFirst05(): Bool =
        Result.map(patt -> Regex.breakOnFirst(substr = patt, "aaa:"),
            Regex.compile(":{2}")) == Ok(("aaa:", ""))

    @test
    def breakOnFirst06(): Bool =
        Result.map(patt -> Regex.breakOnFirst(substr = patt, "aaa::"),
            Regex.compile(":{2}")) == Ok(("aaa", "::"))

    @test
    def breakOnFirst07(): Bool =
        Result.map(patt -> Regex.breakOnFirst(substr = patt, "aaa::bbb"),
            Regex.compile(":{2}")) == Ok(("aaa", "::bbb"))

    @test
    def breakOnFirst08(): Bool =
        Result.map(patt -> Regex.breakOnFirst(substr = patt, "aaa::bbb::ccc"),
            Regex.compile(":{2}")) == Ok(("aaa", "::bbb::ccc"))

    /////////////////////////////////////////////////////////////////////////////
    // breakAfterFirst                                                         //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def breakAfterFirst01(): Bool =
        Result.map(patt -> Regex.breakAfterFirst(substr = patt, ""),
            Regex.compile(":{2}")) == Ok(("", ""))

    @test
    def breakAfterFirst02(): Bool =
        Result.map(patt -> Regex.breakAfterFirst(substr = patt, "aaa"),
            Regex.compile(":{2}")) == Ok(("aaa", ""))

    @test
    def breakAfterFirst03(): Bool =
        Result.map(patt -> Regex.breakAfterFirst(substr = patt, "::"),
            Regex.compile(":{2}")) == Ok(("::", ""))

    @test
    def breakAfterFirst04(): Bool =
        Result.map(patt -> Regex.breakAfterFirst(substr = patt, "::aaa"),
            Regex.compile(":{2}")) == Ok(("::", "aaa"))

    @test
    def breakAfterFirst05(): Bool =
        Result.map(patt -> Regex.breakAfterFirst(substr = patt, "aaa:"),
            Regex.compile(":{2}")) == Ok(("aaa:", ""))

    @test
    def breakAfterFirst06(): Bool =
        Result.map(patt -> Regex.breakAfterFirst(substr = patt, "aaa::"),
            Regex.compile(":{2}")) == Ok(("aaa::", ""))

    @test
    def breakAfterFirst07(): Bool =
        Result.map(patt -> Regex.breakAfterFirst(substr = patt, "aaa::bbb"),
            Regex.compile(":{2}")) == Ok(("aaa::", "bbb"))

    @test
    def breakAfterFirst08(): Bool =
        Result.map(patt -> Regex.breakAfterFirst(substr = patt, "aaa::bbb::ccc"),
            Regex.compile(":{2}")) == Ok(("aaa::", "bbb::ccc"))

    /////////////////////////////////////////////////////////////////////////////
    // breakOnLast                                                             //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def breakOnLast01(): Bool =
        Result.map(patt -> Regex.breakOnLast(substr = patt, ""),
            Regex.compile(":{2}")) == Ok(("", ""))

    @test
    def breakOnLast02(): Bool =
        Result.map(patt -> Regex.breakOnLast(substr = patt, "aaa"),
            Regex.compile(":{2}")) == Ok(("aaa", ""))

    @test
    def breakOnLast03(): Bool =
        Result.map(patt -> Regex.breakOnLast(substr = patt, "::"),
            Regex.compile(":{2}")) == Ok(("::", ""))

    @test
    def breakOnLast04(): Bool =
        Result.map(patt -> Regex.breakOnLast(substr = patt, "aaa"),
            Regex.compile(":{2}")) == Ok(("aaa", ""))

    @test
    def breakOnLast05(): Bool =
        Result.map(patt -> Regex.breakOnLast(substr = patt, "aaa:"),
            Regex.compile(":{2}")) == Ok(("aaa:", ""))

    @test
    def breakOnLast06(): Bool =
        Result.map(patt -> Regex.breakOnLast(substr = patt, "aaa::"),
            Regex.compile(":{2}")) == Ok(("aaa::", ""))

    @test
    def breakOnLast07(): Bool =
        Result.map(patt -> Regex.breakOnLast(substr = patt, "aaa::bbb"),
            Regex.compile(":{2}")) == Ok(("aaa::", "bbb"))

    @test
    def breakOnLast08(): Bool =
        Result.map(patt -> Regex.breakOnLast(substr = patt, "aaa::bbb::ccc"),
            Regex.compile(":{2}")) == Ok(("aaa::bbb::", "ccc"))

    /////////////////////////////////////////////////////////////////////////////
    // breakBeforeLast                                                         //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def breakBeforeLast01(): Bool =
        Result.map(patt -> Regex.breakBeforeLast(substr = patt, ""),
            Regex.compile(":{2}")) == Ok(("", ""))

    @test
    def breakBeforeLast02(): Bool =
        Result.map(patt -> Regex.breakBeforeLast(substr = patt, "aaa"),
            Regex.compile(":{2}")) == Ok(("aaa", ""))

    @test
    def breakBeforeLast03(): Bool =
        Result.map(patt -> Regex.breakBeforeLast(substr = patt, "::"),
            Regex.compile(":{2}")) == Ok(("", "::"))

    @test
    def breakBeforeLast04(): Bool =
        Result.map(patt -> Regex.breakBeforeLast(substr = patt, "aaa"),
            Regex.compile(":{2}")) == Ok(("aaa", ""))

    @test
    def breakBeforeLast05(): Bool =
        Result.map(patt -> Regex.breakBeforeLast(substr = patt, "aaa:"),
            Regex.compile(":{2}")) == Ok(("aaa:", ""))

    @test
    def breakBeforeLast06(): Bool =
        Result.map(patt -> Regex.breakBeforeLast(substr = patt, "aaa::"),
            Regex.compile(":{2}")) == Ok(("aaa", "::"))

    @test
    def breakBeforeLast07(): Bool =
        Result.map(patt -> Regex.breakBeforeLast(substr = patt, "aaa::bbb"),
            Regex.compile(":{2}")) == Ok(("aaa", "::bbb"))

    @test
    def breakBeforeLast08(): Bool =
        Result.map(patt -> Regex.breakBeforeLast(substr = patt, "aaa::bbb::ccc"),
            Regex.compile(":{2}")) == Ok(("aaa::bbb", "::ccc"))

}
