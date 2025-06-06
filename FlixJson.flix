mod Json {
    use JsonElement.{JsonObject, JsonArray, JsonString, JsonNumber, JsonBool, JsonNull}

    pub enum JsonElement {
        case JsonObject(Map[String, JsonElement])
        case JsonArray(List[JsonElement])
        case JsonString(String)
        case JsonNumber(BigDecimal)
        case JsonBool(Bool)
        case JsonNull
    }

    instance Eq[JsonElement] {
        pub def eq(x: JsonElement, y: JsonElement): Bool = match (x, y) {
            case (JsonObject(a), JsonObject(b)) => a == b
            case (JsonArray(a), JsonArray(b)) => a == b
            case (JsonString(a), JsonString(b)) => a == b
            case (JsonNumber(a), JsonNumber(b)) => a == b
            case (JsonBool(a), JsonBool(b)) => a == b
            case (JsonNull, JsonNull) => true
            case _ => false
        }
    }
}

mod Json {
    use Json.Path.Path;
    use Json.Path.{!!};
    use JsonElement.{JsonObject, JsonArray, JsonString, JsonNumber, JsonBool, JsonNull}
    use JsonError.JsonError

    pub enum JsonError(Path, Set[String]) with Eq

    pub trait ToJson[a] {
        pub def toJson(x: a): JsonElement
    }

    pub trait FromJson[a] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, a]
        pub def fromJson(x: JsonElement): Result[JsonError, a] = Json.FromJson.fromJsonAt(Path.Root, x)
        pub def fromNullableJsonAt(p: Path, x: JsonElement): Result[JsonError, Option[a]] = match x {
            case JsonNull => Ok(None)
            case y => Json.FromJson.fromJsonAt(p, y)
                |> Result.mapErr(match JsonError(path, expected) -> JsonError(path, Set.insert("null", expected)))
                |> Result.map(Some)
        }
        pub def fromNullableJson(x: JsonElement): Result[JsonError, Option[a]] = Json.FromJson.fromNullableJsonAt(Path.Root, x)
    }

    pub lawful trait Jsonable[a] with ToJson[a], FromJson[a] {
        law inverse: forall (x: a) with Eq[a] {
            x |> Json.ToJson.toJson |> Json.FromJson.fromJson == Ok(x)
        }
    }

    instance ToJson[Bool] {
        pub def toJson(x: Bool): JsonElement = JsonBool(x)
    }

    instance FromJson[Bool] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Bool] = match x {
            case JsonBool(y) => Ok(y)
            case _ => Err(JsonError(p, Set#{"boolean value"}))
        }
    }

    instance Jsonable[Bool]

    instance ToJson[Char] {
        pub def toJson(x: Char): JsonElement = JsonString(Char.toString(x))
    }

    instance FromJson[Char] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Char] = match x {
            case JsonString(y) if String.length(y) > 0 => Ok(String.charAt(0, y))
            case _ => Err(JsonError(p, Set#{"singleton string"}))
        }
    }

    instance Jsonable[Char]

    instance ToJson[Float32] {
        pub def toJson(x: Float32): JsonElement = {
            match Float32.tryToBigDecimal(x) {
                case Some(num) => JsonNumber(num)
                case None =>
                    if (Float32.isInfinite(x)) {
                        if (x > 0.0f32) {
                            JsonString("Infinity")
                        } else {
                            JsonString("-Infinity")
                        }
                    } else if (Float32.isNan(x)) {
                        JsonString("NaN")
                    } else {
                        bug!("invalid Float32: ${x}")
                    }
            }
        }
    }

    instance FromJson[Float32] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Float32] = match x {
            case JsonNumber(y) => BigDecimal.tryToFloat32(y) |> Option.toOk(JsonError(p, Set#{"floating-point number", "\"-Infinity\"", "\"Infinity\"", "\"NaN\""}))
            case JsonString("Infinity") => Ok(Float32.positiveInfinity())
            case JsonString("-Infinity") => Ok(Float32.negativeInfinity())
            case JsonString("NaN") => Ok(Float32.nan())
            case _ => Err(JsonError(p, Set#{"floating-point number", "\"-Infinity\"", "\"Infinity\"", "\"NaN\""}))
        }
    }

    instance ToJson[Float64] {
        pub def toJson(x: Float64): JsonElement = {
            match Float64.tryToBigDecimal(x) {
                case Some(num) => JsonNumber(num)
                case None =>
                    if (Float64.isInfinite(x)) {
                        if (x > 0.0f64) {
                            JsonString("Infinity")
                        } else {
                            JsonString("-Infinity")
                        }
                    } else if (Float64.isNan(x)) {
                        JsonString("NaN")
                    } else {
                        bug!("invalid Float64: ${x}")
                    }
            }
        }
    }

    instance FromJson[Float64] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Float64] = match x {
            case JsonNumber(y) => BigDecimal.tryToFloat64(y) |> Option.toOk(JsonError(p, Set#{"floating-point number", "\"-Infinity\"", "\"Infinity\"", "\"NaN\""}))
            case JsonString("Infinity") => Ok(Float64.positiveInfinity())
            case JsonString("-Infinity") => Ok(Float64.negativeInfinity())
            case JsonString("NaN") => Ok(Float64.nan())
            case _ => Err(JsonError(p, Set#{"floating-point number", "\"-Infinity\"", "\"Infinity\"", "\"NaN\""}))
        }
    }

    instance ToJson[BigDecimal] {
        pub def toJson(x: BigDecimal): JsonElement = JsonNumber(x)
    }

    instance FromJson[BigDecimal] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, BigDecimal] = match x {
            case JsonNumber(y) => Ok(y)
            case _ => Err(JsonError(p, Set#{"floating-point number"}))
        }
    }

    instance Jsonable[BigDecimal]

    instance ToJson[Int8] {
        pub def toJson(x: Int8): JsonElement = {
            JsonNumber(Int8.toBigDecimal(x))
        }
    }

    instance FromJson[Int8] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Int8] = match x {
            case JsonNumber(y) => BigDecimal.tryToInt8(y) |> Option.toOk(JsonError(p, Set#{"8-bit integer"}))
            case _ => Err(JsonError(p, Set#{"8-bit integer"}))
        }
    }

    instance Jsonable[Int8]

    instance ToJson[Int16] {
        pub def toJson(x: Int16): JsonElement = {
            JsonNumber(Int16.toBigDecimal(x))
        }
    }

    instance FromJson[Int16] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Int16] = match x {
            case JsonNumber(y) => BigDecimal.tryToInt16(y) |> Option.toOk(JsonError(p, Set#{"16-bit integer"}))
            case _ => Err(JsonError(p, Set#{"16-bit integer"}))
        }
    }

    instance Jsonable[Int16]

    instance ToJson[Int32] {
        pub def toJson(x: Int32): JsonElement = {
            JsonNumber(Int32.toBigDecimal(x))
        }
    }

    instance FromJson[Int32] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Int32] = match x {
            case JsonNumber(y) => BigDecimal.tryToInt32(y) |> Option.toOk(JsonError(p, Set#{"32-bit integer"}))
            case _ => Err(JsonError(p, Set#{"32-bit integer"}))
        }
    }

    instance Jsonable[Int32]

    instance ToJson[Int64] {
        pub def toJson(x: Int64): JsonElement = {
            JsonNumber(Int64.toBigDecimal(x))
        }
    }

    instance FromJson[Int64] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Int64] = match x {
            case JsonNumber(y) => BigDecimal.tryToInt64(y) |> Option.toOk(JsonError(p, Set#{"64-bit integer"}))
            case _ => Err(JsonError(p, Set#{"64-bit integer"}))
        }
    }

    instance Jsonable[Int64]

    instance ToJson[BigInt] {
        pub def toJson(x: BigInt): JsonElement = {
            JsonNumber(BigInt.toBigDecimal(x))
        }
    }

    instance FromJson[BigInt] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, BigInt] = match x {
            case JsonNumber(y) => Ok(BigDecimal.toBigInt(y))
            case _ => Err(JsonError(p, Set#{"integer"}))
        }
    }

    instance Jsonable[BigInt]

    instance ToJson[String] {
        pub def toJson(x: String): JsonElement = JsonString(x)
    }

    instance FromJson[String] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, String] = match x {
            case JsonString(y) => Ok(y)
            case _ => Err(JsonError(p, Set#{"string"}))
        }
    }

    instance Jsonable[String]

    instance ToJson[List[a]] with ToJson[a] {
        pub def toJson(x: List[a]): JsonElement = {
            let elems = List.map(Json.ToJson.toJson, x);
            JsonArray(elems)
        }
    }

    instance FromJson[List[a]] with FromJson[a] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, List[a]] = match x {
            case JsonArray(l) => l |> List.zipWithIndex |> Result.traverse(match (i, val) -> Json.FromJson.fromJsonAt(p !! i, val))
            case _ => Err(JsonError(p, Set#{"array"}))
        }
    }

    instance Jsonable[List[a]] with Jsonable[a]

    instance ToJson[Map[k, v]] with ToString[k], ToJson[v] {
        pub def toJson(x: Map[k, v]): JsonElement = {
            let map = x
                |> Map.toList
                |> List.map(match (k, v) -> (ToString.toString(k), Json.ToJson.toJson(v)))
                |> List.toMap;
            JsonObject(map)
        }
    }

    instance FromJson[Map[k, v]] with FromString[k], Order[k], FromJson[v] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Map[k, v]] = match x {
            case JsonObject(m0) =>
                use Result.flatMap;
                let l0 = Map.toList(m0);
                forM (
                    l <- l0 |> Result.traverse(match (k0, v0) ->
                    forM (
                        k <- FromString.fromString(k0) |> Option.toOk(JsonError(p !! k0, Set#{"valid key"}));
                        v <- Json.FromJson.fromJsonAt(p !! k0, v0)
                    ) yield {
                        (k, v)
                    })
                ) yield {
                    List.toMap(l)
                }
            case _ => Err(JsonError(p, Set#{"object"}))
        }
    }

    instance Jsonable[Map[k, v]] with ToString[k], FromString[k], Order[k], ToJson[v], FromJson[v]

    instance ToJson[Option[a]] with ToJson[a] {
        pub def toJson(x: Option[a]): JsonElement = match x {
            case Some(y) => JsonArray(Json.ToJson.toJson(y) :: Nil)
            case None => JsonArray(Nil)
        }
    }

    instance FromJson[Option[a]] with FromJson[a] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Option[a]] = match x {
            case JsonArray(Nil) => Ok(None)
            case JsonArray(y0 :: Nil) =>
                forM (
                    y <- Json.FromJson.fromJsonAt(p, y0)
                ) yield {
                    Some(y)
                }
            case _ => Err(JsonError(p, Set#{"empty array", "singleton array"}))
        }
    }

    instance Jsonable[Option[a]] with FromJson[a], ToJson[a]

    instance ToJson[(a, b)] with ToJson[a], ToJson[b] {
        pub def toJson(x: (a, b)): JsonElement = {
            let (a, b) = x;
            let jsonA = Json.ToJson.toJson(a);
            let jsonB = Json.ToJson.toJson(b);
            JsonArray(jsonA :: jsonB :: Nil)
        }
    }

    instance FromJson[(a, b)] with FromJson[a], FromJson[b] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, (a, b)] = {
            forM (
                l <- Json.FromJson.fromJsonAt(p, x);
                res <- match l {
                    case a :: b :: Nil =>
                        forM (
                            resA <- Json.FromJson.fromJsonAt(p !! 0, a);
                            resB <- Json.FromJson.fromJsonAt(p !! 1, b)
                        ) yield {
                            (resA, resB)
                        }
                    case _ =>
                        Err(JsonError(p, Set#{"2-ary array"}))
                }
            ) yield {
                res
            }
        }
    }

    instance Jsonable[(a, b)] with Jsonable[a], Jsonable[b]

    instance ToJson[(a, b, c)] with ToJson[a], ToJson[b], ToJson[c] {
        pub def toJson(x: (a, b, c)): JsonElement = {
            let (a, b, c) = x;
            let jsonA = Json.ToJson.toJson(a);
            let jsonB = Json.ToJson.toJson(b);
            let jsonC = Json.ToJson.toJson(c);
            JsonArray(jsonA :: jsonB :: jsonC :: Nil)
        }
    }

    instance FromJson[(a, b, c)] with FromJson[a], FromJson[b], FromJson[c] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, (a, b, c)] = {
            forM (
                l <- Json.FromJson.fromJsonAt(p, x);
                res <- match l {
                    case a :: b :: c :: Nil =>
                        forM (
                            resA <- Json.FromJson.fromJsonAt(p !! 0, a);
                            resB <- Json.FromJson.fromJsonAt(p !! 1, b);
                            resC <- Json.FromJson.fromJsonAt(p !! 2, c)
                        ) yield {
                            (resA, resB, resC)
                        }
                    case _ =>
                        Err(JsonError(p, Set#{"3-ary array"}))
                }
            ) yield {
                res
            }
        }
    }

    instance Jsonable[(a, b, c)] with Jsonable[a], Jsonable[b], Jsonable[c]

    instance ToJson[(a, b, c, d)] with ToJson[a], ToJson[b], ToJson[c], ToJson[d] {
        pub def toJson(x: (a, b, c, d)): JsonElement = {
            let (a, b, c, d) = x;
            let jsonA = Json.ToJson.toJson(a);
            let jsonB = Json.ToJson.toJson(b);
            let jsonC = Json.ToJson.toJson(c);
            let jsonD = Json.ToJson.toJson(d);
            JsonArray(jsonA :: jsonB :: jsonC :: jsonD :: Nil)
        }
    }

    instance FromJson[(a, b, c, d)] with FromJson[a], FromJson[b], FromJson[c], FromJson[d] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, (a, b, c, d)] = {
            forM (
                l <- Json.FromJson.fromJsonAt(p, x);
                res <- match l {
                    case a :: b :: c :: d :: Nil =>
                        forM (
                            resA <- Json.FromJson.fromJsonAt(p !! 0, a);
                            resB <- Json.FromJson.fromJsonAt(p !! 1, b);
                            resC <- Json.FromJson.fromJsonAt(p !! 2, c);
                            resD <- Json.FromJson.fromJsonAt(p !! 3, d)
                        ) yield {
                            (resA, resB, resC, resD)
                        }
                    case _ =>
                        Err(JsonError(p, Set#{"4-ary array"}))
                }
            ) yield {
                res
            }
        }
    }

    instance Jsonable[(a, b, c, d)] with Jsonable[a], Jsonable[b], Jsonable[c], Jsonable[d]

    instance ToJson[JsonElement] {
        pub def toJson(x: JsonElement): JsonElement = x
    }

    instance FromJson[JsonElement] {
        pub def fromJsonAt(_: Path, x: JsonElement): Result[JsonError, JsonElement] = Ok(x)
    }

    instance Jsonable[JsonElement]

    pub def getAtKey(p: Path, key: k, m: Map[String, JsonElement]): Result[JsonError, v] with ToString[k], FromJson[v] = {
        match Map.get("${key}", m) {
            case None => Err(JsonError(p, Set#{"object with key '${key}'"}))
            case Some(val) => Json.FromJson.fromJsonAt(p !! "${key}", val)
        }
    }

    pub def getAtKeyOpt(p: Path, key: k, m: Map[String, JsonElement]): Result[JsonError, Option[v]] with ToString[k], FromJson[v] = {
        use Result.flatMap;
        match Map.get("${key}", m) {
            case None => Ok(None)
            case Some(val) =>
                forM (
                    res <- Json.FromJson.fromJsonAt(p !! "${key}", val)
                ) yield {
                    Some(res)
                }
        }
    }
}

mod Json.Parse {
    import java.lang.NumberFormatException
    import java.lang.Integer
    import java.lang.Character

    use Json.JsonElement.{JsonObject, JsonArray, JsonString, JsonNumber, JsonBool, JsonNull}
    use Json.JsonElement;
    use Option.flatMap;


    type alias ParseMonad[t] = Option[(t, List[Char])]

    pub def parse(obj: String): Option[JsonElement] = {
        let in = String.toList(obj);
        forM (
            (_, tail) <- whitespace(in);
            (o, tail1) <- value(tail);
            _ <- eoi(tail1)
        ) yield {
            o
        }
    }

    def eoi(in: List[Char]): ParseMonad[Unit] = match in {
        case Nil => Some(((), Nil))
        case _ :: _ => None
    }

    def whitespace(in: List[Char]): ParseMonad[Unit] = match in {
        case ' ' :: tail => whitespace(tail)
        case '\t' :: tail => whitespace(tail)
        case '\r' :: tail => whitespace(tail)
        case '\n' :: tail => whitespace(tail)
        case _ => Some(((), in))
    }

    def object_(in: List[Char]): ParseMonad[JsonElement] = {
        forM (
            (_, tail) <- require('{', in);
            (_, tail1) <- whitespace(tail);
            (keyVals, tail2) <- keyVals(tail1);
            (_, tail3) <- require('}', tail2);
            (_, tail4) <- whitespace(tail3)
        ) yield {
            let map = List.toMap(keyVals);
            (JsonObject(map), tail4)
        }
    }

    def keyVals(in: List[Char]): ParseMonad[List[(String, JsonElement)]] = match in {
        case '\"' :: _ =>
            forM (
                (key, tail) <- string(in);
                (_, tail1) <- whitespace(tail);
                (_, tail2) <- require(':', tail1);
                (_, tail3) <- whitespace(tail2);
                (val, tail4) <- value(tail3);
                (_, tail5) <- whitespace(tail4);
                res <- match tail5 {
                    case ',' :: tail6 => forM (
                            (_, tail7) <- whitespace(tail6);
                            (tailKeyVals, tail8) <- keyVals(tail7)
                        ) yield {
                            let list = (key, val) :: tailKeyVals;
                            (list, tail8)
                        }
                    case '}' :: _ =>
                        let list = (key, val) :: Nil;
                        Some((list, tail5))
                    case _ => None
                }
            ) yield {
                res
            }

        case '}' :: _ => Some((Nil, in))

        case _ => None
    }

    def array(in: List[Char]): ParseMonad[JsonElement] = {
        forM (
            (_, tail) <- require('[', in);
            (_, tail1) <- whitespace(tail);
            (elems, tail2) <- elements(tail1);
            (_, tail3) <- require(']', tail2)
        ) yield {
            (JsonArray(elems), tail3)
        }
    }

    def elements(in: List[Char]): ParseMonad[List[JsonElement]] = match in {
        case ']' :: _ => Some((Nil, in))
        case _ =>
            region rc {
                let lst = MutList.empty(rc);
                def walk(input) = {
                    let opt = forM(
                        (val, tail) <- value(input);
                        (_, tail1) <- whitespace(tail)
                    ) yield (val, tail1);
                    match opt {
                        case None => None
                        case Some((val, tail1)) =>
                            MutList.push(val, lst);
                            match tail1 {
                                case ']' :: _ => Some(tail1)
                                case ',' :: tail2 =>
                                    match whitespace(tail2) {
                                        case None => None
                                        case Some((_, tail3)) => walk(tail3)
                                    }
                                case _ => None
                            }
                    }
                };
                forM(tl <- walk(in))
                    yield (MutList.toList(lst), tl)
            }
    }

    def value(in: List[Char]): ParseMonad[JsonElement] = match in {
        case '{' :: _ => object_(in)
        case '[' :: _ => array(in)
        case '\"' :: _ => stringValue(in)
        case 't' :: 'r' :: 'u' :: 'e' :: tail => Some((JsonBool(true), tail))
        case 'f' :: 'a' :: 'l' :: 's' :: 'e' :: tail => Some((JsonBool(false), tail))
        case 'n' :: 'u' :: 'l' :: 'l' :: tail => Some((JsonNull, tail))
        case _ => number(in)
    }

    def require(char: Char, in: List[Char]): ParseMonad[Unit] = match in {
        case head :: tail if char == head => Some(((), tail))
        case _ => None
    }

    def stringValue(in: List[Char]): ParseMonad[JsonElement] = {
        forM (
            (str, tail) <- string(in)
        ) yield {
            (JsonString(str), tail)
        }
    }

    def string(in: List[Char]): ParseMonad[String] = {
        forM (
            (_, tail) <- require('\"', in);
            (contents, tail2) <- stringContents(tail);
            (_, tail3) <- require('\"', tail2)
        ) yield {
            let str = listToString(contents);
            (str, tail3)
        }
    }

    def listToString(list: List[Char]): String = region r {
            let sb = StringBuilder.empty(r);
            list |> List.forEach(c -> StringBuilder.append(c, sb));
            StringBuilder.toString(sb)
    }

    def stringContents(in: List[Char]): ParseMonad[List[Char]] = stringContentsHelper(Nil, in)

    def stringContentsHelper(acc: List[Char], in: List[Char]): ParseMonad[List[Char]] = match in {
        case '\"' :: _ => Some((List.reverse(acc), in))

        case '\\' :: '\"' :: tail => stringContentsHelper('\"' :: acc, tail)

        case '\\' :: '\\' :: tail => stringContentsHelper('\\' :: acc, tail)

        case '\\' :: '/' :: tail => stringContentsHelper('/' :: acc, tail)

        case '\\' :: 'b' :: tail => stringContentsHelper('\u0008' :: acc, tail)

        case '\\' :: 'f' :: tail => stringContentsHelper('\u000C' :: acc, tail)

        case '\\' :: 'n' :: tail => stringContentsHelper('\n' :: acc, tail)

        case '\\' :: 'r' :: tail => stringContentsHelper('\r' :: acc, tail)

        case '\\' :: 't' :: tail => stringContentsHelper('\t' :: acc, tail)

        case '\\' :: 'u' :: c1 :: c2 :: c3 :: c4 :: tail =>
            let charRes = forM (
                string <- listToString(c1 :: c2 :: c3 :: c4 :: Nil) |> Some;
                intVal <- hexToInt(string)
            ) yield {
                unsafe Character.toChars(intVal) |> Array.get(0)
            };
            match charRes {
                case None => None
                case Some(char) => stringContentsHelper(char :: acc, tail)
            }

        case '\\' :: _ => None

        case c :: tail => stringContentsHelper(c :: acc, tail)

        case Nil => None
    }

    def hexToInt(hex: String): Option[Int32] = {
        try {
            Some(Integer.parseInt(hex, 16))
        } catch {
            case _: NumberFormatException => None
        }
    }

    def number(in: List[Char]): ParseMonad[JsonElement] = match in {
        case c :: tail if isNumberChar(c) =>
            forM (
                (chars, tail1) <- numberTail(tail);
                string <- listToString(c :: chars) |> Some;
                bigDec <- BigDecimal.fromString(string)
            ) yield {
                let number = JsonNumber(bigDec);
                (number, tail1)
            }
        case _ => None
    }

    def isNumberChar(c: Char): Bool = Char.isDigit(c) or c == '+' or c == '-' or c == 'e' or c == 'E' or c == '.'

    def numberTail(in: List[Char]): ParseMonad[List[Char]] = match in {
        case c :: tail if isNumberChar(c) =>
            forM (
                (chars, tail1) <- numberTail(tail)
            ) yield {
                (c :: chars, tail1)
            }
        case _ => Some((Nil, in))
    }

}

mod Json.Path {
    use Json.JsonElement.JsonArray;
    use Json.JsonElement.JsonObject;
    use Json.JsonElement;
    use Json.Utils.escape;
    use Path.{Root, AtIndex, AtKey}

    pub enum Path with Eq {
        case Root
        case AtIndex(Path, Int32)
        case AtKey(Path, String)
    }

    instance ToString[Path] {
        pub def toString(x: Path): String = match x {
            case Root => "$"
            case AtIndex(base, i) => "${base}[${i}]"
            case AtKey(base, key) => "${base}[${escape(key)}]"
        }
    }

    sealed trait Appendable[a] {
        pub def append(x: a, p: Path): Path
    }

    instance Appendable[Int32] {
        pub def append(x: Int32, p: Path): Path = atIndex(x, p)
    }

    instance Appendable[String] {
        pub def append(x: String, p: Path): Path = atKey(x, p)
    }

    pub def !!(p: Path, x: a): Path with Appendable[a] = Json.Path.Appendable.append(x, p)

    pub def atIndex(i: Int32, p: Path): Path = AtIndex(p, i)

    pub def atKey(k: String, p: Path): Path = AtKey(p, k)

    pub def apply(p: Path, json: JsonElement): Option[JsonElement] = {
        match p {
            case Root => Some(json)
            case AtIndex(root, i) =>
                forM (
                    next <- apply(root, json);
                    res <- match next {
                            case JsonArray(l) => nth(i, l)
                            case _ => None
                        }
                ) yield {
                    res
                }
            case (AtKey(root, key)) =>
                forM (
                    next <- apply(root, json);
                    res <- match next {
                            case JsonObject(o) => Map.get(key, o)
                            case _ => None
                        }
                ) yield {
                    res
                }
        }
    }

    def nth(n: Int32, l: List[a]): Option[a] = match (n, l) {
        case (0, hd :: _) => Some(hd)
        case (_, _ :: tl) if n > 0 => nth(n - 1, tl)
        case _ => None
    }
}

mod Json.Utils {

    pub def escape(s: String): String = {
        let contents = s
            |> String.toList
            |> List.map(char -> Map.getWithDefault(char, "${char}", escapes()))
            |> List.join("");
        "\"" + contents + "\""
    }

    def escapes(): Map[Char, String] = Map.union(specialEscapes(), controlCharacters())

    def specialEscapes(): Map[Char, String] = Map#{
        '\\' => "\\\\",
        '\"' => "\\\""
    }

    def controlCharacters(): Map[Char, String] = Map#{
        '\u0000' => "\\u0000",
        '\u0001' => "\\u0001",
        '\u0002' => "\\u0002",
        '\u0003' => "\\u0003",
        '\u0004' => "\\u0004",
        '\u0005' => "\\u0005",
        '\u0006' => "\\u0006",
        '\u0007' => "\\u0007",
        '\u0008' => "\\b",      // backspace
        '\u0009' => "\\t",      // tab
        '\u000A' => "\\n",      // line feed
        '\u000B' => "\\u000B",
        '\u000C' => "\\f",      // form feed
        '\u000D' => "\\r",      // carriage return
        '\u000E' => "\\u000E",
        '\u000F' => "\\u000F",
        '\u0010' => "\\u0010",
        '\u0011' => "\\u0011",
        '\u0012' => "\\u0012",
        '\u0013' => "\\u0013",
        '\u0014' => "\\u0014",
        '\u0015' => "\\u0015",
        '\u0016' => "\\u0016",
        '\u0017' => "\\u0017",
        '\u0018' => "\\u0018",
        '\u0019' => "\\u0019",
        '\u001A' => "\\u001A",
        '\u001B' => "\\u001B",
        '\u001C' => "\\u001C",
        '\u001D' => "\\u001D",
        '\u001E' => "\\u001E",
        '\u001F' => "\\u001F"
    }
}

mod Json.Write {
    use Json.JsonElement
    use Json.JsonElement.{JsonObject, JsonArray, JsonString, JsonNumber, JsonBool, JsonNull}
    use Json.Utils.escape

    pub def toCompactString(json: JsonElement): String = match json {
        case JsonObject(map) =>
            let contents = map
                |> Map.joinWith((k, v) -> escape(k) + ":" + toCompactString(v), ",");
            "{" + contents + "}"
        case JsonArray(list) =>
            let contents = list |> List.joinWith(toCompactString, ",");
            "[" + contents + "]"
        case JsonString(s) => escape(s)
        case JsonNumber(n) => "${n}"
        case JsonBool(b) => "${b}"
        case JsonNull => "null"
    }

    pub def toPrettyString(tab: Int32, json: JsonElement): String = match json {
        case JsonObject(map) if Map.isEmpty(map) => "{}"
        case JsonObject(map) =>
            let contents = map
                |> Map.joinWith((k, v) -> escape(k) + ": " + toPrettyString(tab, v), ",\n");
            "{\n" + String.indent(tab, contents) + "}"
        case JsonArray(Nil) => "[]"
        case JsonArray(list) =>
            let contents = list |> List.joinWith(toPrettyString(tab), ",\n");
            "[\n" + String.indent(tab, contents) + "]"
        case JsonString(s) => escape(s)
        case JsonNumber(n) => "${n}"
        case JsonBool(b) => "${b}"
        case JsonNull => "null"
    }
}

mod TestReadme {
    use Json.ToJson
    use Json.FromJson;
    use Json.FromJson.fromJsonAt;
    use Json.Path.Path;
    use Json.JsonElement;
    use Json.JsonError;
    use Json.getAtKey;
    use Json.getAtKeyOpt;
    use Json.Path.{!!};

    enum Person({
        name = String,
        age = Int32,
        city = String,
        zip = String,
        contact = Contact
    })

    enum Contact({
        email = String,
        phone = String
    })

    instance FromJson[Contact] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Contact] = {
            forM (
                map <- fromJsonAt(p, x);
                email <- getAtKey(p, "email", map);
                phone <- getAtKey(p, "phone", map)
            ) yield {
                Contact.Contact({ email = email, phone = phone })
            }
        }
    }


    instance FromJson[Person] {
        pub def fromJsonAt(p: Path, x: JsonElement): Result[JsonError, Person] = {
            forM (
                map <- fromJsonAt(p, x);
                name <- getAtKey(p, "name", map);
                age <- getAtKey(p, "age", map);
                addressMap <- getAtKey(p, "address", map);
                city <- getAtKey(p !! "address", "city", addressMap);
                zip <- getAtKey(p !! "address", "zip", addressMap);
                contact <- getAtKey(p, "contact", map)
            ) yield {
                Person.Person({
                    name = name,
                    age = age,
                    city = city,
                    zip = zip,
                    contact = contact
                })
            }
        }
    }

    instance ToJson[Contact] {
        pub def toJson(x: Contact): JsonElement = {
            let Contact.Contact(record) = x;
            let map = Map#{
                "email" => record#email,
                "phone" => record#phone
            };
            ToJson.toJson(map)
        }
    }

    instance ToJson[Person] {
        pub def toJson(x: Person): JsonElement = {
            let Person.Person(record) = x;
            let addressMap = Map#{
                "city" => record#city,
                "zip" => record#zip
            };
            let map = Map#{
                "name" => ToJson.toJson(record#name),
                "age" => ToJson.toJson(record#age),
                "address" => ToJson.toJson(addressMap),
                "contact" => ToJson.toJson(record#contact)
            };
            ToJson.toJson(map)
        }
    }

    pub def testReadmeParse(): Bool = {
        let string = "{\r\n  \"name\": \"Alice\",\r\n  \"age\": 30,\r\n  \"address\": {\r\n    \"city\": \"New York\",\r\n    \"zip\": \"10001\"\r\n  },\r\n  \"contact\": {\r\n    \"email\": \"alice@example.com\",\r\n    \"phone\": \"123-456-7890\"\r\n  }\r\n}";
        let resOpt = forM (
            json <- Json.Parse.parse(string);
            Person.Person(record) <- FromJson.fromJson(json) |> Result.toOption;
            Contact.Contact(contact) = record#contact
        ) yield {
            record#age == 30
            and record#name == "Alice"
            and record#zip == "10001"
            and record#city == "New York"
            and contact#email == "alice@example.com"
            and contact#phone == "123-456-7890"
        };
        Option.getWithDefault(false, resOpt)
    }
}

pub def runBenchmark(): Unit \ IO = {
    TestReadme.testReadmeParse() |> blackhole
}
