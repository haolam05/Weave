import { List, nil, cons, rev, concat } from './list';
import { Color } from './color';

/**
 * Returns the list of colors shown in the each of the odd rows (first,
 * third, fifth, etc.) by a warp-faced weave with the given warp colors.
 * @param list of all the (warp) colors in the weave
 * @return take(colors), i.e., every other color starting from the first
 */
export function weaveWarpFacedOdds(colors: List<Color>): List<Color> {
  let rest: List<Color> = colors;   // "rest" plays the role of "colors"
  let done: List<Color> = nil;      // "done" plays the role of "R"

  // TODO: add an Inv
  // {{ Inv: take(colors) = concat(rev(R), take(colors)) }} <-> {{ Inv: take(colors) = concat(rev(done), take(rest)) }}   since "done" plays the role of "R" and "rest" plays the role of "colors"
    // Prove:
    //        concat(rev(done), take(rest)) = concat(rev(nil), take(rest))    since done = nil
    //                                      = concat(nil, take(rest))         def of rev
    //                                      = take(rest)                      def of concat
    //                                      = take(colors)                    since rest = colors
  while (rest !== nil && rest.tl !== nil) {
    // {{ take(colors) = concat(rev(done), take(rest)) and rest != nil and rest.tl != nil }}          Prove:  (note: rest != nil and rest.tl != nil)
    // {{ take(colors) = concat(rev(cons(rest.hd, done)), take(rest.tl.tl)) }}                                take(colors) = concat(rev(done), take(rest))                           from loop invariant
    //                                                                                                                     = concat(rev(done), cons(rest.hd, skip(rest.tl)))         def of take
    done = cons(rest.hd, done);  //                                                                                        = concat(rev(done), cons(rest.hd, take(rest.tl.tl)))      def of skip
    // {{ take(colors) = concat(rev(done), take(rest.tl.tl)) }}                                                            = concat(rev(cons(rest.hd, done)), take(rest.tl.tl))      equivalent algebra (look at example below for details)
    rest = rest.tl.tl;
    // {{ take(colors) = concat(rev(done), take(rest)) }}                                                                    *** ex1: concat(rev(cons(2, cons(1, nil))), cons(3, nil))) = cons(1, cons(2, cons(3, nil)))
  } //                                                                                                                               concat(rev(cons(3, cons(2, cons(1, nil)))))       = cons(1, cons(2, cons(3, nil)))

  // when we exit the loop:
  // {{ take(colors) = concat(rev(done), take(rest)) and (rest = nil or rest.tl = nil) }}
  if (rest === nil) {
    // {{ take(colors) = concat(rev(done), take(rest)) and rest = nil }}
    // Prove:
    //        take(colors) = concat(rev(done), take(rest))    from loop invariant
    //                     = concat(rev(done), take(nil))     since rest = nil
    //                     = concat(rev(done), nil)           def of take
    //                     = rev(done)                        def of concat
    return rev(done);
  } else {
    // {{ take(colors) = concat(rev(done), take(rest)) and rest.tl = nil }}
    // Prove:
    //        take(colors) = concat(rev(done), take(rest))                      from loop invariant
    //                     = concat(rev(done), cons(rest.hd, skip(rest.tl)))    def of take
    //                     = concat(rev(done), cons(rest.hd, skip(nil)))        since rest.tl = nil
    //                     = concat(rev(done), cons(rest.hd, nil))              def of skip
    //                     = rev(cons(rest.hd, done))                           equivalent algebra (look at ex1 above for details)
    return rev(cons(rest.hd, done));
  }
}

/**
 * Returns the list of colors shown in the each of the even rows (second,
 * fourth, etc.) by a warp-faced weave with the given warp colors.
 * @param list of all the (warp) colors in the weave
 * @return skip(colors), i.e., every other color starting from the second
 */
export function weaveWarpFacedEvens(colors: List<Color>): List<Color> {
  let rest: List<Color> = colors;   // "rest" plays the role of "colors"
  let done: List<Color> = nil;      // "done" plays the role of "R"

  // TODO: add an Inv
  // {{ Inv: skip(colors) = concat(rev(R), skip(colors)) }} <-> {{ Inv: skip(colors) = concat(rev(done), skip(rest)) }}   since "done" plays the role of "R" and "rest" plays the role of "colors"
    // Prove:
    //        concat(rev(done), skip(rest)) = concat(rev(nil), skip(rest))    since done = nil
    //                                      = concat(nil, skip(rest))         def of rev
    //                                      = skip(rest)                      def of concat
    //                                      = skip(colors)                    since rest = colors
  while (rest !== nil && rest.tl !== nil) {
    // TODO: implement this
    // {{ skip(colors) = concat(rev(done), skip(rest)) and rest != nil and rest.tl != nil }}          Prove:  (note: rest != nil and rest.tl != nil)
    // {{ skip(colors) = concat(rev(cons(rest.tl.hd, done)), skip(rest.tl.tl)) }}                             skip(colors) = concat(rev(done), skip(rest))                            from loop invariant
    //                                                                                                                     = concat(rev(done), take(rest.tl)                          def of skip
    done = cons(rest.tl.hd, done);  //                                                                                     = concat(rev(done), cons(rest.tl.hd, skip(rest.tl.tl)))    def of take
    // {{ skip(colors) = concat(rev(done), skip(rest.tl.tl)) }}                                                            = concat(rev(cons(rest.tl.hd, done)), skip(rest.tl.tl))    equivalent algebra (look at ex1 above for details)
    rest = rest.tl.tl;
    // {{ skip(colors) = concat(rev(done), skip(rest)) }}
  }

  // when we exit the loop:
  // {{ skip(colors) = concat(rev(done), skip(rest)) and (rest = nil or rest.tl = nil) }}
  if (rest === nil) {
    // {{ skip(colors) = concat(rev(done), skip(rest)) and rest = nil }}
    // Prove:
    //        skip(colors) = concat(rev(done), skip(rest))    from loop invariant
    //                     = concat(rev(done), skip(nil))     since rest = nil
    //                     = concat(rev(done), nil)           def of rev
    //                     = rev(done)                        def of concat
    return rev(done);
  } else {
    // {{ skip(colors) = concat(rev(done), skip(rest)) and rest.tl = nil }}
    // Prove:
    //        skip(colors) = concat(rev(done), skip(rest))        from loop invariant
    //                     = concat(rev(done), take(rest.tl))     def of skip
    //                     = concat(rev(done), take(nil))         since rest.tl = nil
    //                     = concat(rev(done), nil)               def of take
    //                     = rev(done)                            def of concat
    return rev(done);
  }
}

/**
 * Returns the list of colors shown in the each of the odd rows (first, third,
 * fifth, etc.) by a balanced weave with the given warp and weft colors.
 * @param list of all the (warp) colors in the weave
 * @para c (weft) color to replace with
 * @return leave(colors, c)
 */
export function weaveBalancedOdds(colors: List<Color>, c: Color): List<Color> {
  let rest: List<Color> = colors;   // "rest" plays the role of "colors"
  let done: List<Color> = nil;      // "done" plays the role of "R"

  // TODO: add an Inv
  // {{ Inv: leave(colors, c) = concat(rev(R), leave(colors, c)) }} <-> {{ Inv: leave(colors, c) = concat(rev(done), leave(rest, c)) }}   since "done" plays the role of "R" and "rest" plays the role of "colors"
  // Prove:
  //        concat(rev(done), leave(rest, c)) = concat(rev(nil), leave(rest, c))    since done = nil
  //                                          = concat(nil, leave(rest, c))         def of rev
  //                                          = leave(rest, c)                      def of concat
  //                                          = leave(colors, c)                    since rest = colors
  while (rest !== nil && rest.tl !== nil) {
    // TODO: implement this
    // {{ leave(colors, c) = concat(rev(done), leave(rest, c)) and rest != nil and rest.tl != nil }}          Prove:  (note: rest != nil and rest.tl != nil)
    // {{ leave(colors, c) = concat(rev(cons(c, cons(rest.hd, done))), leave(rest.tl.tl, c)) }}                       leave(colors, c) = concat(rev(done), leave(rest, c))                                  from loop invariant
    //                                                                                                                                 = concat(rev(done), cons(rest.hd, replace(rest.tl, c)))              def of leave
    done = cons(c, cons(rest.hd, done));  //                                                                                           = concat(rev(done), cons(rest.hd, cons(c, leave(rest.tl.tl, c))))    def of replace
    // {{ leave(colors, c) = concat(rev(done), leave(rest.tl.tl, c)) }}                                                                = concat(rev(cons(rest.hd, done)), cons(c, leave(rest.tl.tl, c)))    equivalent algebra (look at ex1 above for details)
    rest = rest.tl.tl;  //                                                                                                             = concat(rev(cons(c, cons(rest.hd, done))), leave(rest.tl.tl, c))    equivalent algebra (look at ex1 above for details)
    // {{ leave(colors, c) = concat(rev(done), leave(rest, c)) }}
  }

  // when we exit the loop:
  // {{ leave(colors, c) = concat(rev(done), leave(rest, c)) and (rest = nil or rest.tl = nil) }}
  if (rest === nil) {
    // {{ leave(colors, c) = concat(rev(done), leave(rest, c)) and rest = nil }}
    // Prove:
    //        leave(colors, c) = concat(rev(done), leave(rest, c))      from loop invariant
    //                         = concat(rev(done), leave(nil, c))       since rest = nil
    //                         = concat(rev(done), nil))                def of leave
    //                         = rev(done)                              def of concat
    return rev(done);
  } else {
    // {{ leave(colors, c) = concat(rev(done), leave(rest, c)) and rest.tl = nil }}
    // Prove:
    //        leave(colors, c) = concat(rev(done), leave(rest, c))                        from loop invariant
    //                         = concat(rev(done), cons(rest.hd, replace(rest.tl, c)))    def of leave
    //                         = concat(rev(done), cons(rest.hd, replace(nil, c)))        since rest.tl = nil
    //                         = concat(rev(done), cons(rest.hd, nil))                    def of replace
    //                         = concat(rev(cons(rest.hd, done)), nil)                    equivalent algebra (look at ex1 above for details)
    //                         = rev(cons(rest.hd, done))                                 def of concat
    return rev(cons(rest.hd, done));
  }
}

/**
 * Returns the list of colors shown in the each of the even rows (second,
 * fourth, etc.) by a balanced weave with the given warp and weft colors.
 * @param list of all the (warp) colors in the weave
 * @para c (weft) color to replace with
 * @return replace(colors, c)
 */
export function weaveBalancedEvens(colors: List<Color>, c: Color): List<Color> {
  let rest: List<Color> = colors;   // "rest" plays the role of "colors"
  let done: List<Color> = nil;      // "done" plays the role of "R"

  // TODO: add an Inv
  // {{ Inv: replace(colors, c) = concat(rev(R), replace(colors, c)) }} <-> {{ Inv: replace(colors, c) = concat(rev(done), replace(rest, c)) }}   since "done" plays the role of "R" and "rest" plays the role of "colors"
  // Prove:
  //        concat(rev(done), replace(rest, c)) = concat(rev(nil), replace(rest, c))      since done = nil
  //                                            = concat(nil, replace(rest, c))           def of rev
  //                                            = replace(rest, c)                        def of concat
  //                                            = replace(colors, c)                      since rest = colors
  while (rest !== nil && rest.tl !== nil) {
    // TODO: implement this
    // {{ replace(colors, c) = concat(rev(done), replace(rest, c)) }}                                         Prove:  (note: rest != nil and rest.tl != nil)
    // {{ replace(colors, c) = concat(rev(cons(rest.tl.hd, cons(c, done))), replace(rest.tl.tl, c)) }}                replace(colors, c) = concat(rev(done), replace(rest, c))                                      from loop invariant
    //                                                                                                                                   = concat(rev(done), cons(c, leave(rest.tl, c)))                            def of replace
    done = cons(rest.tl.hd, cons(c, done)); //                                                                                           = concat(rev(done), cons(c, cons(rest.tl.hd, replace(rest.tl.tl, c))))     def of leave
    // {{ replace(colors, c) = concat(rev(done), replace(rest.tl.tl, c)) }}                                                              = concat(rev(cons(c, done)), cons(rest.tl.hd, replace(rest.tl.tl, c)))     equivalent algebra (look at ex1 above for details)
    rest = rest.tl.tl;  //                                                                                                               = concat(rev(cons(rest.tl.hd, cons(c, done))), replace(rest.tl.tl, c))     equivalent algebra (look at ex1 above for details)
    // {{ replace(colors, c) = concat(rev(done), replace(rest, c)) }}
  }

  // when we exit the loop:
  // {{ replace(colors, c) = concat(rev(done), replace(rest, c)) and (rest = nil or rest.tl = nil) }}
  if (rest === nil) {
    // {{ replace(colors, c) = concat(rev(done), replace(rest, c)) and rest = nil) }}
    // Prove:
    //        replace(colors, c) = concat(rev(done), replace(rest, c))    // from loop invariant
    //                           = concat(rev(done), replace(nil, c))     // since rest = nil
    //                           = concat(rev(done), nil)                 // def of replace
    //                           = rev(done)                              // def of concat
    return rev(done);
  } else {
    // {{ replace(colors, c) = concat(rev(done), replace(rest, c)) and rest.tl = nil }}
    // Prove:
    //        replace(colors, c) = concat(rev(done), replace(rest, c))              // from loop invariant
    //                           = concat(rev(done), cons(c, leave(rest.tl, c)))    // def of replace
    //                           = concat(rev(done), cons(c, leave(nil, c)))        // since rest.tl = nil
    //                           = concat(rev(done), cons(c, nil))                  // def of leave
    //                           = concat(rev(cons(c, done)), nil)                  // equivalent algebra (look at ex1 above for details)
    //                           = rev(cons(c, done))                               // def of concat
    return rev(cons(c, done));
  }
}

/**
 * Returns the given number of rows of a weave with the given colors
 * @param rows the (natural) number of rows in the weave
 * @param colors the weft colors in each row
 * @returns list of the given length where the odd values are the colors of
 *      weaveWarpFacedOdds and the even values are the colors of
 *      weaveWarpFacedEvens.
 * @returns the function defined recursively (on rows) by
 *   - weaveWarpFaced(0, colors) = nil
 *   - weaveWarpFaced(1, colors) = cons(weaveWarpFacedEvens(colors), nil)
 *   - weaveWarpFaced(n+2, colors) =
 *         cons(weaveWarpFacedEvens(colors),
 *             cons(weaveWarpFacedRows(colors), weaveWarpFaced(n, colors)))
 */
export function weaveWarpFaced(rows: number, colors: List<Color>): List<List<Color>> {
  // TODO: implement this with a while loop instead
  // Be sure to document your loop invariant with an Inv comment above the loop
  let row_remains: number = rows;
  let result: List<List<Color>> = nil;
  
  // {{ Inv: weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors)) }}
  // Prove:
  //        concat(result, weaveWarpFaced(row_remains, colors)) = concat(nil, weaveWarpFaced(row_remains, colors))    since result = nil
  //                                                            = weaveWarpFaced(row_remains, colors)                 def of concat
  //                                                            = weaveWarpFaced(rows, colors)                        since rows = row_remains
  while (row_remains >= 2) {
    // {{ weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors)) and row_remains >= 2 }}
    // {{ weaveWarpFaced(rows, colors) = concat(concat(result, cons(weaveWarpFacedEvens(colors), cons(weaveWarpFacedOdds(colors), nil))), weaveWarpFaced(row_remains - 2, colors)) }}
    //
    //                                                                                                                         Prove:
    //                                                                                                                                 weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors))                                                                                         from loop invariant
    result = concat(result, cons(weaveWarpFacedEvens(colors), cons(weaveWarpFacedOdds(colors), nil)));  //                                                          = concat(result, cons(weaveWarpFacedEvens(colors), cons(weaveWarpFacedOdds(colors), weaveWarpFaced(row_remains - 2, colors)))                 def of weaveWarpFaced
    // {{ weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains - 2, colors)) }}                                                                 = concat(concat(result, cons(weaveWarpFacedEvens(colors), cons(weaveWarpFacedOdds(colors), nil))), weaveWarpFaced(row_remains - 2, colors))   def of concat
    row_remains -= 2;
    // {{ weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors)) }}
  }

  // when we exit the loop:
  // {{ weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors)) and (result = 1 or result = 0) }}
  if (row_remains == 0) {
    // {{ weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors)) and result = 0 }}
    // Prove:
    //         weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors))     from loop invariant
    //                                      = concat(result, weaveWarpFaced(0, colors))               since row_remains = 0
    //                                      = concat(result, nil)                                     def of weaveWarpFaced
    //                                      = result                                                  def of concat
    return result;
  } else {  // row_remains = 1
    // {{ weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors)) and result = 1 }}
    // Prove:
    //        weaveWarpFaced(rows, colors) = concat(result, weaveWarpFaced(row_remains, colors))      from loop invariant
    //                                     = concat(result, weaveWarpFaced(1, colors))                since row_remains = 1
    //                                     = concat(result, cons(weaveWarpFacedEvens(colors), nil))   def of weaveWarpFaced
    return concat(result, cons(weaveWarpFacedEvens(colors), nil));
  }
}

/**
 * Returns the given number of rows of a balanced weave with the given colors
 * @param rows the (natural) number of rows in the weave
 * @param colors the warp colors in each row
 * @param c the weft color
 * @returns the function defined recursively (on rows) by
 *   - weaveBalanced(0, colors, c) = nil
 *   - weaveBalanced(1, colors, c) = cons(weaveBalancedEvens(colors, c), nil)
 *   - weaveBalanced(n+2, colors, c) =
 *         cons(weaveBalancedEvens(colors, c),
 *             cons(weaveBalancedRows(colors, c), weaveBalanced(n, colors, c)))
 */
export function weaveBalanced(rows: number, colors: List<Color>, c: Color): List<List<Color>> {
  // TODO: implement this with a while loop instead
  // Be sure to document your loop invariant with an Inv comment above the loop
  let row_remains: number = rows;
  let result: List<List<Color>> = nil;

  // {{ Inv: weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c)) }}
  // Prove:
  //        concat(result, weaveBalanced(row_remains, colors, c)) = concat(nil, weaveBalanced(row_remains, colors, c))    since result = nil
  //                                                              = weaveBalanced(row_remains, colors, c)                 def of concat
  //                                                              = weaveBalanced(rows, colors, c)                        since rows = row_remains
  while (row_remains >= 2) {
    // {{ weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c)) and row_remains >= 2 }}
    // {{ weaveBalanced(rows, colors, c) = concat(concat(result, cons(weaveBalancedEvens(colors, c), cons(weaveBalancedOdds(colors, c), nil))), weaveBalanced(row_remains - 2, colors, c)) }}
    //
    //                                                                                                                         Prove:
    //                                                                                                                                weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c))                                                                                             from loop invariant
    result = concat(result, cons(weaveBalancedEvens(colors, c), cons(weaveBalancedOdds(colors, c), nil)));  //                                                       = concat(result, cons(weaveBalancedEvens(colors, c), cons(weaveBalancedOdds(colors, c), weaveBalanced(row_remains - 2, colors, c))))                def of weaveBalanced
    // {{ weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains - 2, colors, c)) }}                                                              = concat(concat(result, cons(weaveBalancedEvens(colors, c), cons(weaveBalancedOdds(colors, c), nil))), weaveBalanced(row_remains - 2, colors, c))   def of concat
    row_remains -= 2;
    // {{ weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c)) }}
  }

  // when we exit the loop:
  // {{ weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c)) and (row_remains = 1 or row_remains = 0) }}
  if (row_remains == 0) {
    // {{ weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c)) and row_remains = 0 }}
    // Prove:
    //        weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c))      from loop invariant
    //                                       = concat(result, weaveBalanced(0, colors, c))                since row_remains = 0
    //                                       = concat(result, nil)                                        def of weaveBalanced
    //                                       = result                                                     def of concat
    return result;
  } else {  // row_remains = 1
    // {{ weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c)) and row_remains = 1 }}
    // Prove:
    //        weaveBalanced(rows, colors, c) = concat(result, weaveBalanced(row_remains, colors, c))      from loop invariant
    //                                       = concat(result, weaveBalanced(1, colors, c))                since row_remains = 1
    //                                       = concat(result, cons(weaveBalancedEvens(colors, c), nil))   def of weaveBalanced
    return concat(result, cons(weaveBalancedEvens(colors, c), nil));
  }
}
