signature PRINT_FORMATS = sig


end

structure Print_Formats : PRINT_FORMATS = struct

datatype term_formats = Natural | Ordinary | Show_Type | Show_Type_Sort | Show_Type_nv | Random_Type_04_Sort_05

fun name_of Natural = "natural"
  | name_of Ordinary = "ordinary"
  | name_of Show_Type = "type"
  | name_of Show_Type_Sort = "type_sort"
  | name_of Show_Type_nv = "type_nv"
  | name_of Random_Type_04_Sort_05 = "t4s5"

fun string_of_term Natural = (fn ctxt =>
      let val ctxt = Config.put Printer.show_markup false ctxt
       in Syntax.string_of_term ctxt
          (*The format is determined by the given context*)
      end)
  | string_of_term Ordinary = (fn ctxt =>
      let val ctxt = ctxt
                |> Config.put Printer.show_types false
                |> Config.put Printer.show_sorts false
                |> Config.put Printer.show_types_nv false
                |> Config.put Printer.show_markup false
                |> Config.put Printer.show_structs false
                |> Config.put Printer.show_question_marks true
                |> Config.put Printer.show_brackets false
       in Syntax.string_of_term ctxt
       #> REPL.trim_makrup
      end)
  | string_of_term Show_Type = (fn ctxt =>
      let val ctxt = ctxt
                |> Config.put Printer.show_types true
                |> Config.put Printer.show_sorts false
                |> Config.put Printer.show_types_nv false
                |> Config.put Printer.show_markup false
                |> Config.put Printer.show_structs false
                |> Config.put Printer.show_question_marks true
                |> Config.put Printer.show_brackets false
       in Syntax.string_of_term ctxt
       #> REPL.trim_makrup
      end)
  | string_of_term Show_Type_Sort = (fn ctxt =>
      let val ctxt = ctxt
                |> Config.put Printer.show_types true
                |> Config.put Printer.show_sorts true
                |> Config.put Printer.show_types_nv false
                |> Config.put Printer.show_markup false
                |> Config.put Printer.show_structs false
                |> Config.put Printer.show_question_marks true
                |> Config.put Printer.show_brackets false
       in Syntax.string_of_term ctxt
       #> REPL.trim_makrup
      end)
  | string_of_term Show_Type_nv = (fn ctxt =>
      let val ctxt = ctxt
                |> Config.put Printer.show_types true
                |> Config.put Printer.show_sorts false
                |> Config.put Printer.show_types_nv true
                |> Config.put Printer.show_markup false
                |> Config.put Printer.show_structs false
                |> Config.put Printer.show_question_marks true
                |> Config.put Printer.show_brackets false
       in Syntax.string_of_term ctxt
       #> REPL.trim_makrup
      end)
  | string_of_term Random_Type_04_Sort_05 = (fn ctxt =>
      let val show_type = Random.random () <= 0.6
          val ctxt = ctxt
                |> Config.put Printer.show_types show_type
                |> Config.put Printer.show_sorts false
                |> Config.put Printer.show_types_nv false
                |> Config.put Printer.show_markup false
                |> Config.put Printer.show_structs false
                |> Config.put Printer.show_question_marks true
                |> Config.put Printer.show_brackets false
       in Syntax.string_of_term ctxt
       #> REPL.trim_makrup
      end)

end
