structure bir_fileLib =
struct
local
  val ERR = Feedback.mk_HOL_ERR "bir_fileLib"
  val wrap_exn = Feedback.wrap_exn "bir_fileLib"
in

  (* directory creation helper *)
    fun makedir makepath path =
      let
	val r = OS.Process.system ("mkdir " ^ (if makepath then "-p " else "") ^ path);
	val _ = if not (OS.Process.isSuccess r) then
		  raise ERR "makedir" ("couldn't create the following directory: " ^ path)
		else
		  ();
      in
	()
      end;

  fun get_tempfile prefix =
    let
      val tempdir = "tempdir";
      val _ = makedir true tempdir;
      val date = Date.fromTimeLocal (Time.now ());
      val datestr = Date.fmt "%Y-%m-%d_%H-%M-%S" date;
    in
      tempdir ^ "/" ^ prefix ^ datestr
    end;

end (* local *)
end (* struct *)
