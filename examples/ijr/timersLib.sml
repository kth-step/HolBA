structure timersLib =
struct

fun timer_start () = Time.now()
fun timer_stop tm = (Time.- (Time.now(), tm))
fun timer_stop_str tm = Time.toString (Time.- (Time.now(), tm))

end