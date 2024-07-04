#[macro_export]
macro_rules! log {
  (INFO: $($arg:tt)*) => {
    eprintln!("\x1b[2m[{}]\x1b[0m \x1b[34mINFO\x1b[0m: {}", Local::now().format("%Y-%m-%d %H:%M:%S.%3f"), format_args!($($arg)*));
  };
  (WARN: $($arg:tt)*) => {
    eprintln!("\x1b[2m[{}]\x1b[0m \x1b[33mWARN\x1b[0m: {}", Local::now().format("%Y-%m-%d %H:%M:%S.%3f"), format_args!($($arg)*));
  };
  (ERROR: $($arg:tt)*) => {
    eprintln!("\x1b[2m[{}]\x1b[0m \x1b[31mERROR\x1b[0m: {}", Local::now().format("%Y-%m-%d %H:%M:%S.%3f"), format_args!($($arg)*));
  };
  (DEBUG: $($arg:tt)*) => {
    eprintln!("\x1b[2m[{}]\x1b[0m \x1b[35mDEBUG\x1b[0m: {}", Local::now().format("%Y-%m-%d %H:%M:%S.%3f"), format_args!($($arg)*));
  };
  (OUTPUT: $($arg:tt)*) => {
    eprintln!("\x1b[2m[{}]\x1b[0m \x1b[32mOUTPUT\x1b[0m: {}", Local::now().format("%Y-%m-%d %H:%M:%S.%3f"), format_args!($($arg)*));
  };
  ($($arg:tt)*) => {
    eprintln!("\x1b[2m[{}]\x1b[0m {}", Local::now().format("%Y-%m-%d %H:%M:%S.%3f"), format_args!($($arg)*));
  };
}
