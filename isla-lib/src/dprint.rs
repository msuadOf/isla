#[macro_export]
macro_rules! d {
    ($($val:expr),* $(,)?) => {
        $(
            println!("[{}:{}] debug: {} = {:?}", file!(), line!(), stringify!($val), $val);
        )*
    };
}

#[macro_export]
macro_rules! d2 {
    ($($val:expr),* $(,)?) => {
        $(
            println!("[{}:{}] debug: {} = {:#?}", file!(), line!(), stringify!($val), $val);
        )*
    };
}