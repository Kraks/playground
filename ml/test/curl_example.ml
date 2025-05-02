#require "curl"
open Curl

let write_cb content = 
  Printf.printf "%s" content;
  String.length content
;;

Curl.global_init Curl.CURLINIT_GLOBALALL;;

let get_btc_price() = 
  let curl = Curl.init() in
    Curl.set_url curl "https://www.okcoin.com/api/v1/ticker.do?symbol=ltc_usd";
    Curl.set_writefunction curl write_cb;
    Curl.perform curl;
    Curl.cleanup curl
;;

for i = 1 to 10 do
  get_btc_price() ;
  Printf.printf "%d\n" i
done
;;

Curl.global_cleanup()
