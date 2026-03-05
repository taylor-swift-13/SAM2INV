int main1(){
  int pah, l28, we;
  pah=1;
  l28=0;
  we=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant we == 0;
  loop invariant pah == 1;
  loop invariant 0 <= l28;
  loop invariant l28 <= pah;
  loop assigns l28, we;
*/
for (; we>0&&l28<pah; l28++) {
      if (we<we) {
          we = we;
      }
      else {
          we = we;
      }
      we -= we;
      we += we;
  }
}