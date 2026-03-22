int main1(){
  int sma, c, fp, ya99;
  sma=0;
  c=0;
  fp=0;
  ya99=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ya99 + c == 6;
  loop invariant c == fp;
  loop invariant sma >= 6 * c;
  loop invariant 0 <= c <= 6;
  loop assigns sma, c, fp, ya99;
*/
while (1) {
      if (!(ya99>0)) {
          break;
      }
      c = c+1*1;
      ya99 = (ya99)+(-(1));
      fp = fp+1*1;
      sma = sma+1*1;
      sma = sma*3+3;
  }
}