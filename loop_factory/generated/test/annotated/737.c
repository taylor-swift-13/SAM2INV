int main1(){
  int l9x, dp, li, yf;
  l9x=1+12;
  dp=0;
  li=(1%28)+10;
  yf=l9x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dp >= 0;
  loop invariant li == 11 - ((dp * (dp - 1)) / 2);
  loop invariant yf >= 13;
  loop invariant l9x == 13;
  loop invariant dp <= 5;
  loop assigns li, dp, yf;
*/
while (1) {
      if (!(li>dp)) {
          break;
      }
      li -= dp;
      dp += 1;
      yf = ((li%3))+(yf);
  }
}