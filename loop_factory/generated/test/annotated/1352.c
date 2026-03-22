int main1(){
  int m9, sv, n, swt, un, q;
  m9=1+10;
  sv=0;
  n=(1%28)+8;
  swt=(1%22)+5;
  un=0;
  q=sv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m9 == 1 + 10;
  loop invariant sv == 0;
  loop invariant q >= 0;
  loop invariant n >= 9;
  loop invariant swt >= 0;
  loop invariant un >= 0;
  loop invariant (n % 9) == 0;
  loop invariant 0 <= swt <= 6;
  loop assigns un, swt, n, q;
*/
while (swt!=0) {
      if (swt%2==1) {
          un += n;
          swt = swt - 1;
      }
      swt = swt/2;
      n = 2*n;
      q += swt;
      if (sv+7<=q+m9) {
          q = q*q;
      }
  }
}