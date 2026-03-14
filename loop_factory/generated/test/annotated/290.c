int main1(int c){
  int m, wuz, b4, rb, a;
  m=c*5;
  wuz=0;
  b4=c;
  rb=8;
  a=wuz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == wuz * b4;
  loop invariant rb == 8 + b4 * wuz * (wuz - 1) / 2;
  loop invariant m == 5 * b4;
  loop invariant wuz >= 0;
  loop invariant m == \at(c, Pre) * 5;
  loop assigns wuz, rb, a;
*/
for (; wuz+1<=m; wuz++) {
      rb = rb + a;
      a += b4;
  }
}