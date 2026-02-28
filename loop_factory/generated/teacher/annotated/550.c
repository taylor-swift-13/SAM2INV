int main1(int b,int p){
  int c, v, m;

  c=(p%6)+10;
  v=1;
  m=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == (\at(p,Pre) % 6) + 10;
  loop invariant p == \at(p,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant v >= 1;
  loop invariant v <= c;
  loop invariant m >= 1;
  loop invariant m > 0;
  loop invariant (m == 1) || (m % 2 == 0);
  loop invariant c == (p % 6) + 10;
  loop invariant v <= 9;

  loop invariant v >= 1 && v <= c && (v == 1 || v % 3 == 0) && m >= 1;
  loop assigns m, v;
*/
while (v<=c/3) {
      if (v+6<=p+c) {
          m = m*2;
      }
      v = v*3;
  }

}
