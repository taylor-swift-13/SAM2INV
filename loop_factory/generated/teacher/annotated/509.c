int main1(int b,int m){
  int g, x, v, p;

  g=b;
  x=0;
  v=m;
  p=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (v - m) % 6 == 0;
  loop invariant v >= m;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant ((v - m) % 12 == 0) ==> (v - 2*p == m - 4);
  loop invariant ((v - m) % 12 == 6) ==> (v - 2*p == 4 - m);
  loop invariant g == b;
  loop invariant g == \at(b, Pre);
  loop invariant ((v - \at(m, Pre)) % 6) == 0;
  loop assigns v, p;
*/
while (1) {
      v = v+1;
      p = p+1;
      v = v+5;
      p = p+2;
      p = v-p;
  }

}
