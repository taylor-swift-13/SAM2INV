int main1(int a,int n){
  int m, v, w, x;

  m=(a%11)+14;
  v=m+4;
  w=-2;
  x=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == (a % 11) + 14 &&
                   a == \at(a, Pre) &&
                   n == \at(n, Pre) &&
                   ((v - m) % 2 == 0) &&
                   (0 <= (v - m)) &&
                   ((v - m) <= 4) &&
                   (w <= -2);
  loop invariant v >= m;
  loop invariant m == (a % 11) + 14;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (v - (m + 4)) % 2 == 0;
  loop invariant v <= m + 4;
  loop invariant w <= -2;
  loop invariant w % 2 == 0;
  loop invariant m == ((\at(a, Pre) % 11) + 14);
  loop invariant (v - m) % 2 == 0;
  loop invariant v % 2 == m % 2;
  loop assigns w, v;
*/
while (v>=m+1) {
      w = w*4;
      v = v-2;
  }

}
