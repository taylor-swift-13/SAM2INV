int main1(int m,int n){
  int a, g, v;

  a=n;
  g=0;
  v=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == n && m == \at(m, Pre) && n == \at(n, Pre);

  loop invariant a == \at(n,Pre) && n == \at(n,Pre) && m == \at(m,Pre);
  loop invariant g >= 0 && v >= 5 && v >= g;
  loop invariant a == n;

  loop invariant g >= 0;
  loop invariant (v - g) % 2 == 1;
  loop invariant v >= 5;
  loop invariant a == \at(n, Pre);

  loop invariant (v % 2) == 1 - (g % 2);
  loop invariant n == \at(n, Pre);
  loop invariant m == \at(m, Pre);
  loop assigns v, g;
*/
while (g<a) {
      v = v+v;
      v = v+g;
      g = g+1;
  }

}
