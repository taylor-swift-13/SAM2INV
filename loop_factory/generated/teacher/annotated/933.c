int main1(int b,int k){
  int m, u, v, a;

  m=(k%34)+12;
  u=m+3;
  v=0;
  a=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= v;

  loop invariant (v <= m/2) ==> (a == 2*v);

  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);

  loop invariant a % 2 == 0;
  loop invariant (v < m/2) ==> (a == 2*v);

  loop invariant b == \at(b, Pre) && k == \at(k, Pre);
  loop invariant m == (\at(k, Pre) % 34) + 12;

  loop invariant (-2*v) <= a && a <= 2*v;
  loop invariant (a % 2) == 0;
  loop invariant v <= m && (v <= m/2) ==> (a == 2*v) && (v > m/2) ==> (a == 2*(m/2)) && a <= m;


  loop assigns a, v;
*/
while (v<m) {
      if (v<m/2) {
          a = a+2;
      }
      else {
          a = a-2;
      }
      v = v+1;
  }

}
