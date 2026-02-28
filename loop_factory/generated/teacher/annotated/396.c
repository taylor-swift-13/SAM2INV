int main1(int a,int b){
  int g, k, t, v;

  g=b;
  k=0;
  t=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == b;
  loop invariant 0 <= t;

  loop invariant t >= 0;
  loop invariant (t <= g) || (t == 0);
  loop invariant g == \at(b, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop assigns t;
*/
while (t<g) {
      if (t<g) {
          t = t+1;
      }
  }

}
