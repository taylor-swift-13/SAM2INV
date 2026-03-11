int main1(int a,int q){
  int b, c, t, v;

  b=a;
  c=b;
  t=q;
  v=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant b == a;
  loop invariant c == b;
  loop invariant v == -6;
  loop invariant b == \at(a, Pre);
  loop invariant c == \at(a, Pre);
  loop invariant (c < b/2) ==> (t <= \at(q, Pre) && (t - \at(q, Pre)) % 3 == 0);
  loop invariant (c >= b/2) ==> (t >= \at(q, Pre) && (t - \at(q, Pre)) % 4 == 0);
  loop invariant (c < b/2) ==> ((q - t) % 3 == 0);
  loop invariant (c >= b/2) ==> ((t - q) % 4 == 0);
  loop invariant c == a;
  loop invariant (\at(a, Pre) < \at(a, Pre)/2) ==> ((t - \at(q, Pre)) % 3 == 0);
  loop invariant (\at(a, Pre) >= \at(a, Pre)/2) ==> ((t - \at(q, Pre)) % 4 == 0);
  loop invariant (c < b/2) ==> t <= q;
  loop invariant (c >= b/2) ==> t >= q;
  loop assigns t;
*/
while (c>=1) {
      if (c<b/2) {
          t = t+v;
      }
      else {
          t = t+1;
      }
      t = t+3;
  }

}
