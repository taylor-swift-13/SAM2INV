int main1(int a,int m){
  int c, t, v;

  c=43;
  t=0;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 0;
  loop invariant c == 43;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (v - a) % 5 == 0;
  loop invariant v >= a;
  loop invariant ((v - a) % 5) == 0;
  loop invariant v >= \at(a, Pre);
  loop invariant (v - \at(a, Pre)) % 5 == 0;
  loop assigns v;
*/
while (1) {
      v = v+3;
      if ((t%2)==0) {
          v = v+2;
      }
  }

}
