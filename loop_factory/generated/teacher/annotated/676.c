int main1(int a,int m,int n,int p){
  int c, w, o, v, i;

  c=75;
  w=0;
  o=n;
  v=p;
  i=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant n <= o;
  loop invariant i == a;
  loop invariant v == p || v == a;
  loop invariant v <= p;
  loop invariant c == 75;
  loop invariant i == \at(a,Pre);
  loop invariant o >= \at(n,Pre);
  loop invariant v <= \at(p,Pre);
  loop invariant (v == \at(p,Pre)) || (v == i);
  loop invariant o >= n;
  loop invariant (v == p) || (v == i);
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant v == \at(p,Pre) || v == a;
  loop assigns o, v;
*/
while (1) {
      if (o>=c) {
          break;
      }
      if (i<=v) {
          v = i;
      }
      o = o+1;
  }

}
