int main1(int b,int n,int p){
  int h, c, v, o, t;

  h=76;
  c=0;
  v=-48;
  o=h;
  t=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v >= -48;
  loop invariant o >= 76;
  loop invariant v <= o;
  loop invariant t >= \at(b, Pre);
  loop invariant t >= b;
  loop invariant (t - b) % 5 == 0;
  loop invariant v % 2 == 0;
  loop invariant o % 2 == 0;
  loop invariant h == 76;
  loop assigns v, o, t;
*/
while (v<=-2) {
      v = v+o+2;
      o = o+1;
      v = v+1;
      o = o+v;
      t = t+5;
      v = v+3;
  }

}
