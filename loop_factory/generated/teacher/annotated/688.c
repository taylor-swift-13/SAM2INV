int main1(int k,int m,int p,int q){
  int e, c, v, o, y, d, w;

  e=71;
  c=3;
  v=1;
  o=m;
  y=3;
  d=p;
  w=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (v == 1) || (v % 4 == 0);
  loop invariant (v == 1) ==> (o == m);
  loop invariant v >= 1;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant e == 71;
  loop assigns o, v;
*/
while (1) {
      o = v;
      v = v+3;
      v = v*4;
      o = o/4;
  }

}
