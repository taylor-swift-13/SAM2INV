int main1(int a,int b,int k,int p){
  int q, v, g, t, x, e, w, f;

  q=58;
  v=0;
  g=b;
  t=v;
  x=b;
  e=k;
  w=4;
  f=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v <= q;
  loop invariant v >= 0;
  loop invariant q == 58;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= v;
  loop invariant (g - b - 2*v) % 3 == 0;
  loop invariant (v == 0) ==> (g == \at(b, Pre));
  loop invariant (v > 0) ==> (g % 2 == 0);
  loop invariant (v >= 0);
  loop invariant (v <= q);
  loop invariant (v == 0) ==> (g == b);

  loop assigns g, v;
*/
while (v<=q-1) {
      g = g*4+2;
      v = v+1;
  }

}
