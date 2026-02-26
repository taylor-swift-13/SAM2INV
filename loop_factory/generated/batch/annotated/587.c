int main1(int k,int p){
  int n, v, h, e;

  n=k;
  v=0;
  h=-8;
  e=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v == 0;
  loop invariant e >= p;
  loop invariant (e - p) % 5 == 0;
  loop invariant h - e == -8 - p;
  loop invariant (e - h) == (p + 8);
  loop invariant h >= -8;
  loop invariant n == k;
  loop invariant h - e == -(p + 8);
  loop invariant 5*(h + 8) == (e - p) * (5 + v);
  loop assigns h, e;
*/
while (1) {
      h = h+5;
      e = e+5;
      h = h+v;
  }

}
