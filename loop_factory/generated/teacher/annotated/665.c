int main1(int a,int p){
  int q, e, v, x, o, u;

  q=31;
  e=2;
  v=q;
  x=-3;
  o=8;
  u=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v >= 0;
  loop invariant u >= -3;
  loop invariant x >= -3;
  loop invariant q == 31;
  loop invariant v <= 31;
  loop invariant (v == 31 && x == -3) || (x == v*v);
  loop invariant a == \at(a, Pre) && p == \at(p, Pre) && ((v == 31) || (0 <= v && v <= 2)) && ((x == -3) || (x == 0) || (x == 1) || (x == 4));
  loop invariant ((u == -3) || (u >= 0));
  loop assigns v, x, u;
*/
while (1) {
      v = v+1;
      x = x+v;
      u = u*u+v;
      v = v%3;
      x = v*v;
  }

}
