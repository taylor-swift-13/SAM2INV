int main1(int b,int p){
  int x, u, v;

  x=52;
  u=0;
  v=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 52;
  loop invariant v >= -4;
  loop invariant u <= x - 1;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u == 0;
  loop invariant -4 <= v;
  loop invariant v <= (v + 4) * (v + 4);

  loop invariant (v == -4) || (v >= 0);
  loop invariant u <= x;
  loop assigns v;
*/
while (u+1<=x) {
      v = v+4;
      v = v*v;
  }

}
