int main1(int b,int p){
  int x, u, v, h, n, z;

  x=70;
  u=0;
  v=u;
  h=b;
  n=1;
  z=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == b + v*(v+1)/2;
  loop invariant v >= 0;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant x == 70;
  loop invariant h == \at(b,Pre) + (v*(v + 1))/2;
  loop assigns v, h;
*/
while (1) {
      v = v+1;
      h = h+v;
  }

}
