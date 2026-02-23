int main1(int a,int p){
  int i, u, z, v, y, b;

  i=41;
  u=0;
  z=1;
  v=u;
  y=i;
  b=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 41;
  loop invariant z == 1;
  loop invariant v == 0;
  loop invariant y == i;

  loop invariant (0 <= u) && (u <= i);
  loop invariant 0 <= u && u <= i;
  loop invariant z == 1 && v == 0 && y == 41 && u <= i && ((u == 0) ==> (b == a));
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (u > 0) ==> (b == z + v + y);
  loop invariant u <= i;
  loop invariant (u != 0) ==> (b == z + v + y);
  loop assigns b, u;
*/
while (u<i) {
      b = z+v+y;
      u = u+1;
  }

}
