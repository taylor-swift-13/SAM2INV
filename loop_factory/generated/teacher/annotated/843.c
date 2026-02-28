int main1(int a,int b,int k){
  int x, i, v, o, z, u;

  x=29;
  i=x+4;
  v=0;
  o=1;
  z=1;
  u=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 1;
  loop invariant v >= 0;
  loop invariant o >= 1;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v % 2 == 0;
  loop invariant x == 29;

  loop invariant v % 3 == 0;
  loop invariant o % 3 == 1;
  loop invariant o >= v + 1;

  loop invariant z >= 0;
  loop assigns v, o, z;
*/
while (v<x) {
      v = v+3;
      o = o+3;
      z = z+3;
      v = v*2;
      o = o+v;
      z = z%3;
  }

}
