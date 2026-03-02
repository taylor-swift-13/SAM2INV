int main1(int a,int k){
  int y, u, v;

  y=a;
  u=0;
  v=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 0;
  loop invariant u % 4 == 0;
  loop invariant y == \at(a, Pre);

  loop invariant v >= 0;
  loop invariant v >= u;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant u == 0 && (u % 4) == 0;

  loop invariant y == a;
  loop invariant (u % 4) == 0;
  loop invariant y == a && a == \at(a, Pre);
  loop invariant u == 0 && y == \at(a, Pre) && k == \at(k, Pre);

  loop invariant u == 0 && y == a && a == \at(a, Pre) && k == \at(k, Pre);

  loop assigns v;
*/
while (1) {
      v = v+3;
      if ((u%4)==0) {
          v = v*v+v;
      }
  }

}
