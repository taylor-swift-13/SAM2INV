int main1(int b,int k){
  int i, u, f;

  i=b;
  u=0;
  f=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant 2*f >= 7*u;
  loop invariant f >= 0;
  loop invariant i == b;
  loop invariant u % 2 == 0;
  loop invariant u >= 0;
  loop invariant f >= u;
  loop invariant i == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant f >= 7*(u/2);
  loop invariant \at(b, Pre) < 2 ==> f == 7*(u/2);
  loop invariant 0 <= u;
  loop invariant b == \at(b, Pre);
  loop invariant (i < 2) ==> (2*f == 7*u);
  loop assigns f, u;
*/
while (u<=i-2) {
      if (u+2<=u+i) {
          f = f+f;
      }
      f = f+2;
      f = f+5;
      u = u+2;
  }

}
