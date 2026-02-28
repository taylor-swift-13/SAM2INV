int main1(int k,int m){
  int b, u, e, z;

  b=k+24;
  u=0;
  e=k;
  z=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == k + 2*u;

  loop invariant b == k + 24;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= u;
  loop invariant u >= 0;
  loop invariant e - 2*u == k;
  loop assigns e, u;
*/
while (1) {
      if (u>=b) {
          break;
      }
      e = e+2;
      u = u+1;
  }

}
