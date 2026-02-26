int main1(int p,int q){
  int f, b, u;

  f=p;
  b=1;
  u=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == \at(p, Pre);
  loop invariant b > 0;

  loop invariant q == \at(q, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant u >= -6;
  loop invariant f == p;
  loop invariant b == 1 || (b % 3 == 0);
  loop invariant u <= u*u;
  loop assigns u, b;
*/
while (b*3<=f) {
      if ((b%7)==0) {
          u = u*u;
      }
      else {
          u = u*u;
      }
      b = b*3;
  }

}
