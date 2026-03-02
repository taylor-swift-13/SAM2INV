int main1(int a,int q){
  int c, u, b;

  c=a;
  u=0;
  b=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(a, Pre);
  loop invariant b == 4 + 2*u + (u*(u-1))/2;
  loop invariant u >= 0;
  loop invariant c < 0 || u <= c;
  loop invariant (u <= c) || (c < 0);
  loop invariant b == 4 + 2*u + u*(u-1)/2;
  loop invariant u >= 0 && (u <= c || c < 0);
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant b == 4 + 2*u + (u*(u-1))/2 && u >= 0;

  loop invariant a == \at(a, Pre) && q == \at(q, Pre) && c == \at(a, Pre);

  loop assigns b, u;
*/
while (u<=c-1) {
      b = b+2;
      b = b+u;
      u = u+1;
  }

}
