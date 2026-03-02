int main1(int a,int b){
  int s, h, q, u;

  s=a;
  h=s;
  q=5;
  u=s;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant s == \at(a, Pre);
  loop invariant u == 5*\at(a, Pre) - 4*h;
  loop invariant q == 5 + 3*(\at(a, Pre) - h);

  loop invariant u == \at(a, Pre) + 4*(\at(a, Pre) - h);
  loop invariant h <= \at(a, Pre);
  loop invariant s == \at(a, Pre) && h <= \at(a, Pre);
  loop invariant q + 3*h == 5 + 3*\at(a, Pre) && u + 4*h == 5*\at(a, Pre);
  loop invariant q + 3*h == 5 + 3*\at(a, Pre) && u + 4*h == 5*\at(a, Pre) && s == \at(a, Pre);
  loop invariant h <= \at(a, Pre) && q >= 5;
  loop invariant u + 4*h == 5 * \at(a, Pre) && q + 3*h == 5 + 3 * \at(a, Pre);
  loop invariant h <= \at(a, Pre) && s == a && a == \at(a, Pre);
  loop invariant u + 4*h == 5*\at(a, Pre);
  loop invariant q == 5 + 3*(\at(a,Pre) - h) && u == \at(a,Pre) + 4*(\at(a,Pre) - h);
  loop invariant s == \at(a,Pre) && b == \at(b,Pre) && h <= \at(a,Pre) && \at(a,Pre) - h >= 0;
  loop invariant q + 3*h == 5 + 3*\at(a, Pre);
  loop invariant u + 4*h == 5 * \at(a, Pre);

  loop invariant q == 5 + 3*(\at(a, Pre) - h) && u == \at(a, Pre) + 4*(\at(a, Pre) - h);
  loop invariant q + 3*h == 5 + 3 * \at(a, Pre);
  loop assigns q, u, h;
*/
while (h>0) {
      q = q+3;
      u = u+4;
      h = h-1;
  }

}
