int main1(int b,int q){
  int m, v, h, f;

  m=37;
  v=0;
  h=q;
  f=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2 * h == f + 2 * \at(q, Pre);
  loop invariant v >= 0;
  loop invariant m == 37;
  loop invariant q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant f == 2*h - 2*\at(q, Pre);
  loop invariant 2*h == f + 2*\at(q, Pre);
  loop invariant h*2 == f + 2 * \at(q, Pre) && v >= 0;
  loop invariant q == \at(q, Pre) && b == \at(b, Pre) && m == 37;
  loop invariant f + 2 * \at(q, Pre) == 2 * h;
  loop invariant q == \at(q, Pre) && b == \at(b, Pre);
  loop invariant f == 2*h - 2*\at(q, Pre) && v >= 0 && m == 37;
  loop assigns h, f, v;
*/
while (1) {
      h = h*2;
      f = f+h;
      v = v+1;
  }

}
