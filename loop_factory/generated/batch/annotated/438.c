int main1(int b,int q){
  int n, h, v;

  n=(q%39)+15;
  h=2;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == (q % 39) + 15;
  loop invariant 2*v == 2*q + h*h + h - 6;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant h >= 2;
  loop invariant v == \at(q, Pre) + (h*h + h - 6)/2;
  loop invariant n == \at(q, Pre) % 39 + 15;
  loop invariant v == q + ((h*h) + h - 6) / 2;
  loop invariant n == (\at(q,Pre) % 39) + 15;
  loop invariant v >= q;
  loop invariant 2*(v - \at(q, Pre)) == (h - 2) * (h + 3);
  loop invariant v == q + (h*h + h - 6)/2;
  loop assigns v, h;
*/
while (1) {
      v = v+h;
      v = v+1;
      h = h+1;
  }

}
