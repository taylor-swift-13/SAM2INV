int main1(int p,int q){
  int r, t, e, v;

  r=(q%6)+8;
  t=1;
  e=-8;
  v=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant e >= -8;
  loop invariant r == (q % 6) + 8;
  loop invariant (e == -8) || (e - v == 3);
  loop invariant r == (\at(q, Pre) % 6) + 8;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant (e - v == 3) || (e == -8 && v == r);
  loop invariant e == -8 || e - v == 3;
  loop invariant v >= -8;
  loop invariant (e + 8) % 3 == 0;

  loop invariant (p == \at(p, Pre));
  loop invariant (q == \at(q, Pre));
  loop invariant (e >= -8);
  loop invariant ((e + 8) % 3 == 0);
  loop invariant ( (e == -8 && v == r) || (e - v == 3) );
  loop invariant p == \at(p,Pre);
  loop invariant q == \at(q,Pre);
  loop assigns v, e;
*/
while (1) {
      v = e;
      e = e+2;
      e = e+1;
  }

}
