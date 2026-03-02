int main1(int k,int m){
  int h, t, v, j;

  h=8;
  t=2;
  v=-18154;
  j=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4*v - j*j - 2*j == -72624;
  loop invariant j >= 2;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant j*j + 2*j - 4*v == 72624;
  loop invariant j % 2 == 0;
  loop invariant h == 8;

  loop invariant 4*v == (j-2)*(j+4) - 72616;
  loop invariant 4*(v+18154) == j*j + 2*j - 8;
  loop invariant v >= -18154;
  loop invariant 4*v == j*j + 2*j - 72624;
  loop invariant (v <= -3) ==> (j <= 268);
  loop invariant (j >= 2) && (j % 2 == 0);
  loop invariant 4*(v + 18154) == (j - 2)*(j - 2) + 6*(j - 2);
  loop assigns v, j;
*/
while (v<=-3) {
      v = v+j+2;
      j = j+2;
  }

}
