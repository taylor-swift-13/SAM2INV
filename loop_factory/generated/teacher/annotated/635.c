int main1(int b,int q){
  int g, k, i, e, u, v;

  g=53;
  k=0;
  i=g;
  e=-2;
  u=3;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == -2 + 3*k + i * k * (k - 1) / 2;
  loop invariant u == i * k + 3;
  loop invariant v == i * k - 5;
  loop invariant k >= 0;
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant i == 53 &&
                   k >= 0 &&
                   u == 3 + 53*k &&
                   v == -5 + 53*k &&
                   e == -2 + 3*k + 53*k*(k-1)/2 &&
                   b == \at(b, Pre) &&
                   q == \at(q, Pre);
  loop invariant e == -2 + 3*k + i*(k*(k-1))/2;
  loop invariant u - i*k == 3;
  loop invariant i == 53;
  loop invariant u == 3 + i * k;
  loop invariant v == -5 + i * k;
  loop invariant e == -2 + 3 * k + (i * k * (k - 1)) / 2;
  loop invariant i == g;
  loop invariant u == 3 + k*i;
  loop invariant v == -5 + k*i;
  loop assigns e, u, v, k;
*/
while (1) {
      e = e+u;
      u = u+i;
      v = v+i;
      k = k+1;
  }

}
