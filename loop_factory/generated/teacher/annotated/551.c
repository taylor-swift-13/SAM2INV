int main1(int m,int q){
  int n, g, v, f;

  n=(q%39)+8;
  g=1;
  v=q;
  f=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == q + 5*(g - 1);

  loop invariant n == (q % 39) + 8;
  loop invariant m == \at(m, Pre);
  loop invariant g >= 1;
  loop invariant f == 6 + (g - 1) * q + 5 * ((g - 1) * g) / 2;
  loop invariant q == \at(q, Pre);
  loop invariant f == 6 + q*(g - 1) + (5*(g - 1)*g)/2;
  loop invariant f == 6 + (g - 1)*q + 5*(g - 1)*g/2;
  loop invariant n == (\at(q, Pre) % 39) + 8;
  loop invariant v == \at(q, Pre) + 5*(g - 1);
  loop assigns v, f, g;
*/
while (1) {
      v = v+5;
      f = f+v;
      g = g+1;
  }

}
