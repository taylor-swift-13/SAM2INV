int main1(int a,int q){
  int c1nx, mk, o, d9;
  c1nx=a+14;
  mk=c1nx;
  o=12;
  d9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o + d9 == 12;
  loop invariant 0 <= o;
  loop invariant 0 <= d9;
  loop invariant mk <= c1nx;
  loop invariant a >= \at(a, Pre);
  loop invariant q * \at(q, Pre) >= 0;
  loop invariant c1nx == \at(a, Pre) + 14;
  loop invariant \at(a, Pre) + 14 <= mk;
  loop assigns a, q, mk, o, d9;
*/
while (mk<c1nx) {
      if (mk%2==0) {
          if (o>0) {
              o--;
              d9++;
          }
      }
      else {
          if (d9>0) {
              d9 -= 1;
              o = o + 1;
          }
      }
      mk = mk + 1;
      a = a + d9;
      q = q + q;
  }
}