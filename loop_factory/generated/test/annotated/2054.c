int main1(int z){
  int v, x, n, ah5s, ao;
  v=53;
  x=0;
  n=z;
  ah5s=-8;
  ao=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= x);
  loop invariant (x <= v);
  loop invariant v == 53;
  loop invariant (ao == -5 + (x*(x+1))/2);
  loop invariant ((x <= v/2) ==> (n == \at(z, Pre)));
  loop invariant (x <= (v/2)) ==> (ah5s == -8 + x * \at(z, Pre));
  loop invariant \at(z, Pre) <= n;
  loop invariant n <= \at(z, Pre) + 2 * x;
  loop invariant ah5s >= -8 + x * \at(z, Pre);
  loop assigns n, ah5s, x, ao;
*/
while (x<=v-1) {
      if (!(!(x>=v/2))) {
          n += 2;
      }
      ah5s += n;
      x = x + 1;
      ao += x;
  }
}