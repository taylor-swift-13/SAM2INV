int main1(int f){
  int u97, k3l, hz20, q;
  u97=f+14;
  k3l=0;
  hz20=1;
  q=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k3l >= 0;
  loop invariant q == 2*k3l + 1;
  loop invariant hz20 == (k3l + 1) * (k3l + 1);
  loop invariant f == \at(f,Pre) + k3l * k3l + 2 * k3l;
  loop invariant u97 == \at(f, Pre) + 14;
  loop assigns k3l, q, hz20, f;
*/
while (1) {
      if (!(hz20<=u97)) {
          break;
      }
      k3l += 1;
      q += 2;
      hz20 = hz20 + q;
      f = f + q;
  }
}